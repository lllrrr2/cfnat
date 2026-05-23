package main

import (
	"bufio"
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

const (
	timeout     = 1 * time.Second // 超时时间
	maxDuration = 2 * time.Second // 最大持续时间

	baiduFakeHost  = "sptest.baidu.com"
	baiduUserAgent = "okhttp/3.11.0 Dalvik/2.1.0 (Linux; Build/RKQ1.200826.002) baiduboxapp/11.0.5.12 (Baidu; P1 11)"
	baiduAuthToken = "482857715"

	carrierMobile  = "mobile"
	carrierTelecom = "telecom"
	carrierUnicom  = "unicom"
)

var (
	activeConnections  int32 // 用于跟踪活跃连接的数量
	validIPClientCache sync.Map
	randomMu           sync.Mutex
	randomGenerator    = rand.New(rand.NewSource(time.Now().UnixNano()))
)

var carrierDisplayNames = map[string]string{
	carrierMobile:  "中国移动",
	carrierTelecom: "中国电信",
	carrierUnicom:  "中国联通",
}

var defaultCarrierResolvers = map[string][]string{
	carrierMobile:  {"221.131.143.69:53", "112.4.0.55:53", "211.138.180.2:53"},
	carrierTelecom: {"202.96.209.133:53", "202.96.128.86:53", "202.103.24.68:53"},
	carrierUnicom:  {"202.106.0.20:53", "210.21.196.6:53", "221.5.88.88:53"},
}

var defaultBaiduResolvers = []string{
	"223.5.5.5:53",
	"223.6.6.6:53",
	"119.29.29.29:53",
	"180.76.76.76:53",
	"114.114.114.114:53",
	"1.1.1.1:53",
	"8.8.8.8:53",
}

// IPManager 用于安全管理 IP 地址状态
type IPManager struct {
	mu            sync.RWMutex
	currentIP     string
	ipAddresses   []string
	currentIndex  int
	allIPsChecked bool
}

func NewIPManager() *IPManager {
	return &IPManager{}
}

func (m *IPManager) SetIPAddresses(ips []string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = ips
	m.currentIndex = 0
	m.allIPsChecked = false
}

func (m *IPManager) GetCurrentIP() string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.currentIP
}

func (m *IPManager) SetCurrentIP(ip string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.currentIP = ip
}

func (m *IPManager) GetIPAddresses() []string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.ipAddresses
}

func (m *IPManager) IsAllIPsChecked() bool {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.allIPsChecked
}

func (m *IPManager) Clear() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = []string{}
	m.currentIP = ""
	m.currentIndex = 0
	m.allIPsChecked = false
}

func (m *IPManager) switchToNextValidIP(useTLS bool, port int, domain string, code int, proxyPool *BaiduProxyPool) bool {
	m.mu.Lock()
	defer m.mu.Unlock()

	// 尝试从当前索引的下一个 IP 开始检查
	for i := m.currentIndex + 1; i < len(m.ipAddresses); i++ {
		ip := m.ipAddresses[i]

		// 跳过当前 IP
		if ip == m.currentIP {
			continue
		}

		if checkValidIP(ip, port, useTLS, domain, code, proxyPool) {
			m.currentIP = ip
			m.currentIndex = i
			m.allIPsChecked = false
			log.Printf("切换到新的有效 IP: %s 更新 IP 索引: %d", m.currentIP, m.currentIndex)
			return true
		}
	}

	m.allIPsChecked = true
	log.Println("所有 IP 都已检查过，程序将退出")
	return false
}

type result struct {
	ip          string        // IP地址
	dataCenter  string        // 数据中心
	region      string        // 地区
	city        string        // 城市
	latency     string        // 延迟
	tcpDuration time.Duration // TCP请求延迟
}

type location struct {
	Iata   string  `json:"iata"`
	Lat    float64 `json:"lat"`
	Lon    float64 `json:"lon"`
	Cca2   string  `json:"cca2"`
	Region string  `json:"region"`
	City   string  `json:"city"`
}

type carrierListenSpec struct {
	carrier string
	addr    string
}

type proxyEndpoint struct {
	addr      string
	active    int32
	ewmaNanos int64
	failures  int32
}

type BaiduProxyPool struct {
	name      string
	endpoints []*proxyEndpoint
}

func NewBaiduProxyPool(name string, addrs []string) *BaiduProxyPool {
	pool := &BaiduProxyPool{name: name}
	for _, addr := range dedupeStrings(addrs) {
		pool.endpoints = append(pool.endpoints, &proxyEndpoint{
			addr:      addr,
			ewmaNanos: int64(timeout),
		})
	}
	return pool
}

func (p *BaiduProxyPool) CacheKey() string {
	if p == nil {
		return "direct"
	}

	addrs := make([]string, 0, len(p.endpoints))
	for _, endpoint := range p.endpoints {
		addrs = append(addrs, endpoint.addr)
	}
	sort.Strings(addrs)
	return p.name + "|" + strings.Join(addrs, ",")
}

func (p *BaiduProxyPool) Len() int {
	if p == nil {
		return 0
	}
	return len(p.endpoints)
}

func (p *BaiduProxyPool) Addresses() []string {
	if p == nil {
		return nil
	}
	addrs := make([]string, 0, len(p.endpoints))
	for _, endpoint := range p.endpoints {
		addrs = append(addrs, endpoint.addr)
	}
	return addrs
}

func (p *BaiduProxyPool) pick() *proxyEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}
	if len(p.endpoints) == 1 {
		return p.endpoints[0]
	}

	a := p.endpoints[nextRandomIntn(len(p.endpoints))]
	b := p.endpoints[nextRandomIntn(len(p.endpoints))]
	for b == a && len(p.endpoints) > 1 {
		b = p.endpoints[nextRandomIntn(len(p.endpoints))]
	}

	if b.scoreNanos() < a.scoreNanos() {
		return b
	}
	return a
}

func (p *BaiduProxyPool) Dial(ctx context.Context, targetAddr string, dialTimeout time.Duration) (net.Conn, error) {
	if p == nil || len(p.endpoints) == 0 {
		return nil, errors.New("百度代理池为空")
	}

	attempts := len(p.endpoints)
	if attempts > 3 {
		attempts = 3
	}

	var lastErr error
	for i := 0; i < attempts; i++ {
		endpoint := p.pick()
		if endpoint == nil {
			return nil, errors.New("百度代理池没有可用节点")
		}

		atomic.AddInt32(&endpoint.active, 1)
		start := time.Now()
		conn, err := dialBaiduTunnelViaNode(ctx, endpoint.addr, targetAddr, dialTimeout)
		elapsed := time.Since(start)
		if err != nil {
			atomic.AddInt32(&endpoint.active, -1)
			endpoint.recordFailure(elapsed)
			lastErr = fmt.Errorf("%s: %w", endpoint.addr, err)
			continue
		}

		endpoint.recordSuccess(elapsed)
		return &trackedProxyConn{Conn: conn, endpoint: endpoint}, nil
	}

	return nil, lastErr
}

func (e *proxyEndpoint) scoreNanos() int64 {
	ewma := atomic.LoadInt64(&e.ewmaNanos)
	if ewma <= 0 {
		ewma = int64(timeout)
	}
	active := int64(atomic.LoadInt32(&e.active))
	failures := int64(atomic.LoadInt32(&e.failures))
	return ewma + active*int64(50*time.Millisecond) + failures*int64(300*time.Millisecond)
}

func (e *proxyEndpoint) recordSuccess(elapsed time.Duration) {
	updateEWMA(&e.ewmaNanos, elapsed)
	if atomic.LoadInt32(&e.failures) > 0 {
		atomic.AddInt32(&e.failures, -1)
	}
}

func (e *proxyEndpoint) recordFailure(elapsed time.Duration) {
	if elapsed > 0 {
		updateEWMA(&e.ewmaNanos, elapsed)
	}
	atomic.AddInt32(&e.failures, 1)
}

type trackedProxyConn struct {
	net.Conn
	endpoint *proxyEndpoint
	once     sync.Once
}

func (c *trackedProxyConn) Close() error {
	err := c.Conn.Close()
	c.once.Do(func() {
		atomic.AddInt32(&c.endpoint.active, -1)
	})
	return err
}

type targetEndpoint struct {
	ip        string
	addr      string
	active    int32
	ewmaNanos int64
	failures  int32
}

type TargetPool struct {
	name      string
	endpoints []*targetEndpoint
}

func NewTargetPool(name string, results []result, port int) *TargetPool {
	pool := &TargetPool{name: name}
	for _, r := range results {
		pool.endpoints = append(pool.endpoints, &targetEndpoint{
			ip:        r.ip,
			addr:      net.JoinHostPort(r.ip, strconv.Itoa(port)),
			ewmaNanos: int64(r.tcpDuration),
		})
	}
	return pool
}

func (p *TargetPool) Len() int {
	if p == nil {
		return 0
	}
	return len(p.endpoints)
}

func (p *TargetPool) pick() *targetEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}
	if len(p.endpoints) == 1 {
		return p.endpoints[0]
	}

	a := p.endpoints[nextRandomIntn(len(p.endpoints))]
	b := p.endpoints[nextRandomIntn(len(p.endpoints))]
	for b == a && len(p.endpoints) > 1 {
		b = p.endpoints[nextRandomIntn(len(p.endpoints))]
	}

	if b.scoreNanos() < a.scoreNanos() {
		return b
	}
	return a
}

func (p *TargetPool) PickTargets(maxAttempts int) []*targetEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}
	if maxAttempts <= 0 || maxAttempts > len(p.endpoints) {
		maxAttempts = len(p.endpoints)
	}

	targets := make([]*targetEndpoint, 0, maxAttempts)
	seen := make(map[*targetEndpoint]struct{}, maxAttempts)
	for len(targets) < maxAttempts {
		target := p.pick()
		if target == nil {
			break
		}
		if _, ok := seen[target]; ok {
			if len(seen) == len(p.endpoints) {
				break
			}
			continue
		}
		seen[target] = struct{}{}
		targets = append(targets, target)
	}
	return targets
}

func (e *targetEndpoint) scoreNanos() int64 {
	ewma := atomic.LoadInt64(&e.ewmaNanos)
	if ewma <= 0 {
		ewma = int64(timeout)
	}
	active := int64(atomic.LoadInt32(&e.active))
	failures := int64(atomic.LoadInt32(&e.failures))
	return ewma + active*int64(50*time.Millisecond) + failures*int64(300*time.Millisecond)
}

func (e *targetEndpoint) recordSuccess(elapsed time.Duration) {
	updateEWMA(&e.ewmaNanos, elapsed)
	if atomic.LoadInt32(&e.failures) > 0 {
		atomic.AddInt32(&e.failures, -1)
	}
}

func (e *targetEndpoint) recordFailure(elapsed time.Duration) {
	if elapsed > 0 {
		updateEWMA(&e.ewmaNanos, elapsed)
	}
	atomic.AddInt32(&e.failures, 1)
}

func updateEWMA(dst *int64, sample time.Duration) {
	if sample <= 0 {
		return
	}
	sampleNanos := int64(sample)
	for {
		old := atomic.LoadInt64(dst)
		next := sampleNanos
		if old > 0 {
			next = (old*7 + sampleNanos) / 8
		}
		if atomic.CompareAndSwapInt64(dst, old, next) {
			return
		}
	}
}

func main() {
	localAddr := flag.String("addr", "0.0.0.0:1234", "本地监听的 IP 和端口")
	code := flag.Int("code", 200, "HTTP/HTTPS 响应状态码")
	coloFilter := flag.String("colo", "", "筛选数据中心例如 HKG,SJC,LAX (多个数据中心用逗号隔开,留空则忽略匹配)")
	Delay := flag.Int("delay", 300, "有效延迟（毫秒），超过此延迟将断开连接")
	domain := flag.String("domain", "cloudflaremirrors.com/debian", "响应状态码检查的域名地址")
	ipCount := flag.Int("ipnum", 20, "提取的有效IP数量")
	ipsType := flag.String("ips", "4", "指定生成IPv4还是IPv6地址 (4或6)")
	num := flag.Int("num", 5, "目标负载 IP 数量")
	port := flag.Int("port", 443, "转发的目标端口")
	random := flag.Bool("random", true, "是否随机生成IP，如果为false，则从CIDR中拆分出所有IP")
	maxThreads := flag.Int("task", 100, "并发请求最大协程数")
	useTLS := flag.Bool("tls", true, "是否为 TLS 端口")
	useBaiduProxy := flag.Bool("baidu-proxy", true, "是否启用固定百度前置代理")
	baiduDomain := flag.String("baidu-domain", "cloudnproxy.baidu.com", "百度前置代理域名")
	baiduPort := flag.Int("baidu-port", 443, "百度前置代理端口")
	baiduScanTarget := flag.String("baidu-scan-target", "myip.ipip.net:80", "扫描百度代理IP池时用于 CONNECT 的目标")
	baiduIPCount := flag.Int("baidu-ipnum", 12, "每个运营商保留的百度代理IP数量")
	carrierListens := flag.String("carrier-listens", "", "按运营商启动多个监听端口，例如 mobile=0.0.0.0:1234,telecom=0.0.0.0:1235,unicom=0.0.0.0:1236")
	carrierResolvers := flag.String("carrier-resolvers", "", "额外用于聚合解析百度代理域名的DNS，例如 mobile=1.1.1.1:53|2.2.2.2:53,telecom=...,unicom=...")

	flag.Parse()

	if *carrierListens != "" {
		specs, err := parseCarrierListens(*carrierListens)
		if err != nil {
			log.Fatalf("解析 -carrier-listens 失败: %v", err)
		}
		resolvers, err := parseCarrierResolvers(*carrierResolvers)
		if err != nil {
			log.Fatalf("解析 -carrier-resolvers 失败: %v", err)
		}
		if err := runCarrierMode(specs, resolvers, *baiduDomain, *baiduPort, *baiduScanTarget, *baiduIPCount, *code, *coloFilter, *Delay, *domain, *ipCount, *ipsType, *num, *port, *random, *maxThreads, *useTLS, *useBaiduProxy); err != nil {
			log.Fatalf("运营商分池模式失败: %v", err)
		}
		return
	}

	// 创建 IP 管理器
	ipManager := NewIPManager()
	var defaultProxyPool *BaiduProxyPool
	if *useBaiduProxy {
		defaultProxyPool = NewBaiduProxyPool("default", []string{ensureHostPort(*baiduDomain, *baiduPort)})
	}

	// 启动 TCP 监听
	listener, err := net.Listen("tcp", *localAddr)
	if err != nil {
		log.Fatalf("无法监听 %s: %v", *localAddr, err)
	}
	defer listener.Close()

	if defaultProxyPool != nil {
		log.Printf("百度前置代理已启用: %s", strings.Join(defaultProxyPool.Addresses(), ","))
	} else {
		log.Printf("百度前置代理已关闭，使用直连拨号")
	}
	log.Printf("正在监听 %s 并转发到 %d 个目标地址，有效延迟：%d ms", *localAddr, *num, *Delay)

	for {
		startTime := time.Now()

		// 使用函数处理 locations.json，确保 defer 正确执行
		locations, err := loadLocations()
		if err != nil {
			log.Printf("加载位置信息失败: %v", err)
			time.Sleep(3 * time.Second)
			continue
		}

		locationMap := make(map[string]location)
		for _, loc := range locations {
			locationMap[loc.Iata] = loc
		}

		var url string
		var filename string

		// 使用 switch 替代 if-else
		switch *ipsType {
		case "6":
			filename = "ips-v6.txt"
			url = "https://www.baipiao.eu.org/cloudflare/ips-v6"
		case "4":
			filename = "ips-v4.txt"
			url = "https://www.baipiao.eu.org/cloudflare/ips-v4"
		default:
			fmt.Println("无效的IP类型。请使用 '4' 或 '6'")
			return
		}

		var content string

		// 检查本地是否有文件
		if _, err = os.Stat(filename); os.IsNotExist(err) {
			fmt.Printf("文件 %s 不存在，正在从 URL %s 下载数据\n", filename, url)
			content, err = getURLContent(url)
			if err != nil {
				fmt.Println("获取URL内容出错:", err)
				return
			}
			err = saveToFile(filename, content)
			if err != nil {
				fmt.Println("保存文件出错:", err)
				return
			}
		} else {
			content, err = getFileContent(filename)
			if err != nil {
				fmt.Println("读取本地文件出错:", err)
				return
			}
		}

		var ipList []string
		if *random {
			ipList = parseIPList(content)
			switch *ipsType {
			case "6":
				ipList = getRandomIPv6s(ipList)
			case "4":
				ipList = getRandomIPv4s(ipList)
			}
		} else {
			ipList, err = readIPs(filename)
			if err != nil {
				fmt.Println("读取IP出错:", err)
				return
			}
		}

		// 从生成的 IP 列表进行处理
		results := scanIPs(ipList, locationMap, *maxThreads, defaultProxyPool)

		if len(results) == 0 {
			fmt.Println("未发现有效IP")
			time.Sleep(3 * time.Second)
			continue
		}

		// 应用数据中心筛选
		if *coloFilter != "" {
			filters := strings.Split(*coloFilter, ",")
			var filteredResults []result
			for _, r := range results {
				for _, filter := range filters {
					if strings.EqualFold(r.dataCenter, filter) {
						filteredResults = append(filteredResults, r)
						break
					}
				}
			}
			results = filteredResults
		}

		// 按 TCP 延迟排序
		sort.Slice(results, func(i, j int) bool {
			return results[i].tcpDuration < results[j].tcpDuration
		})

		// 只显示指定数量的 IP
		if len(results) > *ipCount {
			results = results[:*ipCount]
		}

		fmt.Println("IP 地址 | 数据中心 | 地区 | 城市 | 延迟")
		for _, r := range results {
			fmt.Printf("%s | %s | %s | %s | %s\n", r.ip, r.dataCenter, r.region, r.city, r.latency)
		}

		fmt.Printf("成功提取 %d 个有效IP，耗时 %d秒\n", len(results), time.Since(startTime)/time.Second)

		// 设置 IP 地址列表
		var ips []string
		for _, r := range results {
			ips = append(ips, r.ip)
		}
		ipManager.SetIPAddresses(ips)

		// 选择一个有效 IP
		currentIP := selectValidIP(ipManager, *useTLS, *port, *domain, *code, defaultProxyPool)
		if currentIP == "" {
			log.Printf("没有有效的 IP 可用")
			continue
		}
		ipManager.SetCurrentIP(currentIP)

		// 创建用于控制 goroutine 退出的 context
		ctx, cancel := context.WithCancel(context.Background())

		// 用于状态检查完成的信号
		done := make(chan bool)

		var loopWG sync.WaitGroup
		loopWG.Add(2)

		// 启动状态检查线程
		go func() {
			defer loopWG.Done()
			statusCheck(ctx, *localAddr, *useTLS, *port, done, *domain, *code, time.Duration(*Delay)*time.Millisecond, ipManager, defaultProxyPool)
		}()

		// 主循环，接收连接
		go func() {
			defer loopWG.Done()
			for {
				select {
				case <-ctx.Done():
					log.Println("连接接受 goroutine 收到退出信号")
					return
				default:
					// 设置接受连接的超时，以便能够检查 context
					if tcpListener, ok := listener.(*net.TCPListener); ok {
						tcpListener.SetDeadline(time.Now().Add(1 * time.Second))
					}
					conn, err := listener.Accept()
					if err != nil {
						if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
							continue
						}
						if opErr, ok := err.(*net.OpError); ok && opErr.Err.Error() == "use of closed network connection" {
							return
						}
						log.Printf("接受连接时发生错误: %v", err)
						continue
					}

					clientAddr := conn.RemoteAddr().String()
					atomic.AddInt32(&activeConnections, 1)
					log.Printf("客户端来源: %s 连接建立，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))

					currIP := ipManager.GetCurrentIP()
					go handleConnection(conn, generateTargets(currIP, *port, *num), time.Duration(*Delay)*time.Millisecond, defaultProxyPool)
				}
			}
		}()

		<-done
		cancel() // 取消 context，通知所有 goroutine 退出
		loopWG.Wait()

		// 清空 IP 地址
		ipManager.Clear()
		validIPClientCache = sync.Map{}
		log.Println("主函数将退出当前循环，因为所有 IP 都已用尽")
	}
}

func runCarrierMode(specs []carrierListenSpec, resolvers map[string][]string, baiduDomain string, baiduPort int, baiduScanTarget string, baiduIPCount int, code int, coloFilter string, delayMS int, domain string, ipCount int, ipsType string, num int, port int, random bool, maxThreads int, useTLS bool, useBaiduProxy bool) error {
	locations, err := loadLocations()
	if err != nil {
		return fmt.Errorf("加载位置信息失败: %w", err)
	}

	locationMap := make(map[string]location)
	for _, loc := range locations {
		locationMap[loc.Iata] = loc
	}

	ipList, err := loadCandidateIPs(ipsType, random)
	if err != nil {
		return err
	}

	log.Printf("运营商分池模式启动，候选转发 IP 数量: %d", len(ipList))
	proxyPools := make(map[string]*BaiduProxyPool)
	if useBaiduProxy {
		proxyPools = buildBaiduPoolsByCarrier(resolvers, baiduDomain, baiduPort, baiduScanTarget, baiduIPCount, maxThreads)
		for _, spec := range specs {
			if _, ok := proxyPools[spec.carrier]; !ok {
				proxyPools[spec.carrier] = NewBaiduProxyPool(spec.carrier, nil)
			}
		}
	} else {
		log.Printf("百度前置代理已关闭，运营商端口将使用直连拨号")
	}

	var listeners []net.Listener
	for _, spec := range specs {
		proxyPool := proxyPools[spec.carrier]
		results := scanCarrierTargets(spec.carrier, ipList, locationMap, maxThreads, proxyPool, coloFilter, ipCount)
		targetPool := NewTargetPool(spec.carrier, results, port)

		listener, err := net.Listen("tcp", spec.addr)
		if err != nil {
			for _, l := range listeners {
				l.Close()
			}
			return fmt.Errorf("无法监听 %s(%s): %w", carrierName(spec.carrier), spec.addr, err)
		}
		listeners = append(listeners, listener)

		log.Printf("%s 监听 %s，百度代理节点 %d 个，转发目标 %d 个", carrierName(spec.carrier), spec.addr, proxyPool.Len(), targetPool.Len())
		go acceptCarrierConnections(listener, spec, targetPool, proxyPool, time.Duration(delayMS)*time.Millisecond, num)
	}

	select {}
}

func loadCandidateIPs(ipsType string, random bool) ([]string, error) {
	var url string
	var filename string
	switch ipsType {
	case "6":
		filename = "ips-v6.txt"
		url = "https://www.baipiao.eu.org/cloudflare/ips-v6"
	case "4":
		filename = "ips-v4.txt"
		url = "https://www.baipiao.eu.org/cloudflare/ips-v4"
	default:
		return nil, fmt.Errorf("无效的IP类型。请使用 '4' 或 '6'")
	}

	var content string
	var err error
	if _, err = os.Stat(filename); os.IsNotExist(err) {
		fmt.Printf("文件 %s 不存在，正在从 URL %s 下载数据\n", filename, url)
		content, err = getURLContent(url)
		if err != nil {
			return nil, fmt.Errorf("获取URL内容出错: %w", err)
		}
		if err = saveToFile(filename, content); err != nil {
			return nil, fmt.Errorf("保存文件出错: %w", err)
		}
	} else {
		content, err = getFileContent(filename)
		if err != nil {
			return nil, fmt.Errorf("读取本地文件出错: %w", err)
		}
	}

	if random {
		ipList := parseIPList(content)
		switch ipsType {
		case "6":
			return getRandomIPv6s(ipList), nil
		case "4":
			return getRandomIPv4s(ipList), nil
		}
	}

	ipList, err := readIPs(filename)
	if err != nil {
		return nil, fmt.Errorf("读取IP出错: %w", err)
	}
	return ipList, nil
}

func scanCarrierTargets(carrier string, ipList []string, locationMap map[string]location, maxThreads int, proxyPool *BaiduProxyPool, coloFilter string, ipCount int) []result {
	log.Printf("%s 开始扫描转发 IP，百度代理池: %s", carrierName(carrier), strings.Join(proxyPool.Addresses(), ","))
	results := scanIPs(ipList, locationMap, maxThreads, proxyPool)
	if len(results) == 0 {
		log.Printf("%s 未发现有效转发 IP", carrierName(carrier))
		return nil
	}

	if coloFilter != "" {
		filters := strings.Split(coloFilter, ",")
		var filteredResults []result
		for _, r := range results {
			for _, filter := range filters {
				if strings.EqualFold(r.dataCenter, strings.TrimSpace(filter)) {
					filteredResults = append(filteredResults, r)
					break
				}
			}
		}
		results = filteredResults
	}

	sort.Slice(results, func(i, j int) bool {
		return results[i].tcpDuration < results[j].tcpDuration
	})
	if ipCount > 0 && len(results) > ipCount {
		results = results[:ipCount]
	}

	fmt.Printf("%s IP 地址 | 数据中心 | 地区 | 城市 | 延迟\n", carrierName(carrier))
	for _, r := range results {
		fmt.Printf("%s | %s | %s | %s | %s | %s\n", carrierName(carrier), r.ip, r.dataCenter, r.region, r.city, r.latency)
	}
	return results
}

func acceptCarrierConnections(listener net.Listener, spec carrierListenSpec, targetPool *TargetPool, proxyPool *BaiduProxyPool, delay time.Duration, maxAttempts int) {
	for {
		conn, err := listener.Accept()
		if err != nil {
			log.Printf("%s 接受连接失败: %v", carrierName(spec.carrier), err)
			continue
		}

		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, 1)
		log.Printf("%s 客户端来源: %s 连接建立，当前活跃连接数: %d", carrierName(spec.carrier), clientAddr, atomic.LoadInt32(&activeConnections))
		go handlePoolConnection(conn, spec.carrier, targetPool, proxyPool, delay, maxAttempts)
	}
}

func handlePoolConnection(conn net.Conn, carrier string, targetPool *TargetPool, proxyPool *BaiduProxyPool, delay time.Duration, maxAttempts int) {
	defer func() {
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, -1)
		log.Printf("%s 客户端来源: %s 连接关闭，当前活跃连接数: %d", carrierName(carrier), clientAddr, atomic.LoadInt32(&activeConnections))
		conn.Close()
	}()

	targets := targetPool.PickTargets(maxAttempts)
	if len(targets) == 0 {
		log.Printf("%s 没有可用转发目标，关闭客户端连接", carrierName(carrier))
		return
	}

	var bestConn net.Conn
	var bestTarget *targetEndpoint
	var bestDelay time.Duration
	for _, target := range targets {
		atomic.AddInt32(&target.active, 1)
		start := time.Now()
		ctx, cancel := context.WithTimeout(context.Background(), delay)
		forwardConn, err := dialTarget(ctx, "tcp", target.addr, delay, proxyPool)
		cancel()
		elapsed := time.Since(start)
		if err != nil {
			atomic.AddInt32(&target.active, -1)
			target.recordFailure(elapsed)
			log.Printf("%s 连接目标 %s 失败或超时 %d ms: %v", carrierName(carrier), target.addr, delay.Milliseconds(), err)
			continue
		}

		target.recordSuccess(elapsed)
		if bestConn == nil || elapsed < bestDelay {
			if bestConn != nil {
				bestConn.Close()
				atomic.AddInt32(&bestTarget.active, -1)
			}
			bestConn = forwardConn
			bestTarget = target
			bestDelay = elapsed
		} else {
			forwardConn.Close()
			atomic.AddInt32(&target.active, -1)
		}
	}

	if bestConn == nil {
		log.Printf("%s 未找到符合延迟要求的连接，关闭客户端连接", carrierName(carrier))
		return
	}
	defer atomic.AddInt32(&bestTarget.active, -1)

	log.Printf("%s 选择目标: %s 延迟: %d ms", carrierName(carrier), bestTarget.addr, bestDelay.Milliseconds())
	pipeConnections(conn, bestConn)
}

func buildBaiduPoolsByCarrier(extraResolvers map[string][]string, domain string, port int, scanTarget string, maxNodes int, maxThreads int) map[string]*BaiduProxyPool {
	candidates := resolveBaiduProxyCandidates(domain, port, extraResolvers)
	if len(candidates) == 0 {
		log.Printf("没有解析到任何百度代理 IP")
		return nil
	}

	grouped := make(map[string][]string)
	for _, addr := range candidates {
		host, _, err := net.SplitHostPort(addr)
		if err != nil {
			log.Printf("跳过无效百度代理地址 %s: %v", addr, err)
			continue
		}

		carrier, asn, asName, err := classifyCarrierByIP(host)
		if err != nil {
			log.Printf("百度代理候选归属未知: %s: %v", addr, err)
			continue
		}
		if carrier == "" {
			log.Printf("百度代理候选未归入三大运营商: %s -> AS%s %s", addr, asn, asName)
			continue
		}

		log.Printf("百度代理候选归属: %s -> AS%s %s -> %s", addr, asn, asName, carrierName(carrier))
		grouped[carrier] = append(grouped[carrier], addr)
	}

	pools := make(map[string]*BaiduProxyPool)
	for carrier, addrs := range grouped {
		addrs = dedupeStrings(addrs)
		log.Printf("%s 百度代理候选池: %s", carrierName(carrier), strings.Join(addrs, ","))
		scanned := scanBaiduProxyAddrs(carrier, addrs, scanTarget, timeout, maxThreads)
		if maxNodes > 0 && len(scanned) > maxNodes {
			scanned = scanned[:maxNodes]
		}
		if len(scanned) == 0 {
			log.Printf("%s 没有扫描到可用百度代理 IP", carrierName(carrier))
			continue
		}

		log.Printf("%s 百度代理可用池: %s", carrierName(carrier), strings.Join(scanned, ","))
		pools[carrier] = NewBaiduProxyPool(carrier, scanned)
	}

	return pools
}

func resolveBaiduProxyCandidates(domain string, port int, extraResolvers map[string][]string) []string {
	resolvers := collectBaiduResolvers(extraResolvers)
	type lookupResult struct {
		source string
		ips    []string
		err    error
	}

	results := make(chan lookupResult, len(resolvers)+1)
	var wg sync.WaitGroup

	wg.Add(1)
	go func() {
		defer wg.Done()
		ips, err := net.LookupHost(domain)
		results <- lookupResult{source: "system", ips: ips, err: err}
	}()

	for _, resolverAddr := range resolvers {
		wg.Add(1)
		go func(addr string) {
			defer wg.Done()
			ips, err := lookupHostWithResolver(domain, addr)
			results <- lookupResult{source: addr, ips: ips, err: err}
		}(resolverAddr)
	}

	go func() {
		wg.Wait()
		close(results)
	}()

	var addrs []string
	for result := range results {
		if result.err != nil {
			log.Printf("解析百度代理域名失败 resolver=%s: %v", result.source, result.err)
			continue
		}

		var parsed []string
		for _, ip := range result.ips {
			if net.ParseIP(ip) == nil {
				continue
			}
			addr := ensureHostPort(ip, port)
			addrs = append(addrs, addr)
			parsed = append(parsed, addr)
		}
		if len(parsed) > 0 {
			log.Printf("解析百度代理域名成功 resolver=%s: %s", result.source, strings.Join(parsed, ","))
		}
	}

	addrs = dedupeStrings(addrs)
	sort.Strings(addrs)
	log.Printf("百度代理聚合候选 IP 数量: %d", len(addrs))
	return addrs
}

func collectBaiduResolvers(extraResolvers map[string][]string) []string {
	var resolvers []string
	resolvers = append(resolvers, defaultBaiduResolvers...)
	for _, values := range defaultCarrierResolvers {
		resolvers = append(resolvers, values...)
	}
	for _, values := range extraResolvers {
		resolvers = append(resolvers, values...)
	}

	for i, resolverAddr := range resolvers {
		resolvers[i] = ensureHostPort(resolverAddr, 53)
	}
	return dedupeStrings(resolvers)
}

func classifyCarrierByIP(ip string) (string, string, string, error) {
	asn, err := lookupASN(ip)
	if err != nil {
		return "", "", "", err
	}
	if asn == "" {
		return "", "", "", fmt.Errorf("没有查到 ASN")
	}

	asName, err := lookupASName(asn)
	if err != nil {
		return "", asn, "", err
	}

	carrier := carrierFromASN(asn, asName)
	return carrier, asn, asName, nil
}

func lookupASN(ip string) (string, error) {
	parsed := net.ParseIP(ip)
	if parsed == nil {
		return "", fmt.Errorf("无效 IP: %s", ip)
	}
	ipv4 := parsed.To4()
	if ipv4 == nil {
		return "", fmt.Errorf("暂不支持 IPv6 ASN 查询: %s", ip)
	}

	query := fmt.Sprintf("%d.%d.%d.%d.origin.asn.cymru.com", ipv4[3], ipv4[2], ipv4[1], ipv4[0])
	txts, err := net.LookupTXT(query)
	if err != nil {
		return "", err
	}
	if len(txts) == 0 {
		return "", nil
	}

	fields := strings.Split(txts[0], "|")
	if len(fields) == 0 {
		return "", nil
	}
	return strings.TrimSpace(fields[0]), nil
}

func lookupASName(asn string) (string, error) {
	txts, err := net.LookupTXT("AS" + strings.TrimSpace(asn) + ".asn.cymru.com")
	if err != nil {
		return "", err
	}
	if len(txts) == 0 {
		return "", nil
	}

	fields := strings.Split(txts[0], "|")
	if len(fields) < 5 {
		return strings.TrimSpace(txts[0]), nil
	}
	return strings.TrimSpace(fields[4]), nil
}

func carrierFromASN(asn string, asName string) string {
	asn = strings.TrimSpace(asn)
	name := strings.ToUpper(asName)

	switch asn {
	case "9808", "56040", "56041", "56042", "56044", "56046", "56047", "56048", "56050", "56052", "56055", "56056", "56057", "56058", "56059", "56060", "56061", "56062":
		return carrierMobile
	case "4134", "4809", "4812", "4816", "4811", "4813", "4815", "23724", "134756":
		return carrierTelecom
	case "4837", "4808", "9929", "10099", "17621", "136958", "140717":
		return carrierUnicom
	}

	switch {
	case strings.Contains(name, "MOBILE") || strings.Contains(name, "CMNET") || strings.Contains(name, "CMCC") || strings.Contains(name, "CHINAMOBILE"):
		return carrierMobile
	case strings.Contains(name, "TELECOM") || strings.Contains(name, "CHINANET") || strings.Contains(name, "CHINA NET") || strings.Contains(name, "CN2"):
		return carrierTelecom
	case strings.Contains(name, "UNICOM") || strings.Contains(name, "CHINA169") || strings.Contains(name, "CNCGROUP") || strings.Contains(name, "NETCOM"):
		return carrierUnicom
	default:
		return ""
	}
}

func buildCarrierBaiduPool(carrier string, resolvers []string, domain string, port int, scanTarget string, maxNodes int, maxThreads int) (*BaiduProxyPool, error) {
	addrs, err := resolveBaiduProxyAddrs(carrier, resolvers, domain, port)
	if err != nil {
		return nil, err
	}
	if len(addrs) == 0 {
		return nil, fmt.Errorf("%s 没有解析到百度代理 IP", carrierName(carrier))
	}

	log.Printf("%s 解析到百度代理候选: %s", carrierName(carrier), strings.Join(addrs, ","))
	scanned := scanBaiduProxyAddrs(carrier, addrs, scanTarget, timeout, maxThreads)
	if maxNodes > 0 && len(scanned) > maxNodes {
		scanned = scanned[:maxNodes]
	}
	if len(scanned) == 0 {
		return nil, fmt.Errorf("%s 没有扫描到可用百度代理 IP", carrierName(carrier))
	}
	log.Printf("%s 百度代理可用池: %s", carrierName(carrier), strings.Join(scanned, ","))
	return NewBaiduProxyPool(carrier, scanned), nil
}

func resolveBaiduProxyAddrs(carrier string, resolvers []string, domain string, port int) ([]string, error) {
	if len(resolvers) == 0 {
		resolvers = defaultCarrierResolvers[carrier]
	}

	var all []string
	var errs []string
	for _, resolverAddr := range resolvers {
		ips, err := lookupHostWithResolver(domain, ensureHostPort(resolverAddr, 53))
		if err != nil {
			errs = append(errs, fmt.Sprintf("%s: %v", resolverAddr, err))
			continue
		}
		for _, ip := range ips {
			if parsed := net.ParseIP(ip); parsed != nil {
				all = append(all, ensureHostPort(ip, port))
			}
		}
	}

	if len(all) == 0 {
		ips, err := net.LookupHost(domain)
		if err != nil {
			errs = append(errs, fmt.Sprintf("system: %v", err))
		}
		for _, ip := range ips {
			if parsed := net.ParseIP(ip); parsed != nil {
				all = append(all, ensureHostPort(ip, port))
			}
		}
	}

	all = dedupeStrings(all)
	if len(all) == 0 {
		return nil, fmt.Errorf("解析 %s 失败: %s", domain, strings.Join(errs, "; "))
	}
	return all, nil
}

func lookupHostWithResolver(host string, resolverAddr string) ([]string, error) {
	resolver := &net.Resolver{
		PreferGo: true,
		Dial: func(ctx context.Context, network, address string) (net.Conn, error) {
			dialer := &net.Dialer{Timeout: timeout}
			return dialer.DialContext(ctx, "udp", resolverAddr)
		},
	}

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	return resolver.LookupHost(ctx, host)
}

func scanBaiduProxyAddrs(carrier string, addrs []string, scanTarget string, dialTimeout time.Duration, maxThreads int) []string {
	type scanResult struct {
		addr    string
		latency time.Duration
	}

	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []scanResult
	if maxThreads <= 0 {
		maxThreads = 1
	}
	thread := make(chan struct{}, maxThreads)

	for _, addr := range addrs {
		wg.Add(1)
		thread <- struct{}{}
		go func(nodeAddr string) {
			defer func() {
				<-thread
				wg.Done()
			}()

			ctx, cancel := context.WithTimeout(context.Background(), dialTimeout)
			defer cancel()
			start := time.Now()
			conn, err := dialBaiduTunnelViaNode(ctx, nodeAddr, scanTarget, dialTimeout)
			elapsed := time.Since(start)
			if err != nil {
				log.Printf("%s 百度代理节点不可用 %s: %v", carrierName(carrier), nodeAddr, err)
				return
			}
			conn.Close()

			mu.Lock()
			results = append(results, scanResult{addr: nodeAddr, latency: elapsed})
			mu.Unlock()
			log.Printf("%s 百度代理节点可用 %s 延迟 %d ms", carrierName(carrier), nodeAddr, elapsed.Milliseconds())
		}(addr)
	}

	wg.Wait()
	sort.Slice(results, func(i, j int) bool {
		return results[i].latency < results[j].latency
	})

	scanned := make([]string, 0, len(results))
	for _, result := range results {
		scanned = append(scanned, result.addr)
	}
	return scanned
}

func parseCarrierListens(raw string) ([]carrierListenSpec, error) {
	var specs []carrierListenSpec
	seen := make(map[string]struct{})
	for _, part := range strings.Split(raw, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		carrier, addr, ok := strings.Cut(part, "=")
		if !ok {
			return nil, fmt.Errorf("无效项 %q，格式应为 carrier=host:port", part)
		}
		carrier = normalizeCarrier(carrier)
		if carrier == "" {
			return nil, fmt.Errorf("未知运营商 %q", part)
		}
		addr = strings.TrimSpace(addr)
		if addr == "" {
			return nil, fmt.Errorf("%s 的监听地址为空", carrierName(carrier))
		}
		if _, ok := seen[carrier]; ok {
			return nil, fmt.Errorf("%s 重复配置", carrierName(carrier))
		}
		seen[carrier] = struct{}{}
		specs = append(specs, carrierListenSpec{carrier: carrier, addr: addr})
	}
	if len(specs) == 0 {
		return nil, errors.New("未配置任何运营商监听端口")
	}
	return specs, nil
}

func parseCarrierResolvers(raw string) (map[string][]string, error) {
	resolvers := make(map[string][]string)
	if strings.TrimSpace(raw) == "" {
		return resolvers, nil
	}
	for _, part := range strings.Split(raw, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		carrier, value, ok := strings.Cut(part, "=")
		if !ok {
			return nil, fmt.Errorf("无效项 %q，格式应为 carrier=dns1|dns2", part)
		}
		carrier = normalizeCarrier(carrier)
		if carrier == "" {
			return nil, fmt.Errorf("未知运营商 %q", part)
		}
		for _, resolverAddr := range strings.Split(value, "|") {
			resolverAddr = strings.TrimSpace(resolverAddr)
			if resolverAddr == "" {
				continue
			}
			resolvers[carrier] = append(resolvers[carrier], ensureHostPort(resolverAddr, 53))
		}
	}
	return resolvers, nil
}

func normalizeCarrier(value string) string {
	switch strings.ToLower(strings.TrimSpace(value)) {
	case carrierMobile, "cmcc", "china-mobile", "移动", "中国移动":
		return carrierMobile
	case carrierTelecom, "ct", "chinanet", "china-telecom", "电信", "中国电信":
		return carrierTelecom
	case carrierUnicom, "cu", "cuc", "china-unicom", "联通", "中国联通":
		return carrierUnicom
	default:
		return ""
	}
}

func carrierName(carrier string) string {
	if name, ok := carrierDisplayNames[carrier]; ok {
		return name
	}
	return carrier
}

func ensureHostPort(addr string, port int) string {
	addr = strings.TrimSpace(addr)
	if addr == "" {
		return addr
	}
	if _, _, err := net.SplitHostPort(addr); err == nil {
		return addr
	}
	return net.JoinHostPort(strings.Trim(addr, "[]"), strconv.Itoa(port))
}

func dedupeStrings(values []string) []string {
	seen := make(map[string]struct{}, len(values))
	var out []string
	for _, value := range values {
		value = strings.TrimSpace(value)
		if value == "" {
			continue
		}
		if _, ok := seen[value]; ok {
			continue
		}
		seen[value] = struct{}{}
		out = append(out, value)
	}
	return out
}

// loadLocations 加载位置信息，使用函数封装确保 defer 正确执行
func loadLocations() ([]location, error) {
	var locations []location

	if _, err := os.Stat("locations.json"); os.IsNotExist(err) {
		fmt.Println("本地 locations.json 不存在\n正在从 https://www.baipiao.eu.org/cloudflare/locations 下载 locations.json")
		resp, err := http.Get("https://www.baipiao.eu.org/cloudflare/locations")
		if err != nil {
			return nil, fmt.Errorf("无法从URL中获取JSON: %v", err)
		}
		defer resp.Body.Close()

		body, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("无法读取响应体: %v", err)
		}

		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}

		file, err := os.Create("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法创建文件: %v", err)
		}
		defer file.Close()

		_, err = file.Write(body)
		if err != nil {
			return nil, fmt.Errorf("无法写入文件: %v", err)
		}
	} else {
		file, err := os.Open("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法打开文件: %v", err)
		}
		defer file.Close()

		body, err := io.ReadAll(file)
		if err != nil {
			return nil, fmt.Errorf("无法读取文件: %v", err)
		}

		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}
	}

	return locations, nil
}

// scanIPs 扫描 IP 列表并返回结果
func scanIPs(ipList []string, locationMap map[string]location, maxThreads int, proxyPool *BaiduProxyPool) []result {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []result

	thread := make(chan struct{}, maxThreads)

	var count int32
	total := len(ipList)

	for _, ip := range ipList {
		wg.Add(1)
		thread <- struct{}{}
		go func(ipAddr string) {
			defer func() {
				<-thread
				wg.Done()
				current := atomic.AddInt32(&count, 1)
				percentage := float64(current) / float64(total) * 100
				fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\r", current, total, percentage)
				if int(current) == total {
					fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\n", current, total, percentage)
				}
			}()

			start := time.Now()
			ctx, cancel := context.WithTimeout(context.Background(), timeout)
			defer cancel()
			conn, err := dialTarget(ctx, "tcp", net.JoinHostPort(ipAddr, "80"), timeout, proxyPool)
			if err != nil {
				return
			}
			defer conn.Close()

			tcpDuration := time.Since(start)

			// 通过根路径响应头里的 CF-RAY 提取机房信息
			requestURL := "http://" + net.JoinHostPort(ipAddr, "80")
			req, err := http.NewRequest("GET", requestURL, nil)
			if err != nil {
				return
			}
			req.Header.Set("User-Agent", "Mozilla/5.0")
			req.Close = true

			conn.SetDeadline(time.Now().Add(maxDuration))
			err = req.Write(conn)
			if err != nil {
				return
			}

			reader := bufio.NewReader(conn)
			resp, err := http.ReadResponse(reader, req)
			if err != nil {
				return
			}
			defer resp.Body.Close()

			cfRay := strings.TrimSpace(resp.Header.Get("CF-RAY"))
			if cfRay == "" {
				return
			}

			parts := strings.Split(cfRay, "-")
			if len(parts) < 2 {
				return
			}

			dataCenter := strings.TrimSpace(parts[len(parts)-1])
			if dataCenter == "" {
				return
			}

			loc, ok := locationMap[dataCenter]
			mu.Lock()
			if ok {
				fmt.Printf("发现有效IP %s 位置信息 %s 延迟 %d 毫秒\n", ipAddr, loc.City, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, loc.Region, loc.City, fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			} else {
				fmt.Printf("发现有效IP %s 位置信息未知 延迟 %d 毫秒\n", ipAddr, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, "", "", fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			}
			mu.Unlock()
		}(ip)
	}

	wg.Wait()
	return results
}

func dialTarget(ctx context.Context, network, targetAddr string, dialTimeout time.Duration, proxyPool *BaiduProxyPool) (net.Conn, error) {
	if proxyPool != nil {
		return proxyPool.Dial(ctx, targetAddr, dialTimeout)
	}

	dialer := &net.Dialer{
		Timeout:   dialTimeout,
		KeepAlive: 0,
	}
	return dialer.DialContext(ctx, network, targetAddr)
}

// dialBaiduTunnelViaNode 使用 test_proxy.go 中的固定百度 CONNECT 参数建立前置隧道。
func dialBaiduTunnelViaNode(ctx context.Context, nodeAddr string, targetAddr string, dialTimeout time.Duration) (net.Conn, error) {
	dialer := &net.Dialer{
		Timeout:   dialTimeout,
		KeepAlive: 0,
	}
	conn, err := dialer.DialContext(ctx, "tcp", nodeAddr)
	if err != nil {
		return nil, fmt.Errorf("连接百度前置代理失败: %w", err)
	}

	deadline := time.Now().Add(dialTimeout)
	if ctxDeadline, ok := ctx.Deadline(); ok && ctxDeadline.Before(deadline) {
		deadline = ctxDeadline
	}
	if err := conn.SetDeadline(deadline); err != nil {
		conn.Close()
		return nil, fmt.Errorf("设置百度前置代理超时失败: %w", err)
	}

	connectReq := fmt.Sprintf(
		"CONNECT %s HTTP/1.1\r\n"+
			"Host: %s\r\n"+
			"X-T5-Auth: %s\r\n"+
			"User-Agent: %s\r\n"+
			"Proxy-Connection: keep-alive\r\n"+
			"Connection: keep-alive\r\n"+
			"\r\n",
		targetAddr,
		baiduFakeHost,
		baiduAuthToken,
		baiduUserAgent,
	)
	if _, err := conn.Write([]byte(connectReq)); err != nil {
		conn.Close()
		return nil, fmt.Errorf("写入百度前置代理 CONNECT 失败: %w", err)
	}

	resp, err := http.ReadResponse(bufio.NewReader(conn), nil)
	if err != nil {
		conn.Close()
		return nil, fmt.Errorf("读取百度前置代理 CONNECT 响应失败: %w", err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		conn.Close()
		return nil, fmt.Errorf("百度前置代理 CONNECT 被拒绝: %s", resp.Status)
	}

	if err := conn.SetDeadline(time.Time{}); err != nil {
		conn.Close()
		return nil, fmt.Errorf("清除百度前置代理超时失败: %w", err)
	}

	return conn, nil
}

// 获取URL内容
func getURLContent(url string) (string, error) {
	resp, err := http.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("HTTP请求失败，状态码: %d", resp.StatusCode)
	}

	var content strings.Builder
	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			content.WriteString(line + "\n")
		}
	}
	if err := scanner.Err(); err != nil {
		return "", err
	}

	return content.String(), nil
}

// 从本地文件读取内容
func getFileContent(filename string) (string, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return "", err
	}
	return string(data), nil
}

// 将内容保存到本地文件
func saveToFile(filename, content string) error {
	return os.WriteFile(filename, []byte(content), 0644)
}

// 解析IP列表，跳过空行
func parseIPList(content string) []string {
	scanner := bufio.NewScanner(strings.NewReader(content))
	var ipList []string
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			ipList = append(ipList, line)
		}
	}
	return ipList
}

func nextRandomIntn(n int) int {
	randomMu.Lock()
	defer randomMu.Unlock()
	return randomGenerator.Intn(n)
}

// 从每个/24子网随机提取一个IPv4
func getRandomIPv4s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		// 跳过空行
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}
		baseIP := strings.TrimSuffix(subnet, "/24")
		octets := strings.Split(baseIP, ".")
		if len(octets) >= 4 {
			octets[3] = fmt.Sprintf("%d", nextRandomIntn(256))
			randomIP := strings.Join(octets, ".")
			randomIPs = append(randomIPs, randomIP)
		}
	}
	return randomIPs
}

// 从每个/48子网随机提取一个IPv6
func getRandomIPv6s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		// 跳过空行
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}
		baseIP := strings.TrimSuffix(subnet, "/48")
		sections := strings.Split(baseIP, ":")
		if len(sections) >= 3 {
			sections = sections[:3]
			for i := 3; i < 8; i++ {
				sections = append(sections, fmt.Sprintf("%x", nextRandomIntn(65536)))
			}
			randomIP := strings.Join(sections, ":")
			randomIPs = append(randomIPs, randomIP)
		}
	}
	return randomIPs
}

// 从CIDR中拆分出所有IP
func readIPs(filename string) ([]string, error) {
	file, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var ips []string
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		// 跳过空行
		if line == "" {
			continue
		}
		if strings.Contains(line, "/") {
			ipAddr, ipNet, err := net.ParseCIDR(line)
			if err != nil {
				return nil, err
			}
			// 使用新变量避免遮蔽
			for currentIP := ipAddr.Mask(ipNet.Mask); ipNet.Contains(currentIP); incrementIP(currentIP) {
				ips = append(ips, currentIP.String())
			}
		} else {
			ips = append(ips, line)
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, err
	}

	return ips, nil
}

// 增加IP
func incrementIP(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

func generateTargets(ip string, port int, num int) []string {
	targets := make([]string, num)
	address := net.JoinHostPort(ip, fmt.Sprintf("%d", port))
	for i := 0; i < num; i++ {
		targets[i] = address
	}
	return targets
}

func checkValidIP(ip string, port int, useTLS bool, domain string, code int, proxyPool *BaiduProxyPool) bool {
	address := net.JoinHostPort(ip, fmt.Sprintf("%d", port))
	targetURL := fmt.Sprintf("http://%s", domain)
	if useTLS {
		targetURL = fmt.Sprintf("https://%s", domain)
	}

	cacheKey := fmt.Sprintf("%s|%s", proxyPool.CacheKey(), address)
	clientAny, loaded := validIPClientCache.Load(cacheKey)
	var client *http.Client
	if loaded {
		client = clientAny.(*http.Client)
	} else {
		transport := &http.Transport{
			TLSClientConfig:   &tls.Config{InsecureSkipVerify: true},
			DisableKeepAlives: true,
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				log.Printf("尝试连接 IP: %s 端口: %d", ip, port)
				return dialTarget(ctx, network, address, 2*time.Second, proxyPool)
			},
		}
		newClient := &http.Client{
			Timeout:   2 * time.Second,
			Transport: transport,
		}
		actual, _ := validIPClientCache.LoadOrStore(cacheKey, newClient)
		client = actual.(*http.Client)
	}

	log.Printf("向 URL %s 发送请求以检查 IP %s 是否有效", targetURL, ip)
	resp, err := client.Get(targetURL)
	if err != nil {
		log.Printf("检查 IP %s 时发生错误: %v", ip, err)
		return false
	}
	defer resp.Body.Close()

	log.Printf("IP %s 的检查响应状态码: %d", ip, resp.StatusCode)

	isValid := resp.StatusCode == code
	if isValid {
		log.Printf("IP %s 是有效的", ip)
	} else {
		log.Printf("IP %s 不是有效的", ip)
	}

	return isValid
}

func selectValidIP(ipManager *IPManager, useTLS bool, port int, domain string, code int, proxyPool *BaiduProxyPool) string {
	for _, ip := range ipManager.GetIPAddresses() {
		if checkValidIP(ip, port, useTLS, domain, code, proxyPool) {
			return ip
		}
	}
	return ""
}

func statusCheck(ctx context.Context, localAddr string, useTLS bool, port int, done chan bool, domain string, code int, delay time.Duration, ipManager *IPManager, proxyPool *BaiduProxyPool) {
	_, localPort, _ := net.SplitHostPort(localAddr)
	checkAddr := fmt.Sprintf("127.0.0.1:%s", localPort)

	for {
		select {
		case <-ctx.Done():
			log.Println("状态检查收到退出信号")
			return
		default:
		}

		failCount := 0
		log.Printf("开始状态检查，目标地址: %s", checkAddr)

		for failCount < 2 {
			select {
			case <-ctx.Done():
				log.Println("状态检查收到退出信号")
				return
			default:
			}

			conn, err := net.DialTimeout("tcp", checkAddr, delay)
			if err != nil {
				failCount++
				log.Printf("状态检查失败 (%d/2): 无法连接到 %s 错误: %v", failCount, checkAddr, err)
				time.Sleep(1 * time.Second)
				continue
			}

			// 使用带超时的读取检查
			checkSuccess := make(chan bool, 1)
			go func() {
				reader := bufio.NewReader(conn)
				conn.SetReadDeadline(time.Now().Add(delay + 1*time.Second))
				_, err := reader.ReadString('\n')
				if err != nil {
					if err == io.EOF {
						checkSuccess <- false
					} else if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
						// 超时说明连接保持正常
						checkSuccess <- true
					} else {
						checkSuccess <- false
					}
				} else {
					checkSuccess <- true
				}
			}()

			select {
			case success := <-checkSuccess:
				if success {
					log.Printf("状态检查成功: 连接到 %s 成功", checkAddr)
					failCount = 0
				} else {
					failCount++
					log.Printf("状态检查失败 (%d/2): 服务端断开连接", failCount)
				}
			case <-time.After(delay + 2*time.Second):
				log.Printf("状态检查成功: 连接到 %s 保持稳定", checkAddr)
				failCount = 0
			case <-ctx.Done():
				conn.Close()
				log.Println("状态检查收到退出信号")
				return
			}

			conn.Close()

			if failCount == 0 {
				time.Sleep(2 * time.Second)
				break
			}
		}

		if failCount >= 2 {
			log.Println("连续两次状态检查失败，切换到下一个 IP")
			if !ipManager.switchToNextValidIP(useTLS, port, domain, code, proxyPool) {
				log.Println("所有 IP 都已检查过，状态检查停止")
				done <- true
				return
			}
		}
	}
}

// 处理客户端连接，尝试连接到指定的转发地址，并选择延迟最低的连接
func handleConnection(conn net.Conn, forwardAddrs []string, delay time.Duration, proxyPool *BaiduProxyPool) {
	defer func() {
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, -1)
		log.Printf("客户端来源: %s 连接关闭，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))
		conn.Close()
	}()

	type connResult struct {
		conn   net.Conn
		addr   string
		delay  time.Duration
		errMsg string
	}

	results := make(chan connResult, len(forwardAddrs))

	// 并发尝试连接每个转发地址
	for _, addr := range forwardAddrs {
		go func(targetAddr string) {
			start := time.Now()
			ctx, cancel := context.WithTimeout(context.Background(), delay)
			defer cancel()
			forwardConn, err := dialTarget(ctx, "tcp", targetAddr, delay, proxyPool)
			elapsed := time.Since(start)

			if err != nil {
				results <- connResult{nil, targetAddr, elapsed, fmt.Sprintf("连接到 %s 失败或延迟超过有效值 %d ms: %v", targetAddr, delay.Milliseconds(), err)}
				return
			}

			results <- connResult{forwardConn, targetAddr, elapsed, ""}
		}(addr)
	}

	var validConns []connResult
	var bestConn net.Conn
	var bestDelay time.Duration
	var bestAddr string

	// 收集结果并找到延迟最低的有效连接
	for i := 0; i < len(forwardAddrs); i++ {
		res := <-results
		if res.conn != nil {
			validConns = append(validConns, res)

			if bestConn == nil || res.delay < bestDelay {
				if bestConn != nil {
					bestConn.Close()
				}
				bestConn = res.conn
				bestDelay = res.delay
				bestAddr = res.addr
			} else {
				res.conn.Close()
			}
		} else {
			log.Printf("错误: %s", res.errMsg)
		}
	}

	log.Println("符合要求的连接:")
	for _, vc := range validConns {
		log.Printf("地址: %s 延迟: %d ms", vc.addr, vc.delay.Milliseconds())
	}

	// 如果找到最佳连接，开始转发数据
	if bestConn != nil {
		log.Printf("选择最佳连接: 地址: %s 延迟: %d ms", bestAddr, bestDelay.Milliseconds())
		pipeConnections(conn, bestConn)
	} else {
		log.Println("未找到符合延迟要求的连接，关闭客户端连接")
	}
}

func pipeConnections(src, dst net.Conn) {
	var wg sync.WaitGroup
	var closeOnce sync.Once
	closeBoth := func() {
		closeOnce.Do(func() {
			src.Close()
			dst.Close()
		})
	}

	wg.Add(2)

	go func() {
		defer wg.Done()
		_, _ = io.Copy(src, dst)
		closeBoth()
	}()

	go func() {
		defer wg.Done()
		_, _ = io.Copy(dst, src)
		closeBoth()
	}()

	wg.Wait()
}
