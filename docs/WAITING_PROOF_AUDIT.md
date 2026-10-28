# 临时等待证明

本入口保留尚未完成的运行语义假设，不是完成的电路证明。

## 数据与确认

A 组确认：Lamport d55887e4、db355cbb。B 组精确确认：f27cd75c。
Dirac 的接口决定 be93ebba 与准入 e4e2de48 允许本次更新。
实际程序来自 PR216 的 s2ForwardProgram、s6ForwardProgram、s6EraseProgram。
所有程序、布局、前缀、后缀、游标、pre、records 与 phaseDebt 都是显式定义。

前向 actualPrefix/scanAndHalves 由实际 Uses.take 2/drop 2 实例化。
程序分解直接证明。actualPrefix 与旧 lift/fold 要求完整状态语义相等，
并单独要求测量计数相等，保证后缀的游标一致；不要求两个门列表相等。
合法游标分别是源程序起点 53734、422703。对应起点的合法性直接证明。

逆乘的 pre 包含原始 HmrRowMulPre，以及存在 start 的 records 和
HmrEraseBoundary。records 固定 start=422703、cursor=620345，实际起点
可满足该条件。eraseRule6.accepts 直接封装这些前提。

三个执行导出的相位债是 xor 初始相位 执行后相位。它们只提供恒等式，
不提供跨调用抵消、整体相干性或误差界。A 组 unpark 的相位债仍为 false，
只表示恢复当前相位，不清偿此前 K2 的相位债。

## 等待项与边界

唯一允许 sorry 的文件是 WaitingOnProducer.lean。剩余 7 条具名 Prop 义务：

| 项目 | 数量 | 生产方 |
|---|---:|---|
| unpark2 的 run | 1 | task #50 |
| forward2/forward6 各自 run | 2 | task #49 |
| erase6 的 run | 1 | task #49 / task #50 |
| 三个程序各自 releaseZero | 3 | task #49 / task #50 |

四条 support 和三条 wellFormed 已由源模板结构和实际端口表证明。
临时审计也检查这七条不依赖 sorryAx。

剩余每条定理注释记录确认消息、程序名和消费方 PR215。结构本身不整条 sorry。
每个 releaseZero 对实际 Lifecycle 全称量化，状态使用实际程序 take n
执行后的状态。共覆盖三处各 498 次释放，不拆成 1494 条假设。
它不从最终 scratch 清零推出，不使用任意 stateAt，也不把 R 当作 reset。

## 两张审计表

严格入口保持原白名单 propext、Classical.choice、Quot.sound。
根模块不导入等待文件。新增有限数据证明进入严格表，原入口顺序不变。
两处 prefix_run 和 prefix_measurements 共四条已证明并移入严格表；
严格审计单独导入等待模块以检查这四个证明的实际依赖，根模块仍不导入它。
临时入口独立运行，共 42 条，其中 7 条登记为等待 Prop 证明。
Lean 检查登记类型并遍历真实依赖；Python 拒绝未登记的 admission、缺失
或重复入口及额外公理。14 个显式数据定义必须不依赖 sorryAx。
临时表通过只表示假设边界可追踪，不能记作严格电路证明完成。

K2/K6/J 的恢复、实际三调用绑定、整机 ≤935 与具体误差接入仍未完成。
