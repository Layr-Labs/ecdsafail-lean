# 来源与复现

数学层改编自 [VerifiedQC/ShorECDLP](https://github.com/VerifiedQC/ShorECDLP) 的提交 `15d2a336743304e069f8a8a468c6ab1da334577b`：`Math/BitcoinCurve.lean`、`Math/BitcoinPrimes.lean` 和 `Math/EllipticCurve/AffineFormula.lean`。命名空间改为 ECDSAAdd，AffineFormula 路径扁平化并直接使用已证 p 素性的实例。BitcoinPrimes 仅保留 `lucasFromFactors`、`p_prime` 所需的 40 条 `prime_cert_*` 及字段/曲线实例；未复制群阶证明。BitcoinCurve 保留群、生成元 G 和坐标；所有证明重新由 Lean 检查。Framework、AND 与 Arithmetic 程序及证明为本项目编写，Hoare/program 语法糖改编自 Dirac 在项目频道提供的原型。

`Math/Kaliski.lean`、`Math/ModularHalving.lean`、`Math/KaliskiInverse.lean` 为本项目按已确认的二进制 EEA/Kaliski 算法规格编写的数学证明；未复制上游求逆实现，也不包含求逆电路。

Lean 固定为 `leanprover/lean4:v4.28.0`；Mathlib 固定为 `fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42`。全新检出执行 `lake exe cache get`，再执行 `scripts/verify.sh`；不需要其他本地仓库。公理检查针对脚本列出的公开定理及其传递依赖，不是全环境声明审计。

本仓库为 private；Apache 2.0 由 Runzhou 于 2026-09-08 指定。所检上游提交没有 LICENSE，此声明不表示上游独立选择了该许可证。详见 [NOTICE](../NOTICE)。

I2 的 CSWAP 交换网络、移位和 10 位计数原语及证明为本仓库新增。CSWAP 使用标准 CX/CCX 分解；计数器复用已有加法器和前向 XOR 清理，没有复制新的外部源码。

I3 的 Math/KaliskiRound 与单轮布局、比较、零检测、受控加减、记录、正逆轮组合和资源证明均为本项目编写。算法根据频道确认的 EEA 路线，修正十位计数、终止轮计数时机与完整两位编码；计数比较采用固定 i<更新后 k 恢复活动性。未复制外部电路或证明源码，也未运行数值样例、Python 对照或真值表。I3 只实现单轮与逆轮；I4 与 I5 的后续实现见下文。

I4 的记录带循环、模减半/模加倍互逆证明、条件 XOR 包装、规范化取负、第二阶段循环和整体反计算均为本项目编写，复用 I1–I3 及既有模加减的已证程序。终态 r 先取模再取负，不假定 r<p；计数器在第二阶段保持。没有复制新的外部源码，没有新增测试、Python 数值对照或真值表。共享外部寄存器框架从既有 Double 实现提取，模加证明扩展到输入和小于两倍模数，既有公开模加/模乘接口保持兼容。

I5 的 InverseLayout/InverseLoad/InverseSpec/InverseResources 为本项目编写，复用已证 I4 内核及 I1 的 kaliski_inverse_p。装载与卸载使用既有 copyRegister/xorConstant；六字段值表仅用于封装证明中的寄存器保持与更新。布局置换、输出高位清零和实际支持集均由 Lean 证明；没有复制新外部源码，没有增加数值测试或对照程序。旧 Halve（本次已删除）曾使用已载入奇模数最低位作为移位控制。

M3 第一部分的相等检测、分支标志、安全除数、共享池端口布局、候选计算/清理及资源证明均为本项目编写，依照频道确认的六减、三乘、一次求逆方案，复用已证模算术与 I5。候选数学关系复用已有 AffineFormula；未复制其他论文的电路或证明源码。本部分是既有算术模块的正确性基线，不实现另行讨论的原地算术优化。没有新增数值测试、Python 对照、真值表或公理。

M3 第二部分的完整分类、共享池零检测映射、常量/候选输出、点状态组合、完整 XOR 规格及实际支持集/资源证明均为本项目编写，复用第一部分的候选程序及既有 AffineFormula 曲线性质。未复制新的外部程序或证明源码；仍是已确认的算术基线，不包含另行规划的原地算术或 Montgomery 优化。完整点加覆盖所有合法点，受控原地组合见下文。没有新增测试、数值对照、真值表、公理或证明资源限制放宽。

M3 第三部分的四线控制扩展、最终输出选择、受控点交换、两次前向调用的组合规格及实际支持/资源证明均为本项目编写，复用前两部分点加、既有 CSWAP 和寄存器交换。没有复制新的外部源码，没有引入全算术受控变换；不包含另行规划的原地算术或 Montgomery 优化。没有新增测试、Python 数值对照、真值表、公理或证明资源限制放宽。

基础层的 `majority`、`addInPlace`/`subInPlace`、受控常数/寄存器加减和 `compareChain`/`compareLt`/`compareLtConst` 为本项目编写，按 [REWORK_PLAN](REWORK_PLAN.md) §1.1 与 §5.2 的构造（Gidney 2018 "Halving the cost of quantum addition" 的进位链、和位写回与比较器思路），门列复用现有 `fullAdder` 的进位段与 `eraseCarry`。擦除顺序按独立复审意见改为"先擦进位再写和位"，最高位不算进位。`Math/ModularHalving.lean` 的三条奇偶/加倍引理为本项目编写。`RippleAdder.lean` 的 `sum_value_step` 由私有改为公开以供复用，陈述未变。没有复制外部程序或证明源码，没有新增测试、数值对照、真值表、公理或证明资源限制放宽。

改 1：`HalveInPlace.lean` 与重写的 `HalvingLoop.lean` 按已复审设计实现原地减半、显式加倍恢复与固定轮数正逆证明。奇数加模数、移位、从输出范围恢复奇偶的构造依据 Roetteler 等（2017）Fig. 4 的模减半/加倍思路，基础加法及比较器复用上节的 Gidney 原语。证明和布局复用代码均为本项目编写，未复制外部源码。删除旧 out-of-place Halve/两字交替循环，保留 Double（模乘仍调用）。历史基线 fieldInverse 为 14,303,280/6,936,624/6,468，本次变为 5,626,928/2,198,576/6,211；第二阶段仍正反两遍，公开 XOR 接口不变。未新增测试、公理、native_decide 或放宽证明资源限制。

改 4 首批：计数活动比较直接组合本项目已证明的 Gidney 比较器与 X 门。删除旧 Borrow 包装，当时将仍用到的数学引理移为 RecordRound 私有引理。新接口、frame、精确支持及资源适配均为本项目证明，未复制外部源码；完整求逆从5,626,928/2,198,576降至5,596,208/2,167,856，内部线路仍为5,955。该批记录段门列未变；后续记录段改动见下段。

改 4 记录段：组合本项目已证明的受控 compareLt 与四个条件 CCX、两个记录 CX，直接写两位分支记录；没有复制外部源码或新增比较链。全部 XOR 记录、工作位恢复和全测量记录相位结论由本项目证明；删除 CaseRecord 和已无调用的 subtraction_high。记录段由2w+5/2w降至w+5/w，完整求逆再省263,168至5,333,040/1,904,688，内部5,955线保持。

## 改 2 C1 原地模加减

依照已复审 REWORK_PLAN §12 的显式门列实现，复用本仓库 Gidney 原地加法器、比较器、常数装卸及 Reduction 数学引理。扩宽约减/比较清借位、低位受控复制和取负组合证明由 Lamport 在本仓库编写，无外部源码复制。正确性与资源针对同一程序，模型仍为带符号基态分支；该阶段完成四个模加减接口；后续 C2/D 见下文。

改 5：零检测沿本项目AND测量擦除模型，针对负输入以X包夹CZ修正，递归证明对任意测量记录的完整状态恢复。原地受控算术复用已有Gidney原语，不新增另一套加法器。支持证明去除旧out银行、保留池编号；门列、组合证明与资源传播均为本项目编写，未复制外部源码。完整求逆由5,333,040/1,904,688/6,211变为4,541,488/1,639,472/5,954；受控点加52,914,997/31,848,736/74,024。无测试、新公理、native_decide或证明资源放宽。

## 改 2 C2 半倍与 Horner

按已复审 §12 实现固定线路上的三 CX 旋转、无控制模加倍/减半及 Horner 正向和清理。复用仓库内 Gidney 加法/比较器、C1 模加减与 HalvingBijection 数学；前缀递推、全部组合证明、精确支持与资源由 Lamport 在本仓库编写，未复制外部源码。C1 的两个阶段引理仅去除 private 供加倍复用。清理用前向模减和减半，模型仍为带符号基态分支。未添加测试、数值 oracle、新公理或放宽证明资源限制；该阶段尚未接入域乘法和点加，后续 D 接入见下文。

## 改 2 D 适配器与共享池迁移

XOR/模乘加/模乘减以本仓库 C2 临时积内核、既有复制和 C1 模加减组合；全部规格、逐线保持、门数与支持由 Lamport 在本仓库证明。域乘法布局换为固定临时积，删除旧倍数链及其仅用辅助文件，无外部源码复制。保留改 5 求逆的池编号，新的候选支持是模减前缀与求逆实际支持的并集；97 根旧 out 位继续不触及。现有点加算法与四次求逆/十二次乘法调用不变，受控结果为32,347,957/17,585,440/9,718，未声称最大存活数或最优性。未增加测试、数值 oracle、新公理或放宽证明资源限制。


改 3 数学批：`Math/PointInPlace.lean` 的有限点分类、输出侧平移谓词、原地坐标等式、第二除数零点与例外斜率证明均由本项目编写，直接复用已有 `AffineFormula`、Mathlib 点群律和域运算。数学步骤对应已复审 REWORK_PLAN §16；没有复制新的外部源码。此批没有修改电路或宣称实现新的资源目标，没有新增测试、公理、native_decide 或放宽证明资源限制。


改3除法批：依照§16的直接装卸、准备、临时乘积、受控累加、清积、恢复门列，复用仓库内 inverseCompute_values/InverseMiddle、C1模加减与D的Horner内核。布局分割、全部记录相位与工作清理、完整输入输出规格、逐线保持和精确支持/门数由Deutsch在本仓库编写。未复制外部源码，未改变求逆算法或现有模乘/点加门列，未增加测试、新公理、native_decide或证明资源放宽。未来改6a的历史布局不由本批1030位分割覆盖。

### 改 3 原地点加本体

Deutsch依照已复审§16和本仓库数学/除法接口编写PointInPlace系列：直接子视图、规范常数加/取负、独立副本减平方、普通分支、完整点分类/角落XOR/输出清标志、逐线保持与精确支持。公开controlledPointAdd规格未变，有限门列替换为两次除法与五个乘积，实际资源14,998,618/7,880,538/6,218，布局仍分配9,817位。平方的t/S先清理再加3cx，以满足复用工作区的零前提；这保持设计数学和预算。删除旧ControlledPointPair及专用装载/擦除组合，独立XOR接口保留。实现与Lean证明均为本项目编写，未复制外部源码；无测试、额外公理或证明限制放宽。
### 改6a数学与查表

按REWORK_PLAN §17实现。本项目直接证明基16的整数不变量、secp256k1低位与ZMod转换关系；查表采用16项逐项三层AND匹配、既有受控常数XOR与CZ测量清理。未搬用论文的15-Toffoli查表或更低成本受控加法预算。完整verify实际输出见PROOF_STATUS，该批之后的P/Q实现见下；域乘法接入尚未实现。

### 改6a准备与恢复电路

按已复审的REWORK_PLAN §17.3/17.4，在本项目实现物理旋转、变量/常数四位窗口、两段64轮计算及前向恢复。复用原地加减、受控加减、查表与复制；未复制外部源码。窗口记录用已证整数商的基16展开描述，规范化借位保存至恢复；MontgomeryConversion 将整数恒等式与ZMod标准表示转换接到实际程序。MontLayout 的第二段通过结构更新共享辅助寄存器，MontPrepared 明确列出两段历史；内部P/Q的Triple、相位/逐线保持、门数及实际支持均由Lean验证。未新增状态语义框架、测试、新公理、native_decide或证明资源放宽。五个输出适配器和域乘法/点加接入留在后续批次。

## 改6a第三批：输出适配器与域乘法

MontAdapterLayout/Spec/Frame/Resources复用本项目P/Q和C1模算术，按REWORK_PLAN §17.4组合五个适配器，未引入外部代码。中段carry长度由设计笔误255更正为256，既有260位分配不变。fieldMul迁移到MontLayout；共享池前缀1827及实际支持5670、旧XOR点加路径资源均重证。除法与受控原地点加仍使用Horner，待下一批迁移。完整verify为2140项构建、259条实际公理输出，白名单不变。

## 改6a第四批：除法与原地点加

沿用§16的算法和公开寄存器契约，把五个Horner乘积替换为§17的Montgomery适配器。borrowedMont仅把既有poolMul映射到借用列表连续片段；平方S清理先于复用其线路的常数加。旧Horner四文件和MulAdapter三文件已无电路调用者，本PR保留，后续另交清理PR；数学HornerMultiply与半倍原语仍被复用。最终资源11,800,058/4,656,378/6,218由同一完整程序证明；未增加测试、公理或放宽证明限制。

## 改6a独立清理批

按复审清单删除无调用者的Horner四文件、MulAdapter三文件、controlledPointSwap与PointSwap。regValue_bit陈述与证明逐字迁移、仅改所在文件至Registers；其余源码变化只有删除及导入路径调整。半倍原语与Montgomery仍复用的数学保留，活动程序、功能规格和资源不变。


### 改7方案1：共享前缀的单迭代查表

Deutsch依照已复审§18.6在本仓库编写lookupWalk及其递归证明：正AND子树、CX切负分支、负AND测量修正，两半直接由地址a0使能。未复制外部代码、未引用15门预算代替实际计数；14/14来自同一程序的递归计数。lookup_spec与controlledPointAdd_spec陈述逐字保持，资源和支持传播到现有Montgomery/域乘法/除法/点加。Framework未改，逐位测量清表的方案2只留设计。实际公理输出244条，完整verify通过，无测试、新公理或证明限制放宽。

## 改8第一批：测量清掩码受控加减

本批直接复用本库AND测量清理语义及InPlaceAdder的加减门列：中段保持t=c AND src，末段每位测量并用CZ c src[i]消除相位。新文件MeasuredMaskedAdder证明全记录正确性、目标外逐线保持和精确资源；没有引入新的量子语义或外部未验证原语。原InPlaceAdder三个内部组合引理改为可跨文件复用的具名引理，陈述与证明主体保持，其余旧公开规格/门列不变。尚未接入Montgomery，完整点加成本不变。

## 改8窗口集成

MontPrepare变量窗口接入MeasuredMaskedAdder，按已审§20的门列组合；MontDigit规格、精确支持和全部下游资源重新证明。常数窗口、查表、求逆和公开点加契约不变；同程序完整点加11,001,338 Toffoli /5,193,978测量 /6,218线。完整verify2134/252通过，实际公理输出保存于PROOF_STATUS；没有新的外部证明来源或语义扩展。

## 改10 Kaliski轮集成

复用本仓库MeasuredMaskedAdder已证原语，替换RoundFrame.inplaceArithmetic的加减分支；不引入外部证明或语义。保留RoundFrame与公开求逆/点加规格，重证精确支持和下游资源。完整点加9,948,666 Toffoli /6,246,650测量 /6,218线；这是门数换测量的优化。


### 改11第一批：十位查表与计数缩放数学

Deutsch按REWORK_PLAN §22自主组合本仓库的递归lookup与Montgomery数学。lookup的私有通用长度证明供四位和十位规格共用，新增计数/相位清理/frame/支持证明；门列定义未变。InverseScaleFactor用ZMod单位关系证明R补偿、单段缩放与既有Kaliski数学一致，不依赖外部代码、额外公理或测试。缩放组合电路尚未实现，当前求逆和点加资源保持。


### 改11第二批：缩放组合电路

Deutsch按§22组合既有lookup10、montPrepare/montRestore与copyRegister。私有Values仅记录各门列边界的寄存器值；显式InverseScaleLayout和InverseLoopLayout视图给出实际借用，不引入回调或状态框架。完整相位/清理/frame、308,744/308,744计数及借用互异证明均由本仓库原语推出，无外部代码或新公理。当前求逆和点加门列尚未替换。


### 改11第三批：计数缩放接入求逆

Deutsch组合本仓库第一阶段循环、negativeInit及第二批计数缩放，显式证明y=N/carry商与借位的历史生命周期。数学使用已证kaliski_montgomery_scale；全部测量记录、使用段frame与最终双向支持从相同门列推出，无外部代码或新语义。内部任意奇数规格收窄为q%16=15/固定256位，外部secp256k1规格保持。

改10历史基线fieldInverse4,015,152/2,165,808、点加9,948,666/6,246,650；改11后分别3,513,912/1,928,760和8,946,186/5,772,554，线数5,954/6,218不变。每次求逆净少501,240/237,048，完整点加净少1,002,480/474,096。2138/276完整验证日志为证据，未放宽限制。

### D1 第一批：正偶终态与原地取负

Deutsch从本仓库Kaliski状态机证明终态u/v/s为1/0/q、r为正偶数并小于2q；早终止后的恒等轮保持该性质。可逆取负采用现有rotateRight、negRaw、dblInPlace，恢复采用halfInPlace、negRaw、rotateLeft，全部为显式前向门列。数学恢复公式与Triple、逐线保持、精确T/M/支持在本仓库证明，无外部实现、新公理或证明限制变更。

本批仅建立组合所需基础，尚未替换求逆/除法/点加程序；8,946,186/5,772,554/6,218保持为当前受控点加已证资源。工作区借用映射与后续节省仍待后两批。


Q1的一位记录入口按已审§24由本项目编写：四分支更新与奇数整数不变量推出交换位由更新后的r奇偶恢复，recoverSwap使用CX与CCX各一次；未复制外部代码或证明。单轮继续复用已有RecordRound/RoundBody/Counter，通用两位入口不变；循环压缩与下游接入另批。无数值测试、真值表、额外公理或心跳限额调整。
### D1 第二批：实际借用视图与终态常量清理

Deutsch按§23直接列出旧银行前804位、B=1828及外层P=2603的物理列表；r、原518位缩放历史和B的置换与Nodup由旧布局的全局互异推出，记录带从未借出。缩放、取负视图按固定切片构造，getD回退只服务坏布局全域定义，所有合法索引均由长度证明覆盖。

终态常量程序只用两次xorConstant，同一程序负责清除和写回u=1/s=q；已证明寄存器规格、目标外frame及零T/M。3673是将来组合支持列表的已证长度，尚不是新求逆或点加程序的qubitCount结论。本批不改变其现有门列或资源；无外部实现、新公理或证明资源放宽。


### D1 第三批a：求逆组合与资源传播

Deutsch组合本仓库已证明的终态常量、negativeEven与紧缩缩放视图，明确r/H/B生命周期及全测量记录相位。结果移到r要求同步Divide；旧外层物理位置保留，支持通过除法与外部乘积/平方的并集逐项重证。旧XOR候选池也按实际支持重新计算，无分配长度冒充支持数。2151构建/312公理完整验证通过；4,450点加线目标保留给后续P映射，不在本批宣称实现。


### D1 第三批b：点加外层工作区复用

Deutsch按§23将外层子程序接到已证明的P列表，以首轮固定数据视图表示并证明与idleBorrow相等。现有子程序偏移、数学分支和公开数值规格保持；完整门列支持由Divide下界与P包含关系上界共同证明为4450。未借记录带，未改变求逆或Montgomery算术；总D1较原基线少1768线。本批完整验证2151/312通过，无外部代码、新公理、测试或证明限制放宽。

Q1循环接入由本项目组合已证一位轮完成。共享交换位零值随循环断言传递，其余逐轮减法记录用frame保持，旧交换位尾部从支持表排除；没有借用D1之外的资源、扩展语义或放宽证明限制。计数和支持来自实际正逆程序，公开点加与求逆规格保持。


## K2 第一批：三角平方原语

按REWORK_PLAN §28，以二进制平方对称恒等式构造受控加法行，复用本库测量清掩码加减；新增原始Lean证明覆盖全测量记录、清理与逐线保持。129位和与Karatsuba整数恒等式为后续组合准备。本批未接入点加，未实现约减或引用未证预算为实际资源。


## K2 第二批：Karatsuba重组与伪Mersenne折叠

本项目依据§28的已审门列，组合第一批三角平方、原地加减、比较及受控常量算术；新增Lean证明处理高段中间回绕、129位和、三折叠数值界及q/b/f恢复。共享区的生命周期在各显式寄存器断言中体现。没有引入外部实现、新公理、测试、量子语义扩展或证明限制变更；点加接入留待第三批。


## K2 第三批：平方适配与既有点加组合

复用本仓库已证Karatsuba整数平方、三折叠约减及原地模减，构造计算—目标更新—前向清理的squareSub。固定P前缀切片与全局互异、完整工作区清理和逐线保持均为本批原始Lean组合证明；替换点加平方复制/模乘段，重证同程序资源与支持。未引入外部源码、框架、公理或测量逆执行。


## Q1交换位测量清理

基于本库kaliski_swap_from_r的布尔恒等式t=a∧¬r₀=a⊕a·r₀，将正轮交换临时位的CX/CCX清理替换为measureX及CZ+Z即时修正。相位抵消、精确状态与逐线保持为原始Lean证明，复用现有measureAndCorrect语义；逆轮重算不变。没有外部源码、CCZ或新语义。

### 改12受控模半倍

按REWORK_PLAN §30.4/30.5自有门列实现，复用本仓库C1常数加减、shiftRight/shiftLeft及比较器。奇偶/借位恢复的数学依据沿用ModHalf/ModDouble的规范模算术恒等式；新增控制false分支、全记录精确相位、frame与同程序支持/计数证明。未引入外部代码、CCZ或语义公理。

### 改12第一批：值走数学与单轮电路

本项目从既有Kaliski状态机投影u/v/k，以逐步等价复用原终止证明；有限域载荷函数按四分支显式定义，原始Lean证明其线性、逆及商/积关系。电路仅组合既有记录、测量清掩码加减、交换、移位和计数器；旧布局作为兼容视图，未触及r/s/out，尚未接入紧凑循环与点加。没有外部代码、新公理、语义扩展或证明限制变更。


### 改12载荷回放组合

§30.10按已审四分支门列组合既有C1受控模加减、受控半倍及SwapRegisters。新增SwapLow只证明规范输入的低位交换保持高位零。ReplayCell/ReplayLoop的规格、frame、支持及资源均来自实际前向门列；反回放不倒放测量。ReplayField把规范Nat运算连接到既有ValueReplay数学，未引入公理或新语义。比较scratch复用通过Valid包含关系陈述，整机具体映射交§29集成证明；2321仅为非空512轮正回放的实际支持，非整机资源。


### 改12紧凑循环与原地乘除

依据已审§29/30组合现有Kaliski值走与载荷回放，不采用论文经验轮数。ValueTrace把最终K与活动记录对齐；ValueBoundary以不触及线路的运行一致性证明消除幽灵out前提。DialogLayout具体复用原视图字段与零工作区，DialogSpec给完整安全分母乘除，DialogResources按同一门列的精确支持计3,126线。独立除法3,591,168/2,140,672、乘法3,328,000/1,878,016，均与设计一致；旧点加未接入，资源不变。无新增语法、公理、证明限额或测试。

## 改12第四批独立角落数学

Math/DialogPoint与DialogPointFlags由本项目证明，复用Math/PointInPlace中已有仿射分母分类及平移等价。新增H=−(C+C)的重复类保护、几何排除、输入/输出互斥和四类异或写回；不引入外部公理或群阶结论。此批没有电路替换或资源收益声明。


### 改12批④：原地乘除与六阶段点加集成

按已审§29/§30组合本仓库已证值走、dialog乘除、K2平方与C1算术；几何分母排除和四类写回使用PR74的DialogPoint/Flags。没有采用论文经验轮数或额外群阶前提。公开点加数值陈述逐字保持，门列改为一次D、一次U、平方与E；同程序资源7207866/4305594/3134，物理支持由显式池映射、置换与Nodup得出。全部测量记录下相位和旧分配工作位恢复；完整verify为2243构建/452公理，与PROOF_STATUS实际输出一致。§30.8可选优化未实施。


### §30.8 独立受控模加减测量清掩码

Deutsch 按已复审的 §30.8/§30.11 门列，复用本仓库 `eraseMask_eq_copy`、
`modAddCore` 与 `negRaw`，在现有两个模算术文件中组合完整规格、逐线保持、支持与资源证明。
掩码低位关系从完整寄存器读数和范围推出；减法在源恢复之前清 mask，保留 A≤p。
没有复制外部代码或新增抽象、公理、测试、语义扩展、证明限额调整。
仅新增独立 measuredControlledModAdd/Sub，旧入口及整机不变；资源为
5n−1/5n−1/5n+5 与 7n−1/7n−1/5n+6，均指同一门列。

本批在合入 `9bd65f9` 后完整运行 `scripts/verify.sh`，退出0：2,244项构建、468条公理实际输出；脚本入口、PROOF_STATUS 公理块与日志逐项一致。


## Exact Skywalk source and verification

The October 2, 2026 exact Skywalk point program is fully verified under the unchanged original all-valid-input `controlledPointAdd_spec`. It has 3,636,669 static Toffolis, 2,845,373 measurements and a proved static support upper bound of 2,994 distinct logical sites. This is not an independently proved peak-live/physical-qubit result. All 512 rounds and full carry propagation are retained. The complete remote build (3,475 jobs) and all 483 public entry-point axiom audits passed in 330 seconds (228 build, 102 audit). See [the exact Skywalk verification record](SKYWALK_EXACT_20261002.md); earlier numerical stages above remain historical. Matt Zweil and the challenge contributors are credited for the Skywalk construction. No sampled schedule, clipped carry window, new axiom, `sorry` or `native_decide` is used. The sub-1.5M target and unconnected fused-kernel budgets remain future work.


## Exact universal-width Skywalk update

The complete point program subsequently integrated the universally proved signed prefix schedule, preserving all 512 rounds and the unchanged public specification. It now has 3,505,085 static Toffolis, 2,713,789 measurements and support ≤2,994. Full pod verification passed 3,480 build jobs and 528 axiom checks in 294 seconds. The initial Skywalk checkpoint above remains historical. See [the exact width integration record](NARROW_SKYWALK_EXACT_20261002.md).

The next exact checkpoint integrates universally reduced integer routing and the independently proved retained-carry forward endpoint into the complete point program. It has 3,114,941 static Toffolis, 2,455,737 measurements, and support ≤2,994. All 674 public axiom queries passed with the protected specification unchanged. See [the retained forward record](RETAINED_FORWARD_EXACT_20261003.md).

The independent retained inverse endpoint and its 512-cell replay subsequently passed complete point integration. The verified full circuit now has 2,856,381 static Toffolis, 2,197,177 measurements and support ≤2,994. All 727 public axiom queries passed with the protected specification unchanged. See [the complete retained arithmetic record](RETAINED_BOTH_EXACT_20261003.md).

## Exact compact-guard integration, 2026-10-03

The complete controlled point circuit now uses the independently proved compact forward and inverse raw-word guards, while retaining every 256-bit field value and all 512 rounds. It passed 3,518 build jobs and all 749 public axiom queries at 2,853,821 static Toffolis, 2,194,105 measurements and support ≤2,994. The protected specification is byte-identical. The final 122s check used a cached 2s build and 120s audit; the preceding 95s compilation and failed legacy-import audit are retained separately. See [the full record](COMPACT_GUARD_EXACT_20261003.md).


## 2026-10-04 精确 measured streamed-square 接入

源码88aad07以三个128/129位子平方的生成/折叠/独立清理替换当前 Step4，保留精确512轮 Skywalk乘除和全部点分类。mapped literal/互补读取、全源归一化/恢复、借位测量清理、方向帧及完整控制平方组合由本项目在 Lean 中实现和证明；复用仓库的 signed-square、Gidney进位/测量修正、secp256k1模数与点加接口。旧无测量 streamed 版本保留作历史比较，未作为当前成本替代值。

incumbent的 streamed `with_square` 架构用于结构参考；没有移入近似折叠窗口或截断。Rust的10K输入诊断只用于早期候选筛选，不是正确性证明或最终Lean资源证据。最终完整电路正确性、相位、控制和工作清理，以及同一程序的T/M与支持上界，均经CPU pod的完整build和931项公开传递公理白名单检查；480源哈希匹配。Step4为99,902T/99,382M/≤1,297分配位置，完整点加为2,743,618T/2,083,894M/≤2,579静态支持。详细证据见[接入记录](MEASURED_STREAMED_SQUARE_20261004.md)。


## 2026-10-04 精确 fused output recovery

源码9ea2e58把当前 Step6 改为受控规范反射、经典offset+1修正与精确y修正。结构参考 Layr-Labs/ecdsafail-challenge 的公开默认 HEAD3161bd2：`coord_rsub` 的经典+1和补码反减、共享进位及工作复用。该来源的截断折叠/高位比较窗口与乘法/y恢复边界融合未移入此实现，恢复成本全部保留在本阶段。Lean程序、规范边界、零输入、所有测量记录相位/控制/清理与资源证明在本仓库实现；常量核复用已证 MeasuredCanonicalMod。阶段为2,301T/2,301M/≤1,036分配位置；完整点加为2,740,035T/2,081,591M/≤2,579支持。完整CPU pod验证165s build +135s audit，971公开查询、487哈希匹配，无新公理或近似。


## Exact penultimate swap specialization, 2026-10-06

Source checkpoint `f83e51c` removes one equal-word S-selector/swap window from each selected field replay. The forward endpoint duplication follows from the original 512-round trace. The inverse starts from the corresponding duplicate pair. Complete-state equality, arbitrary independent measurement records, wire containment and resource propagation are proved by the new Penultimate modules using existing exact arithmetic. No incumbent gate code was copied for this change.

`CertifiedProgram` supplies a kernel-checked opaque subtype with a proof that its value is the original program. Its aliases avoid expanding a large gate list during proof checking. They introduce no instruction, assumption or axiom. The raw emitted programs and protected point specifications remain unchanged except for the proved removed gate windows. Generic record padding preserves the original default-false behavior for short measurement lists.

The full CPU build and all 1,493 public axiom queries passed. All 855 source hashes matched. Resource counts refer to the complete selected point circuit in the original signed-basis/measurement-record model. This work does not add a full quantum-channel semantics bridge. See [checkpoint evidence](EXACT_PENULTIMATE_SWAP_20261006.md).

## 双 submission 整合（PR #80 / #81）

ValueWalk 来源为 `d9ae6002dc99b0d38fdeeb9a4961820470a0abcb`，Skywalk 来源为 `eca407ae621ac22ff9c48ec00103d37ead3b57fb`，共同基线为 `9699678f71cab2bcd84e75fb8def64f01c482e6c`。整合历史保留两条父提交。`ValueWalkPoint*` 的程序与证明取自前者，改名后与后者共存；共用分类、布局、基础库与唯一成本模型。未复制另一套 Framework。

原 #81 验证脚本的构建集合未覆盖三个审计导入模块，在缺失其 `.olean` 时会先构建成功、随后导入失败。本次将 `TerminalMappedFieldPoolRestore`、`NearestLiftMath`、`FusedInversePackedProof` 纳入显式构建。历史 source-manifest 证明当时源码哈希，不保证任何新检出的缓存已预先包含这些模块。当前复现以仓库脚本及本次 PROOF_STATUS 记录为准。

短源三角平方的三个 `ShortTriangularSquare*` 模块同样取自 #81，在 `Arithmetic.ShortTriangular` 命名空间保留完整平方、独立清理、精确计数与支持证明；复用原有 `SquareFrame`，避免改变 ValueWalk 的原平方。
