# 证明范围与结论边界

本说明的公开正确性陈述在 **`9699678` 加 2026-10-02 精确测量回放接入** 上保持，完整构建与公理白名单检查已在用户提供的 CPU pod 上通过。当前完整精确 Skywalk 电路已接入 measured streamed-square，并接入 fused output recovery，最新完整验证源码为 `a782d1342f771ee880398572cfb971eeaf7dcf44`；已接入 known-output native inverse，结果与完整验证见[最新检查点](EXACT_KNOWN_OUTPUT_NATIVE_20261008.md)；[输出恢复记录](EXACT_OUTPUT_RECOVERY_20261004.md)保留历史阶段；[早期精确优化记录](EXACT_OPTIMIZATION_20261002.md)保留历史阶段。后续实现应重新核对本页与源码；本页不把设计预算视为证明，也不增加任何电路或定理。

**当前成果是在仓库定义的带符号基态、固定测量记录执行模型中，证明受控经典常量点加的功能、相位恢复和工作区清理，并证明同一程序的静态资源计数。没有在本仓库中把该结论提升为完整量子态或量子信道正确性。**

## 1. 执行模型具体表示什么

[Syntax.lean](../ECDSAAdd/Framework/Syntax.lean) 定义：

- `BasisState := Wire → Bool`，每根线路持有一个布尔值。
- `State` 只有 `phase : Bool` 与 `basis : BasisState`；phase记录正负号，不是任意复数相位或振幅。
- `Program := List Instr`。指令为X、CX、CCX及`measureX`；即时修正列表只包含Z、CZ。

[Semantics.lean](../ECDSAAdd/Framework/Semantics.lean) 中的`run`接收程序、`List Bool`测量记录和初始State，确定地产生一个State。`measureAndCorrect`先以测量结果与清零前的目标位更新符号，再把目标位置false，最后执行该结果对应的修正列表。修正只影响符号。

测量结果选择本次即时修正；该指令表没有“按测量结果跳转到另一段算术”的控制流。记录不足时补false，多余记录忽略；`run_take`与`run_append`分别证明记录截取及顺序组合的行为。这里没有抽样过程，也没有给某条记录赋概率。

仓库沿用“monomial语义”这一名称，但含义必须限定：**固定记录下，每个输入基态被映到一个带符号基态。** 清零测量可能让不同输入映到同一基态，因此一般分支不保证单射，不能据此称它为严格monomial矩阵或可逆幺正算子。

## 2. Triple承诺什么

[Hoare.lean](../ECDSAAdd/Framework/Hoare.lean) 的定义是：

```lean
def Triple (P : BasisState → Prop) (c : Program) (Q : BasisState → Prop) : Prop :=
  ∀ (s : State) (m : List Bool), P s.basis →
    (run c m s).phase = s.phase ∧ Q (run c m s).basis
```

这同时要求：对所有满足P的初始基态、两个初始符号及所有测量记录，执行后符号精确等于初始符号，且Q成立。它不是抽查若干输入，也不是只验证某个测量结果。相位恢复必须在证明中建立，不能由“使用即时修正”这一语法事实推出。

`Triple.seq`负责程序组合与记录分段；`Triple.conseq`负责前后置条件推导；`Triple.frame`在给定外部依赖条件后保持额外断言。一般Triple只保证写在Q中的性质，并不自动保证所有未列输入保持或所有辅助位清零。程序支持之外的逐线保持另由[Cost.lean](../ECDSAAdd/Framework/Cost.lean)中的`run_preserves_outside`提供。

`Holds`规定寄存器断言的含义：单线读Bool，线路列表按小端读Nat，`PointReg`读取有限点标志和坐标。无穷远点编码为有限点标志false且两个坐标均零；有限点编码使用坐标在`[0,p)`中的规范代表。

## 3. 公开受控点加规格及前提

[ControlledPointAddSpec.lean](../ECDSAAdd/Arithmetic/ControlledPointAddSpec.lean) 的公开定理如下：

```lean
theorem controlledPointAdd_spec (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R C : Point) :
    {{ L.control=b,L.point=R,L.work=0 }} controlledPointAdd L C
    {{ L.control=b,L.point=(if b then R+C else R),L.work=0 }}
```

“全输入静态证明”指这个定理全称量化的输入，且仍受以下前提约束：

|条件或参数|精确含义|
|---|---|
|`L.Widths`|布局满足规定的位宽、列表长度等结构条件，并非任意长度寄存器。|
|`L.wires.Nodup`|公开布局线路互异；不能未经重证就将两个字段别名为同一线路。|
|`R C : Point`|对象属于Mathlib中的该曲线点类型；有限点带合法性证明，不是任意256位坐标对。|
|`L.point=R`|物理位串必须满足上述规范编码。|
|`L.work=0`|公开工作区初始全零，后置恢复为零；不是任意脏辅助位规格。|
|`b`|控制输入为任意Bool，输出保持该值；这本身不是叠加控制态的定理。|
|`C`|作为程序构造参数传入的经典常量点；定理对任意C成立，但程序不从量子点寄存器读取C。|

`L.work`的定义见[ControlledPointPorts.lean](../ECDSAAdd/Arithmetic/ControlledPointPorts.lean)。[PointDialogIntegration.lean](../ECDSAAdd/Arithmetic/PointDialogIntegration.lean) 的`pointDialogFinite_full_spec`把内部工作区结果接回公共布局，包括通过逐线保持恢复未被本实现使用的旧分配字段。

“公开规格逐字不变”是版本比较结论：比较的是定理陈述；不表示程序定义、证明体、布局内部映射或资源数字不变。单靠陈述相同，也不能替代对新证明和新程序的验证。

## 4. 哪些角落已被覆盖

公开定理没有额外要求R、C非零，也没有排除R=C或R=−C：

- `b=false`：点保持R，控制保持false，工作区归零，符号恢复。对于有限C，程序仍是固定指令表；输出恒等不等于静态门数为零。
- `C=0`：`controlledPointAdd`在构造时就是空程序，见[ControlledPointLayout.lean](../ECDSAAdd/Arithmetic/ControlledPointLayout.lean)。
- R为无穷远、R=C、R=−C：由同一公开定理覆盖；不是留给调用者避开的输入。
- 内部额外例外H=−(C+C)及H与旧角落重合、C=−C等情况：由[DialogPoint.lean](../ECDSAAdd/Math/DialogPoint.lean)与[DialogPointFlags.lean](../ECDSAAdd/Math/DialogPointFlags.lean)的分类、平移重算与写回定理处理。分类/写回中的C≠0前提只用于有限常量分支，公共入口另处理C=0。

普通路径所需的非零分母由分类推出，没有加到最终公开点加规格上。中间模算术、求逆或乘除定理各自的规范范围、非零等前提仍然存在，应读取相应定理，不能因最终点加全覆盖而删掉这些条件。

## 5. 从基态结论不能直接跳到哪些结论

当前`State`、`run`、`Triple`未定义复振幅向量、密度矩阵、测量概率或Kraus算子，也未证明它们与当前执行函数之间的语义桥。因此本页不声称：

- 对任意叠加态、与外部系统纠缠的态已证明量子信道等价；
- 测量记录的概率分布、分支归一化或总概率保持已证明；
- 基态清零断言已经证明实际量子系统中的辅助位解纠缠；
- 一般含测量程序可直接倒放，或所有分支都实现幺正变换。

全记录符号恢复是本模型中的实质结论，但“对所有基态成立”不自动补齐上述物理语义定义与桥接证明。这里也不提供完整Shor算法、量子傅里叶变换、成功概率、密钥恢复或硬件运行的正确性结论。

## 6. 资源数字的范围

[Cost.lean](../ECDSAAdd/Framework/Cost.lean)与[Syntax.lean](../ECDSAAdd/Framework/Syntax.lean)定义：

|量|仓库计数|
|---|---|
|`toffoliCount`|指令表中的CCX个数；不是T门数，也不是时深。|
|`measurementCount`|`measureX`指令个数；不按某个记录的概率加权。|
|`wires`|所有指令触及线路的静态并集，包含测量的两条可能修正列表。|
|`qubitCount`|上述并集的基数；不是最大编号、字段分配总长、峰值活跃位数或物理纠错量子位数。|

有限C的同程序精确计数见[ControlledPointResources.lean](../ECDSAAdd/Arithmetic/ControlledPointResources.lean)的`controlledPointAdd_finite_resources`；C=0另见`controlledPointAdd_zero_resources`。两者不能混作一条不分条件的计数声明。数值总表由[PROOF_STATUS.md](PROOF_STATUS.md)和[README](../README.md)维护，历史阶段与未实现预算应分别标注。

这些计数没有给出硬件映射、噪声、容错开销、魔法态制备、经典反馈时延或墙钟时间。少某一类操作不自动意味着总运行成本下降；跨论文比较必须另核它们的规格与计数口径。

## 7. 验证证据与信任边界

[scripts/verify.sh](../scripts/verify.sh)执行`lake --wfail build`，随后对脚本列出的公开入口运行`#print axioms`并检查传递依赖白名单：`propext`、`Classical.choice`、`Quot.sound`。这不是零公理结论，也不是对环境里全部声明进行审计；入口名单与实际输出应一起看。

Lean检查的是所写定义和假设下的命题。模型选择、规格是否表达了想要的问题，以及物理语义是否匹配，仍须阅读和审阅；编译通过本身不能消除规格遗漏。构建、公理日志、CI状态和独立审阅是不同证据，不应互相冒充。工具链版本在[lean-toolchain](../lean-toolchain)，依赖锁定在[lake-manifest.json](../lake-manifest.json)。

[BitcoinPrimes.lean](../ECDSAAdd/Math/BitcoinPrimes.lean)中有`p_prime`及相应域实例的证明；[BitcoinCurve.lean](../ECDSAAdd/Math/BitcoinCurve.lean)定义曲线和常量`order`。**定义一个名为order的数不等于证明它是曲线群阶。** 本页不把该常量定义当作群阶、生成元阶或离散对数算法正确性证明。

对外可引用的简述是：**“在所定义的带符号基态和测量记录模型中，Lean证明了满足布局与编码前提的所有输入的受控经典常量点加功能、符号恢复、工作区清理及同程序静态资源计数；完整量子态语义提升不在本证明范围内。”**
