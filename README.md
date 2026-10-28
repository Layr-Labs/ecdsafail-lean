# ecdsa.fail Lean — Lean 4 Point-Addition Challenge

> **Goal.** Build and formally verify in Lean 4 the cheapest quantum circuit that performs in-place controlled point addition on **secp256k1**, scored by the product of **Toffoli upper bound × static qubit upper bound** (`score = qubits * toffoli`, lower is better).
>
> **Challenge:** 受控点加的形式化验证 challenge 见 [docs/CHALLENGE.md](docs/CHALLENGE.md)（与 Eigen Labs 合作，Apache 2.0）。

## Benchmark Contract

- **Track**: `lean` (`schemaVersion: 2`)
- **Editable path**: `ECDSAAdd/Submission/Entrant` (entry module: `ECDSAAdd/Submission/Entrant/Main.lean` in namespace `ECDSAAdd.Entrant`)
- **Protected contract**: `ECDSAAdd/Challenge/Contract.lean` (`ECDSAAdd.Challenge.Certificate`)
- **Protected kernel judge**: `ECDSAAdd/Judge/Main.lean` + `scripts/challenge/judge.lean` + `scripts/challenge/gate.py`
- **Score file**: `scripts/score.json`
- **Scoring formula**:

  $$\text{score} = \text{bounds.qubits} \times \text{bounds.toffoli}$$

  where `bounds.toffoli` is the certified uniform upper bound on `ECDSAAdd.toffoliCount (entry C)` and `bounds.qubits` is the certified uniform upper bound on `ECDSAAdd.Challenge.qubits (entry C)` (`(ioWires ∪ wires (entry C)).card`) over all classical secp256k1 addends `C : Point` (including infinity). Lower is better (`direction: "-"`).

### Baseline Numbers

| Entry | Toffoli ≤ | Measurements ≤ | Qubits ≤ | Syntax slots ≤ | Score (`Q × T` ≤) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Skywalk` (normalized, default baseline) | 2,217,386 | 1,557,928 | 1,899 | 47,000,000 | 4,210,816,014 |
| `ValueWalk` (normalized) | 6,286,806 | 3,779,274 | 3,134 | 61,000,000 | 19,702,850,004 |

### Solver Workflow (`--track lean`)

```bash
yukon setup --track lean
yukon run --track lean
yukon submit --track lean
```

`yukon switch lean` updates local Yukon track selection only and preserves your Git branch, `HEAD`, index, and worktree.

---

证明语义、输入前提及未覆盖的结论统一见[证明范围说明](docs/PROOF_SCOPE.md)。

在 Lean 中证明 Bitcoin/secp256k1 点加程序的 monomial 行为与资源计数。

## 两个 submission，共享基础库

两个入口同时可导入，均使用唯一的 `Framework.Syntax`、`Framework.Semantics` 和 `Framework.Cost`，以及共同的 secp256k1、布局和基础算术库。没有另一套成本模型或语义副本。

| Submission 文件 | 有限经典加数：Toffoli | 测量指令 | 静态支持线路 |
| --- | ---: | ---: | ---: |
| [ValueWalk](ECDSAAdd/Submissions/ValueWalk.lean)（PR #80） | 6,286,806 | 3,779,274 | =3,134 |
| [Skywalk](ECDSAAdd/Submissions/Skywalk.lean)（PR #81） | 2,217,386 | 1,557,928 | ≤1,899 |

每个文件集中给出 `program`、成本常量、`correctness`、`gate_count`、`measurement_count`、`qubit_count` 和 `zero_resources`。`gateCount` 沿用本项目的 Toffoli 口径，不是所有 Clifford 指令的总数。Skywalk 使用 `qubitBound` 明确声明上界，ValueWalk 的 `qubitCount` 是精确基数。两者对 C=O 都发出空程序、三项资源均为零。

```lean
import ECDSAAdd.Submissions
-- ECDSAAdd.Submissions.ValueWalk.correctness
-- ECDSAAdd.Submissions.Skywalk.correctness
```

两项正确性定理覆盖所有合法输入点、两种控制值、任意初始相位及测量记录，恢复全部工作位；资源定理作用于对应的同一 `program`。原 `controlledPointAdd` 兼容入口仍指向 Skywalk。ValueWalk 保留已证位宽收窄和原回放/平方实现，不将 Skywalk 的局部改动叠加进其电路。共享输入分类、角落处理和布局；仅分开两条不同点加路径的组合证明。详见[整合设计](docs/REWORK_PLAN.md#dual-submissions)与[当前证明状态](docs/PROOF_STATUS.md)。

验证入口为 `bash scripts/verify.sh`。脚本明确构建所有额外审计导入，包括 `TerminalMappedFieldPoolRestore`、`NearestLiftMath` 和 `FusedInversePackedProof`，不依赖它们偶然残留的编译产物。整合后的验证结果见 PROOF_STATUS；下方旧 checkpoint 的日志仅为该历史源码的证据。

## Skywalk 历史 checkpoint 与阶段分解

The pre-integration Skywalk checkpoint was verified at source commit `a782d13`. The native inverse now recovers its carry bits from a known output sum supplied by the existing forward copy. The reusable receiver replaces 252 Toffolis in each of Stages 2 and 5, preserving all measurement records, phase and workspace restoration. The unrestricted native inverse retains its original behavior. The exact 512-round Skywalk construction, streamed square, recovery and protected specifications remain in use. The proof covers every valid input point, classical addend, both controls, arbitrary incoming phase, independent measurement records and complete work restoration under the original monomial semantics. See [proof scope](docs/PROOF_SCOPE.md).

For a finite addend, the full circuit uses **2,217,386 static Toffolis / 1,557,928 measurement instructions / ≤1,899 static logical sites**. The infinity addend emits an empty circuit. Against the original baseline of 7,207,866 static Toffolis / 4,305,594 measurement instructions / 3,134 static logical sites, the full circuit saves **4,990,480 Toffolis (69.24%)**, **2,747,666 measurement instructions (63.82%)**, and lowers the reported static-site bound by **1,235 sites (39.41%)**. The Q percentage compares static support bounds; it does not measure a reduction in peak-live or physical qubits. Relative to verified `092e87c`, the full circuit saves 504 Toffolis, with measurements and the Q ceiling unchanged. The support/allocation ceiling includes residents and is not a separately measured exact peak-live count. The Stage 2/5 targets ≤1,297 Q and <600,000 Toffolis remain open.

The CPU-pod full build passed 3,988 jobs, and the separate audit passed 1,616 public transitive axiom queries (1,615 distinct declarations). All 891 selected committed Lean source hashes, plus four build/verifier metadata files, matched before and after verification. The successful cached incremental check took 17s build + 241s audit = 258s (4m18s). Earlier attempts remain separate: 601s failed on kernel memory, 397s stopped an obsolete transfer check after its replacement passed, and 94s failed on a stale resource subtotal. Queue and verifier setup were zero. Source preparation and transfer are excluded. The exact whitelist is `propext`, `Classical.choice` and `Quot.sound`. Correctness is formal, with no approximations. See [checkpoint evidence](docs/EXACT_KNOWN_OUTPUT_NATIVE_20261008.md) and the [source manifest](docs/verification/known-output-native-20261008/source-manifest.json), [build log](docs/verification/known-output-native-20261008/build.log), [axiom audit](docs/verification/known-output-native-20261008/axioms.log), and [timing receipt](docs/verification/known-output-native-20261008/timing.json).

### Six-stage decomposition (Skywalk checkpoint)

Comparison reference: our previously instrumented 1,174-Q Q×T incumbent, source [`799153a`](https://github.com/ecdsafail/ecdsafail-challenge/tree/799153aac444491dcac273ad552ea8473d2a63dd), with 9,024 evaluator inputs. This intentionally retains the reference used in our earlier comparison. The incumbent columns below are from that same pinned source and are not labeled as the latest leaderboard result. See the [saved stage profile](docs/comparison/incumbent-799153a/profile.json).

| Stage | Lean logical Q ceiling | Lean static Toffolis | Lean measurements | Reference peak-live Q | Reference static Toffolis | Reference average executed Toffolis | Static Toffoli gap (Lean − reference) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1. Coordinate differences | ≤1,036 | 2,046 | 2,046 | 769 | 510 | 510.0 | 1,536 |
| 2. Skywalk-GCD division | ≤1,899 | 1,053,750 | 724,536 | 1,174 | 464,759 | 450,215.5 | 588,991 |
| 3. Prepare X workspace | ≤1,036 | 1,023 | 1,023 | 1,174 | 326 | 316.6 | 697 |
| 4. Measured streamed modular square | ≤1,297 | 99,902 | 99,382 | 1,174 | 41,150 | 40,583.0 | 58,752 |
| 5. Forward multiplication | ≤1,899 | 1,054,260 | 724,536 | 1,174 | 468,649 | 452,182.6 | 585,611 |
| 6. Recover output | ≤1,036 | 2,301 | 2,301 | 1,174 | 326 | 316.6 | 1,975 |
| Six-stage subtotal | ≤1,899 | 2,213,282 | 1,553,824 | 1,174 | 975,720 | 944,124.3 | 1,237,562 |
| Additional input/corner classification | ≤1,034 | 4,104 | 4,104 | — | — | — | — |
| Complete controlled finite-addend point addition | **≤1,899** | **2,217,386** | **1,557,928** | **1,174** | **975,720** | **944,124.3** | **1,241,666** |

Lean Q is a certified static-support/allocation ceiling including resident sites. Reference Q is the peak-live allocator count within each stage, including resources retained from earlier stages. The columns therefore have different Q evidence. Lean static Toffolis should be compared with reference static Toffolis; the reference average-executed column separately reports its input-sampled average count. Both Toffoli columns count CCX/Toffoli operations, not elementary T gates.

The reference evaluator does not provide an equivalent all-valid-input corner-classification block. The dashes do not assert zero cost for equivalent coverage. Its stopping, width and comparison settings also include benchmark-tuned approximations, while the Lean checkpoint retains exact functionality on every valid input in the stated proof model. The table establishes resource gaps, not equivalent verification coverage.

Q 是支持/分配证书给出的保守存活上界，不是精确 peak-live 测量。Step 4 的证书含 521 个常驻点/控制/分类位置与 776 个工作位置。完整电路 Q 上界仍由乘除阶段决定。表中采用六阶段示意图的概念顺序；源码先做平方减法，再加 `3x_A`，两者在域中可交换。

Step 4 对照前一已证低宽版本 `d477a67`：749,338 →99,902 T，省 649,436 T（86.67%），保持 ≤1,297-site 证书；完整点加相应从 3,393,054 降至 2,743,618 T。较早的 signed-row 版本仍是另一空间/门数取舍：Step 4 82,101 T /2,865 schedule-peak Q，完整点加 2,725,817 T /≤2,994 静态位置。当前完整版本比该历史完整电路少508,431 T；这些独立检查点的资源不能相加。

Step 6 将取负与 `x_A` 修正合并：受控规范反射 `p−1−X` 后加经典 `x_A+1 mod p`，并精确修正 y。常量加法仍为每段1,023 T，但共享池从1,030位置缩到515位置。Stage6由5,884降至2,301 T（省60.89%），Q证书由≤1,550降至≤1,036；没有把恢复成本转移到乘法阶段。此全点检查点相对88aad07省3,583 T与2,303次测量。公开受控点加规格保持，全部合法点、控制/相位/工作清理均经完整验证。

新路径把控制放在子平方的输入掩码中，读取隐式常量/互补位，并保留精确输出方向帧。三个 128/129 位子平方依次生成、折叠、独立清理；38 个精确模加、四个全字归一化/恢复与所有测量相位/工作清理均已接入并证明。未反转含测量的门列，未采用概率窗口、截断或近似。旧 unitary streamed 控制包装作为历史实现保留，未用于当前 `pointDialogSquare`。

| 范围 | 当前状态 | 代码入口 |
| --- | --- | --- |
| Bitcoin 数学基础 | 已证明 p 的素性、群与 G 的相关性质、完整 affine 群律规格；没有群阶证明 | [Math](ECDSAAdd/Math) |
| 程序与语义 | 已实现 X/CX/CCX、测量及即时 Z/CZ 修正、monomial 执行和静态资源计数 | [Framework](ECDSAAdd/Framework) |
| Hoare 规格 | 已实现寄存器断言与程序语法糖，证明 seq/conseq/frame | [Hoare.lean](ECDSAAdd/Framework/Hoare.lean) |
| AND 测量反计算 | 已证明完整状态恢复，以及 1 Toffoli、1 次测量、3 根静态线路 | [And.lean](ECDSAAdd/Circuit/And.lean) |
| M2 加减法基础 | 已证明任意位宽加减法与任意初值输出 XOR 接口、同程序前向清理；输入、相位和工作位恢复 | [Layout.lean](ECDSAAdd/Arithmetic/Layout.lean) |
| 模 p 加减 | 已证明保留输入、任意初值输出 XOR、全部工作位清零，以及同程序精确资源公式 | [FieldAddSub.lean](ECDSAAdd/Arithmetic/FieldAddSub.lean) |
| 模乘 | 已证明两段Montgomery的五个适配器，fieldMul使用标准模积XOR，工作区1,827位 | [FieldMultiply.lean](ECDSAAdd/Arithmetic/FieldMultiply.lean) |
| 改 2 C1 原地模加减 | 已证明普通/受控四接口的 Triple、frame、清理及资源；已供 Montgomery 适配器复用 | [ModInPlaceSubtract.lean](ECDSAAdd/Arithmetic/ModInPlaceSubtract.lean) |
| 改 2 C2 半倍 | 无控制半倍的 Triple/frame/资源保留；旧Horner电路已由Montgomery替换，旧文件已清理 | [ModUnaryResources.lean](ECDSAAdd/Arithmetic/ModUnaryResources.lean) |
| 改 6a 准备/恢复 | 已证明P/Q与五个适配器的Triple、逐线保持、精确资源；已接入fieldMul，原地点加改接已实现 | [MontPQ.lean](ECDSAAdd/Arithmetic/MontPQ.lean) · [MontResources.lean](ECDSAAdd/Arithmetic/MontResources.lean) |
| EEA 求逆数学 | 已证明 Kaliski 不变量、2n 轮终止、范围、固定减半与逆元等式；不是电路证明 | [KaliskiInverse.lean](ECDSAAdd/Math/KaliskiInverse.lean) |
| EEA 电路原语 | 已证明 CSWAP、带偶数/无溢出前提的左右移位、10 位受控增减与清理及精确资源 | [Shift.lean](ECDSAAdd/Arithmetic/Shift.lean) · [Counter.lean](ECDSAAdd/Arithmetic/Counter.lean) |
| EEA 单轮与逆轮 | 已证明数据/计数/done 更新、两位分支记录、逆轮恢复与清理、同程序精确资源 | [RoundSpec.lean](ECDSAAdd/Arithmetic/RoundSpec.lean) |
| EEA 固定循环与反计算 | 已证明两个 512 轮阶段、规范化取负、XOR 输出及恢复已初始化输入；共享计数线路和全部记录线计入资源 | [InverseLoopSpec.lean](ECDSAAdd/Arithmetic/InverseLoopSpec.lean) · [InverseLoopResources.lean](ECDSAAdd/Arithmetic/InverseLoopResources.lean) |
| 完整求逆电路 | 已证明外部 256 位非零输入的域逆元、XOR 输出、装载/卸载、相位/清理和同程序精确资源及契约实例 | [InverseSpec.lean](ECDSAAdd/Arithmetic/InverseSpec.lean) · [InverseResources.lean](ECDSAAdd/Arithmetic/InverseResources.lean) |
| M3 候选计算 | 已证明全部标志取值下的安全候选、清理和同程序 Toffoli/测量数；分支标志原语单独证明 | [PointCandidateSpec.lean](ECDSAAdd/Arithmetic/PointCandidateSpec.lean) · [PointCandidateResources.lean](ECDSAAdd/Arithmetic/PointCandidateResources.lean) |
| 完整点加电路 | 已证明经典常量 C、任意合法输入 R 的完整点加 XOR、零输出规格及同程序精确资源 | [PointAddSpec.lean](ECDSAAdd/Arithmetic/PointAddSpec.lean) · [PointAddResources.lean](ECDSAAdd/Arithmetic/PointAddResources.lean) |
| 受控原地点加 | 已证明控制保持、全部点情形、临时点/工作区清零及同程序精确资源 | [ControlledPointAddSpec.lean](ECDSAAdd/Arithmetic/ControlledPointAddSpec.lean) · [ControlledPointResources.lean](ECDSAAdd/Arithmetic/ControlledPointResources.lean) |
| 原地加减与比较器原语 | 已证明原地加/减（n−1 Toffoli、n−1 测量、3n 线）、受控常数/寄存器加减、Gidney 比较器（n Toffoli）；已由求逆第二阶段复用 | [InPlaceAdder.lean](ECDSAAdd/Arithmetic/InPlaceAdder.lean) · [Compare.lean](ECDSAAdd/Arithmetic/Compare.lean) |
| 回放正逆组合 | 已证明 secp256k1 规范载荷上单格及循环的双向恢复；电路组合对任意测量记录恢复相位、寄存器断言和零工作区 | [ReplayRoundTrip.lean](ECDSAAdd/Arithmetic/ReplayRoundTrip.lean) |

每次创建或更新 PR 前，逐项核对本节与实际源码、公开定理和验证结果；状态变化时在同一 PR 更新 README。后续计划不计入已实现范围。

n 位加法和减法均使用 n 个 Toffoli、n 次测量；非空加法与减法均使用 4n+1 根静态线路。用 n+1 位加法保留完整结果时，资源为 n+1 个 Toffoli、n+1 次测量、4n+5 根线路。n 位常量模数的模加减各用 5n+4 个 Toffoli、4(n+1) 次测量、8n+9 根线路；secp256k1 实例分别为 1284、1028、2057。当前fieldMul使用379,424个Toffoli、379,424次测量和2,596根实际线路。全部模乘调用已统一为Montgomery适配器；旧Horner电路与适配器已删除。模乘空间为 O(n)，未声称资源最优。每项计数都针对规格中的同一个程序，详见 [证明状态](docs/PROOF_STATUS.md)。

I2 的 w 位受控移位使用 max(w−1,0) 个 Toffoli、零测量；w≥2 时静态线路为 w+1，否则为零。10 位计数器按模 1024 增减，使用 20 个 Toffoli、20 次测量、41 根静态线路；结果移入空寄存器并清空旧寄存器，控制为假时数值不变但角色仍交换。

I3 正轮与逆轮各使用 12w+31 个 Toffoli、6w+28 次测量；w≥2 时精确静态线路数为 7w+48。w=257 时分别为 3115、1570、1847。这是单轮成本，不能写成完整逆元成本；轮内共享工作区为 O(w)，只保留两位分支记录，计数器两份银行的角色按固定轮号交换。

I4 固定执行512轮Kaliski正向循环，取负得到N，再用十位量子计数K查表和一段Montgomery缩放得到逆元；使用结果后显式恢复缩放、清N并执行512轮Kaliski恢复。两次查表/清表及交换在每个缩放方向精确计入154,372 Toffoli/测量；518位缩放历史借自原轮y/zero低4位/carry，1054位共享工作区在使用逆元前已清零。完整 `inverseLoop` 使用 3,500,551 个 Toffoli、1,918,471 次测量、2,645 根实际静态线路；内部模数前提为q%16=15且q<2^256，外部secp256k1规格不变。详见[证明状态](docs/PROOF_STATUS.md#i4固定循环第二阶段与反计算)。

改 1 的公开接口直接列寄存器值：减半为 `data=X, counter.x=K, work=0 → data=(halveMod q)^[K] X, counter.x=K, work=0`，恢复方向相反。求逆准备段 `inversePrepare_spec` 的后置条件明确为 `middle.r=((X : ZMod q)⁻¹).val, compactBorrow=0`，另保留 `InverseHistory` 中的第一阶段数据、计数与记录；`inverseRestore_spec` 要求保留这些历史并归还逆元，然后恢复初始数据、清零全部工作区。完整源码陈述见 [公开寄存器接口](docs/PROOF_STATUS.md#改-1-的公开寄存器接口) 与 [准备/恢复接口](docs/PROOF_STATUS.md#改-1-的准备与恢复接口)。

I5 的 `fieldInverse` 在 I4 内核前后添加 CX/X 装载与卸载，Toffoli 和测量数保持 3,500,551 / 1,918,471，完整静态线路为 2,901。外部输入增加 256 根线路；内核的 257 位输出被拆成 256 位公开输出与一根工作高位，后者由逆元范围证明为零。

M3 的 `pointCandidateCompute` 计算六次模减、三次模乘和一次求逆，非普通分支将除数设为 1。`pointCandidateClear` 按依赖逆序再次执行这些前向 XOR 模块；每段分别使用 4,646,783 个 Toffoli、3,062,911 次测量。两段都已证明输入坐标与普通分支标志保持，共享池归零；清理段还恢复所有候选寄存器为零。乘法、求逆与减法直接连接调用方寄存器，工作区分别映射到同一池的旧分配视图；求逆分配视图仍为5,699位，但门列实际仅触及其中2,900位。布局分配数为 9,813；实际池支持为2,617位，完整电路排除dx/dy/delta/yg四根填充最高位及池中的29根旧out线。

M3 完整 `pointAddOut` 对有限经典常量使用 9,295,106 个 Toffoli、6,126,846 次测量、6,727 根实际静态线路。`pointAddOut_support` 证明门列支持集恰好等于 `L.usedWires.toFinset`，再由全局互异条件得到基数；这不是最大同时存活线数。C=O 时构造期选择点复制分支：0 个 Toffoli、0 次测量、1,026 根实际线路（513 个 CX）。普通分支所需横坐标不等由相等检测标志推出，不向完整点加的调用者增加几何前提。空间为 O(n+N)，不声称资源最优。

历史精确 Skywalk 检查点（2026-10-02）的 M3 受控原地 `controlledPointAdd` 对有限 C 使用 3,636,669 个 Toffoli、2,845,373 次测量、实际静态线路上界2,994。一次原地除法和一次原地乘法沿已证512轮精确Skywalk记录回放，专用平方前后受控复制并清理；斜率直接存于当前y，不另分配。输入分类与输出重算恢复七个标志，覆盖O、互逆点、倍点、C=−C、H=−(C+C)与控制false，重复H由旧角落处理。C=O在构造期为空程序，三项资源均为零。`pointDialogFinite_small_wires` 与全局互异证明给出实际支持上界，公共布局仍分配9,817位，未用工作位也恢复零。独立XOR点加接口继续保留。

基础层原语（重做计划 §1）：n 位原地加法 `addInPlace` 与减法 `subInPlace` 各用 n−1 个 Toffoli、n−1 次测量、3n 根线路（先擦进位再写和位，最高位不算进位）；受控常数加减不增加 Toffoli，受控寄存器加减另加两次 n 位受控复制；Gidney 比较器 `compareLt` / `compareLtConst` 用 n 个 Toffoli（受控 +1）、n 次测量、3n+2 根线路（受控版本为 3n+3）。求逆第二阶段已复用常数加减与受控比较器；其它原语供后续改动组合。

§30.8 的独立测量清掩码包装 `measuredControlledModAdd/Sub` 已证明完整 Triple、目标外逐线保持及同程序精确支持/资源；前提与原受控模加减一致，包括 `A≤p`。n>0 时，加法资源为 `(5n−1,5n−1,5n+5)`，减法为 `(7n−1,7n−1,5n+6)`，依次为 Toffoli、测量及实际支持线。n=256 时分别为 `1279/1279/1285` 和 `1791/1791/1286`。这两个入口已于 2026-10-02 接入回放和整机，该历史阶段点加为 6,880,186 / 4,502,202 / 3,134；历史精确 Skywalk 检查点为 3,636,669 / 2,845,373 / 静态支持上界2,994；本分支当前值见上方 Current status。见[证明状态](docs/PROOF_STATUS.md#measured-controlled-mod)。

## 优化进度与下一步计划

历史阶段记录：本节旧实现与其资源保留用于追溯，不表示当前公共入口仍调用该实现；当前值以上方 Current status 为准。未实现选项只作为预算，不能算入当前值。

改 2 C1 已实现普通/受控原地模加减的完整 Triple、目标外 frame 与同程序精确资源，入口为 `ModInPlaceWrappers.lean` 和 `ModInPlaceSubtract.lean`。源/目标宽 n+1，允许 A≤p、Z<p、0<p<2^n；工作区初末全零。四项 Toffoli/测量/实际线路分别为普通加 `(4n−1,4n−1,4n+4)`、普通减 `(6n−1,6n−1,4n+4)`、受控加 `(6n−1,4n−1,5n+5)`、受控减 `(8n−1,6n−1,5n+6)`（n>0）。C2 阶段曾证明无控制半倍与 Horner 内核（后者现已替换，旧文件已清理）。n=256 时，mulInto 为 523,776 Toffoli / 392,704 测量 / 1,540 线，mulClear 为 655,104 / 524,032 / 1,542；输入保持、累加器由零得到乘积或由该乘积清回零，全部工作位和相位恢复。D 已证明三个适配器并替换域乘法；旧倍数链布局已删除，该阶段完整受控点加降至 32,347,957 Toffoli / 17,585,440 测量 / 9,718 根实际线路。

改 1、改 2、改 3、改 4、改 5 已计入 Current status；改6a五个适配器和fieldMul已实现，原地点加改接也已实现；改7方案1的查表和全部下游资源已验证。成本压缩按 [重做设计](docs/REWORK_PLAN.md) 分七项推进；目标数是按文档门列推导的预期值（标"研究预算"者未从已有门列推导），以实现后的 Lean 资源定理为准。依赖：先做基础层（原地加法器与原地模算术），改 1/2/4 只通过 Hoare triple 接口相互独立、可并行，改 5 可并行开发但集成依赖改 4，改 3 依赖改 1 与改 2。

| 项（除末行外均为历史阶段） | 内容 | 该阶段 Toffoli | 该阶段实际线路 | 负责 / 证据 |
| --- | --- | ---: | ---: | --- |
| 改 1（已实现） | 求逆第二阶段改为内部寄存器上的受控原地模减半与逆序加倍，XOR 接口不变 | 57,258,805（该阶段已证） | 74,024（共享池由模乘决定） | Deutsch |
| 改 2（已实现） | Horner 内核与 XOR/加/减适配器；调用次数不变 | 32,347,957（该阶段已证） | 9,718 | Lamport |
| 改 3（已实现） | 除法中心原地更新：2 次除法内含 2 个乘积，另加 3 个乘积；输出侧标志清理 | 14,998,618（改3阶段已证） | 6,218 实际支持（已证） | Deutsch |
| 改 4（已实现） | 计数活动比较与记录段直接调用 Gidney 比较器 | 56,083,253（该阶段已证） | 74,024 | Deutsch |
| 改 5（已实现） | Kaliski轮测量清零检测、原地受控加减；等常量检测同步 | 52,914,997（改 2 前阶段值） | 74,024 | Deutsch |
| 改 6a（已实现） | 标准表示四位窗口Montgomery，全部模乘接入 | 11,800,058（改6a阶段已证） | 6,218（已证） | Lamport；6b设计留档 |
| 改 7（方案1已实现，改8前阶段） | 14/14单迭代查表；测量清理仍为可选设计 | 11,669,498（已证） | 6,218（已证） | [实现与设计](docs/REWORK_PLAN.md#18-改-7四位单迭代查表与可选测量清理方案1已实现)；测量4,525,818 |
| 改 8（已实现，改10前阶段） | 变量窗口测量清掩码 | 11,001,338（已证） | 6,218（已证） | [实现](docs/REWORK_PLAN.md#opt8-measured-mask)；测量5,193,978 |
| 改 10（改10阶段） | Kaliski两处测量清掩码 | 9,948,666（已证） | 6,218（已证） | [实现](docs/REWORK_PLAN.md#opt10-kaliski)；测量6,246,650 |
| 改 11（已实现） | 量子计数查表与单段Montgomery缩放 | 8,946,186（已证） | 6,218（已证） | [实现](docs/REWORK_PLAN.md#opt11-counted-scaling)；测量5,772,554；基于改10 |
| K2（已实现，交换位测量清理前阶段） | 专用Karatsuba平方与三折叠约减 | 8,814,658（已证） | 3,939（实际支持） | [实现](docs/REWORK_PLAN.md#k2-special-square)；测量5,645,122 |
| 改12（历史整机基线） | 值走记录回放、原地乘除与六阶段点加 | 7,207,866（已证） | 3,134（实际支持） | [实现](docs/REWORK_PLAN.md#dialog-value-walk-design)；测量4,305,594 |
| 精确回放接入（2026-10-02，历史阶段） | 两方向使用测量掩码清理 | 6,945,722（已证） | 3,134（实际支持） | [验证记录](docs/EXACT_OPTIMIZATION_20261002.md)；测量4,567,738 |
| 精确短来源平方（2026-10-02，历史阶段） | 完整进位；省去零 padding 复制与清理 | 6,880,186（已证） | 3,134（实际支持） | [验证记录](docs/EXACT_OPTIMIZATION_20261002.md)；测量4,502,202 |
| 精确Skywalk整机（2026-10-02，历史已证） | 全512轮、完整进位、共享池及控制/角落/相位清理 | 3,636,669（已证） | ≤2,994（静态支持上界） | [验证记录](docs/SKYWALK_EXACT_20261002.md)；测量2,845,373 |

每项先提交设计 PR 描述（构造、逐步寄存器表、门数推导、证明义务、文件改动），复审确认后再写证明；公开定理陈述保持不变，只替换实现与资源数。

线路按实际门列支持计数。改 2 后共享池仍按求逆编号分配 5,699 位，模乘/模减/求逆的支持并集为 5,602 位；97 根旧 out 位没有门触及。该阶段受控点加的外部支持为4,116位，合计9,718；改3已进一步缩至6,218实际线，分配编号保持。

改 2 的构造与资源见 [实施设计](docs/REWORK_PLAN.md#12-改-2-实施设计历史阶段horner电路已被改6a替换)。C1/C2/D 阶段实现六个模算术原语、Horner 内核与三个适配器（以下为历史阶段值）；XOR 模乘为 1,178,880 Toffoli / 916,736 测量 / 1,799 线，加/减适配器分别为 1,179,903/917,759 与 1,180,415/918,271，均为 1,799 线。D阶段集成保留4次求逆与12次模乘，按改5后程序重算为32,347,957 Toffoli；当前改3已减少调用次数。受控半倍已在改12回放原语中实现，见§30.9。

改 4 首批计数比较器接入已实现，见 [实施说明 §13](docs/REWORK_PLAN.md#13-改-4-首批接入计数比较器已实现)：完整求逆省30,720 Toffoli/测量，当前资源已包含此收益；记录段直接受控比较也已实现，见 [§14](docs/REWORK_PLAN.md#14-改-4-后续记录段直接受控比较已实现)，每次求逆再省263,168 Toffoli/测量。

改 5 的历史阶段设计见 [§15](docs/REWORK_PLAN.md#15-改-5-实施设计测量清零检测与原地受控加减已实现)：原地替换零检测并接入 Kaliski 原地受控加减，单轮已证3,629 Toffoli/1,056测量/1,847线；该阶段受控点加52,914,997 Toffoli/31,848,736测量/74,024线。不包含改2/3收益；原求逆池编号保留，实际工作支持5,442线。

历史路径：改 3 的具体门列与寄存器表见 [§16](docs/REWORK_PLAN.md#16-改-3-实施设计除法中心的受控原地点加已实现)：总Triple、逐线保持、8,946,186 / 5,772,554及6,218线是改11时该路径的阶段值；当前公共入口已由改12替换。旧内部 `pointInPlaceFinite` 仍保留，其当前数值见证明状态索引。D兼容布局仍分配9,817位，未触及位保持零。

改3的八个数学引理已证明，见[证明状态](docs/PROOF_STATUS.md#改-3-数学原地更新与输出侧清理条件)：涵盖输出侧标志、普通分支域等式和第二除数为零时的例外斜率。历史除法批已完成完整规格、逐线保持与精确资源，见[除法证明状态](docs/PROOF_STATUS.md#改-3-除法保留求逆历史的受控累加)：加3,895,383 Toffoli / 2,309,207测量，减3,895,895 / 2,309,719，均6,210根实际支持线（历史批次值，非当前保留入口数值）。当前 `divideAdd/Sub` 及替代后的 `dialogDivide/Multiply` 分别见资源索引。原路径的证明记录见[完整证明](docs/PROOF_STATUS.md#改-3-原地点加本体与公开入口)。

## 每次交付的检查

每次创建或更新 PR 都逐项检查，并在 PR 描述里简述结果；可读性和设计必要性需要人工审阅，不能用构建通过代替。

- [ ] Human readable：公开定理直接表达前置条件、程序与结果；使用 `r = v`、命名布局、统一 `Nodup` 和中文说明。先展示零输出等常用形式，再提供组合所需的 XOR 形式；检查程序及测量语法是否容易读。
- [ ] Overdesign：每个新增类型、谓词、文件、工具都有当前用途；避免重复公开 API、全环境审计器和无需要的抽象。项目文档集中在 README、PROOF_STATUS、PROVENANCE；未实现的计划只放在 REWORK_PLAN（唯一来源，README 只留摘要表）。
- [ ] 状态真实：逐项对照 README Current status、实际源码、公开定理和验证结果；契约不写成实现，数学群律不写成点加电路证明。
- [ ] Lean 验证：固定工具链与依赖，运行 `lake --wfail build` 和选定公开定理的传递 `#print axioms` 白名单，仅允许 `propext`、`Classical.choice`、`Quot.sound`。不添加小 case 测试、Python 对照或真值表验证。
- [ ] 语义与清理：Triple 对任意初始相位及所有测量记录证明相位恢复、所需输入保持和工作位清零。即时 Z/CZ 修正不是自动正确；测量结果只能选择即时修正。清理必须有适用的不变量，不能直接反转带测量的程序。
- [ ] 同一条合法电路：正确性与 Toffoli、测量、qubit 定理指向同一具体程序；门的控制与目标满足互异要求，不含重复控制 CCX。线路数按完整程序及修正分支的实际支持集计算，不冒充最大同时存活数；披露空间复杂度，不声称未经证明的最优性。
- [ ] 范围与完整性：当前只做带符号基态分支模型，不加入量子态语义、桥或 Reference 树。最终点加必须覆盖无穷远、相反点和倍点等角落情形，C 是经典常量、R 是变量；模算术必要的位宽与取值范围前提仍应明确写出。一般测量分支不称为严格 monomial 矩阵，也不冒充完整量子态正确性。
- [ ] 可审阅证据与约定：PROOF_STATUS 保留可读陈述、证明含义、同程序资源及公理证据；频道和项目文档用中文，复制数学代码保留来源与提交说明。仓库维持 private、Apache 2.0，除非另有明确决定。

只有 Dirac 合并：在同一头提交上 CI 通过、独立复审通过、README 与代码一致，且无当前暂停。Lamport 与 Deutsch 不合并；Dirac 遇到需要人类决定的不确定事项，应 @runzhou-tao 并等回复。暂停及解除都以最新明确指令为准，不把已解除的暂停继续当作阻塞。

## 程序与规格

常用的零输出模加直接写成：

```lean
theorem fieldAdd_zero_spec (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width = 256)
    (X Y : Nat) (hX : X < p) (hY : Y < p) :
  {{ L.x = X, L.y = Y, L.out = 0, L.work = 0 }} fieldAdd L
  {{ L.x = X, L.y = Y, L.out = ((X+Y)%p), L.work = 0 }}
```

`fieldSub_zero_spec` 同样给出模 p 的差；组合证明需要时，`fieldAdd_spec` / `fieldSub_spec` 支持任意输出初值的 XOR 更新。

模乘也先使用零输出形式：

```lean
theorem fieldMul_zero_spec (L : MontLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (X Y : Nat) (hX : X < p) :
  {{ L.x = X, L.y = Y, L.out = 0, L.work = 0 }} fieldMul L
  {{ L.x = X, L.y = Y, L.out = ((X*Y)%p), L.work = 0 }}
```

`L.Widths` 要求 x、out 为257位、乘数 y 为256位，工作区为1,827位；全布局用一个 `Nodup` 要求互异。X 必须小于 p，Y 只受寄存器位宽限制，不必另加 `Y < p`。组合用 `fieldMul_spec` 将输出写为 `O ^^^ ((X*Y)%p)`。准备阶段保留两段Montgomery历史至输出更新后，再由恢复阶段清零全部工作位。


非零输入求逆的零输出接口：

```lean
theorem fieldInverse_spec (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (X : Nat) (hX0 : 0<X) (hX : X<p) :
  {{ L.x=X, L.out=0, L.work=0 }} fieldInverse L
  {{ L.x=X, L.out=((X : Fp)⁻¹).val, L.work=0 }}
```

`L.Widths` 列出外部 256 位输入/输出及 I4 内部位宽、512 对记录、十位计数器要求；`fieldInverse_xor_spec` 支持任意初值输出的 XOR 更新。`fieldInverse_contract` 证明这个具体程序满足 `inverseContract`，包括同一门列的三个资源数和线路包含关系。输入零明确排除。


```lean
def andComputeErase (a b anc : Wire) : Program := prog {
  CCX a b anc;
  if meas anc = 1 then CZ a b else skip
}

theorem andComputeErase_spec (a b anc : Wire) (hnd : [a, b, anc].Nodup) (A B : Bool) :
  {{ a = A, b = B, anc = false }} andComputeErase a b anc
  {{ a = A, b = B, anc = false }}
```

三线互异、辅助位初始为零时，数据与相位恢复；同一程序使用 1 个 Toffoli、1 次测量、3 根静态线路。测量结果只能选择即时 Z/CZ 修正，不能改变后续算术或测量流程。结论限于 monomial 语义模型：固定测量分支把每个基态映到单个带符号基态；一般测量分支不保证单射，因此不能称为严格的 monomial 矩阵。

```sh
lake exe cache get
scripts/verify.sh
```

验证包含 Lean 构建和公开定理的公理白名单检查，不包含测试。Lean 固定为 `v4.28.0`，Mathlib 固定为 `fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42`。

- [公开定理与证明状态](docs/PROOF_STATUS.md)
- [来源与复现](docs/PROVENANCE.md)

Apache License 2.0；来源声明见 [NOTICE](NOTICE)。

## 实施沿革与未实现选项

本节的“该批／第一批／第三批”均为历史交付时点；各阶段收益不累加到 Current status。标为取消、搁置、可选的数值均为未实现预算。仍保留模块的当前资源见[定理索引](docs/PROOF_STATUS.md#current-resource-index)。

改 6a 的具体门列设计见 [重做计划 §17](docs/REWORK_PLAN.md#montgomery-design)：包含标准表示转换与历史清理的 XOR适配器已证379,424 Toffoli / 379,424测量 / 2,596根实际线路，并已用于fieldMul；原地点加8,946,186/5,772,554/6,218是改11时的历史阶段值，已由当前改12公共入口替换。

改6a已实现数学、查表和共享工作区的准备/恢复电路 P/Q。`montP_spec` 得到标准模积并保留两段历史，`montQ_spec` 消费历史并清空全部工作位；两者各为189,712 Toffoli / 189,712测量 / 2,339根实际线路（工作区1,827位），对全部测量记录保持相位及工作区外线路。入口为Arithmetic/MontPQ.lean、MontResources.lean。五个适配器已证明，fieldMul使用XOR版；普通加/减为380,447/380,447和380,959/380,959，均2,596线；受控加/减为380,959/380,447和381,471/380,959，均2,597线。原地点加改接已实现。

改6b已按普通坐标评测口径搁置，历史设计账本见 [REWORK_PLAN §19](docs/REWORK_PLAN.md#19-改-6b全-montgomery-表示与边界成本设计待复审)。编码接口核心目标11,339,178 Toffoli；保留普通坐标的保守边界包装反而增至12,076,586，设计已复审但未实现，不计入当前已证值。

以上6b预算保留改7前的6a基线；接入14/14查表后的净账本由6b实现批重算。

改8受控加减的实现见 [REWORK_PLAN §20](docs/REWORK_PLAN.md#opt8-measured-mask)。`MeasuredMaskedAdder.lean` 的完整Triple、目标外逐线保持与同程序资源为 `(2W−1, 2W−1, 4W+1)`；W=261时521 Toffoli /521测量 /1045线。Montgomery变量窗口已接入，旧原语保留；接改7的14/14查表后，改8阶段完整点加已证11,001,338 Toffoli /5,193,978测量 /6,218线。

改10的Kaliski轮测量清掩码实现见[REWORK_PLAN §21](docs/REWORK_PLAN.md#opt10-kaliski)。该阶段两处替换曾证明完整点加9,948,666 Toffoli /6,246,650测量 /6,218线。

改11的[第二阶段替换实现](docs/REWORK_PLAN.md#opt11-counted-scaling)采用十位K查表与一段Montgomery准备/恢复，每次求逆已证少501,240 Toffoli和237,048次测量；与改10的单轮优化分开记账。完整点加再少1,002,480门和474,096次测量，线路保持6,218。

改11第一批已完成十位查表的完整Triple/frame、1,022/1,022计数与地址/scratch支持下界，以及计数因子的Montgomery缩放数学证明；四位查表规格保持。第二批已证明缩放准备/恢复的完整Triple、逐线保持、308,744/308,744计数，以及518位历史和1054位工作区的具体借用与互异。第三批已完成求逆、除法及两条点加路径接入；全记录相位/清理、最终资源与双向支持等式均已证明。

求逆工作区减线的 D1 联合设计见 [§23](docs/REWORK_PLAN.md#d1-compact-inverse)：保持受控常数点加公开规格，通过可逆原地取负与终态工作区复用，D1阶段已将有限 C 点加降至 8,918,440 Toffoli / 5,750,952 测量 / 4,450 线；均由同程序规格与支持等式证明，不含一位记录的额外收益。


D1第一批已证明Kaliski终态常量及r正偶、原地取负/恢复的双向Triple与精确资源（767/767与768/768），见[NegativeEven.lean](ECDSAAdd/Arithmetic/NegativeEven.lean)。第三批已完成工作区借用与求逆/点加接入，资源见Current status。

线数计划Q1的一位Kaliski历史见[设计与分批实现§24](docs/REWORK_PLAN.md#q1-one-bit-tape)：数学恢复引理及奇数模数的一位正逆轮已证明，初版每方向3,116 Toffoli /1,570测量 /1,847线（历史：测量清交换位前），通用两位记录规格保持。循环共享与下游接入已完成；净省511线、完整受控点加增加2,048个Toffoli，测量不变。
D1第二批已证明B/P工作区的分割、长度和互异，具体缩放/取负借用视图，以及终态常量清除/写回的双向规格；第三批已将这些视图接入求逆和点加。

D1第三批a已证明紧缩求逆、除法与资源传播；内部结果改写r，B在使用段归零，历史显式保留。外部求逆、除法及受控点加公开规格保持；第三批b已把外层改借P并证明4,450线；3a的5,731为中间阶段值。

Q1循环接入已完成：保留旧记录分配及通用两位轮规格，生产求逆循环共用第一根swap，仅保存512根subtract，未使用swap尾部仍保持零。正逆循环完整Triple、精确支持及下游资源均随同一门列重证；相比D1净省511线，完整受控点加增加2048个Toffoli，测量不变。见[§24](docs/REWORK_PLAN.md#q1-one-bit-tape)。

Q5的[完整mask复用审计](docs/REWORK_PLAN.md#q5-mask-audit)建议取消实现：单段可少261位，但受控适配器中段仍需独立零空间；现有原语的完整可构造方案仅净省19线，尚未实现，不计入Current status。
改12之前的Q6轮工作字共用的[容量复核§27](docs/REWORK_PLAN.md#q6-round-sharing)尚未实现：轮内共享不能与Q5的整机节省直接相加，当时受缩放历史和中段容量约束。这是旧布局的审计，不是改12后资源下界；后续分支不在本次代码基线内。

专用平方[实现§28](docs/REWORK_PLAN.md#k2-special-square)已接入：2217位借用前缀、275,129 Toffoli/测量，替换原380,959门平方块；完整点加少105,830 Toffoli与同数测量，实际支持仍3939线。Q5/W5已取消，该阶段P为2603位（当前改12池为2613位）。
W5的[五位窗口设计](docs/REWORK_PLAN.md#w5-window-design)按完整门列重算目标为8,867,944 Toffoli /5,698,408测量 /3,959线，全部待证明；净省52,544 T/M而非原0.3M粗估，保守映射增加20线。收益较小而数学及布局改动较大，建议取消W5实现；Current status不计此设计。

K2第一批已实现独立三角平方/清理原语及129位和的数学界，含完整寄存器规格、逐线保持、同程序计数和精确支持；每方向128位为32,385、129位为32,896 Toffoli/测量。第二批已证明Karatsuba整数重组及三折叠约减的计算/恢复：每方向132,223与4,574 Toffoli/测量，q/b/f记录保留到恢复。第三批已完成squareSub适配与点加接入：全部工作位恢复零，目标外逐线保持，K2阶段完整点加8,814,658/5,645,122/3,939由同一程序证明。

Q1交换位测量清理[§24.8](docs/REWORK_PLAN.md#q1-measured-swap)已实现：正轮以测量及CZ+Z修正清交换位，逆轮重算保留；该阶段完整点加8,813,634 Toffoli /5,646,146测量 /3,939线，较K2阶段少1,024门、多1,024测量。公开数值规格与实际支持不变；这是两类操作的取舍，不声称实际运行成本必然下降。

改12载荷回放[设计§30](docs/REWORK_PLAN.md#opt12-payload-replay)列出受控模半倍、四分支及512轮正逆回放门列；这些回放原语现已证明，完整乘除见§29.8，点加完整集成见§29.10。
改12原始批次的值走、原地乘除与六阶段接入已完整证明，见[§29](docs/REWORK_PLAN.md#dialog-value-walk-design)：7,207,866 Toffoli /4,305,594测量 /3,134实际支持线，与该批次基准设计零偏差；该批次未实施的回放测量清理已于 2026-10-02 接入，当前资源见上方索引。

改12回放原语第一批已实现受控模半倍：256位实例分别770/512和768/511 Toffoli/测量，具完整寄存器规格、逐线保持与精确支持（773/772线）。第一批只交独立原语；回放组合见下段，当前整机资源保持；见[§30.9](docs/REWORK_PLAN.md#opt12-controlled-unary)。

改12第一批已证明值走数学（投影、512轮终止继承、线性回放与乘除关系）及正逆单轮，单轮为1,832 Toffoli /1,057测量 /1,333实际支持线；[实现边界见§29.7](docs/REWORK_PLAN.md#297-第一批实现数学与值走单轮)。完整乘除见§29.8，六阶段接入与整机资源见§29.10。

改12载荷回放组合已证明：正/反格3,329/2,047和2,815/1,534 Toffoli/测量，512轮含活动比较为1,714,688/1,058,304与1,451,520/795,648。全记录规格保持K、两位记录及载荷外线路，工作区归零，并对应ValueReplay/Inverse域函数。正回放实际支持2,321线，反回放包含于同一支持；整机借用映射及资源已由§29.8/29.10接入，见[§30.10](docs/REWORK_PLAN.md#opt12-replay-implementation)。

改12第三批已证明完整原地乘除：除法3,591,168 Toffoli /2,140,672测量 /3,126实际支持线，乘法3,328,000 /1,878,016 /3,126。控制关闭时保持载荷，开启时只要求除数非零，全部工作位归零；512轮循环已消除旧out=0兼容要求。[紧凑映射与实现边界见§29.8](docs/REWORK_PLAN.md#opt12-dialog-implementation)。六阶段点加现已接入，整机资源见§29.10。

改12第四批的独立角落数学已证明：新增H=−(C+C)排除、两个分母非零、四类输入/输出互斥、输出标志重算及Nat/Bool异或写回；重复角落禁用条件显式处理C=−C等情形。该独立批次只增加数学接口，六阶段门列与整机资源随后由§29.10接入，见[§29.9](docs/REWORK_PLAN.md#opt12-dialog-corners)。
