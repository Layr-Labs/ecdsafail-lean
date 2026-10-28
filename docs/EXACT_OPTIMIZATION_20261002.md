# 2026-10-02 精确优化与远程验证

Latest complete verified checkpoint: **2,853,821 static Toffolis / 2,194,105 measurements / ≤2,994 static logical sites**. Full pod library check and all 749 public axiom queries passed in 122s (2s cached incremental build +120s audit). The preceding complete compilation took 95s; its legacy-import audit failure is recorded separately. See [the complete compact-guard integration record](COMPACT_GUARD_EXACT_20261003.md). Earlier results below are historical.

本阶段只接纳精确优化。公开 `controlledPointAdd_spec` 的源文件与 `9699678` 基线逐字相同，仍覆盖所有合法点、控制位、规范编码和任意测量记录，并保持控制、符号与零工作区。模型范围见 [PROOF_SCOPE](PROOF_SCOPE.md)。

## 已接入：回放掩码测量清理

`replayCell` 与 `replayUncell` 改用仓库已有完整证明的 `measuredControlledModSub` 与 `measuredControlledModAdd`。来源掩码完成所有算术和比较用途后，通过测量及即时 CZ 修正清零，省去原来的 CCX 复制清理。来源不变、掩码关系和任意测量记录下的符号恢复由已有规格与 frame 定理保证。顺序组合使用 `Triple.seq`，没有假设两个测量次数不同的程序对相同记录逐步相等。

每条 256 位回放方向的 512 次调用各省 131,072 个 Toffoli，并增加同数测量。全部公开资源定理沿同一程序重证，实际线路支持保持。

| 程序 | 基线 Toffoli / 测量 | 当前 Toffoli / 测量 | 静态支持线 |
| --- | ---: | ---: | ---: |
| `dialogDivide` | 3,591,168 / 2,140,672 | 3,460,096 / 2,271,744 | 3,126 |
| `dialogMultiply` | 3,328,000 / 1,878,016 | 3,196,928 / 2,009,088 | 3,126 |
| `controlledPointAdd`，有限常量（回放接入后） | 7,207,866 / 4,305,594 | 6,945,722 / 4,567,738 | 3,134 |
| `controlledPointAdd`，有限常量（当前，短来源平方接入后） | 7,207,866 / 4,305,594 | **6,880,186 / 4,502,202** | **3,134** |

整机净省 262,144 个 Toffoli（约 3.64%），不引入输入筛选、窗口截断、随机正确性或 nonce 搜索。额外测量不是近似，所述清理对每条测量记录都精确恢复模型中的符号。

## 已接入：短来源平方行

平方行只复制真实来源位，不再复制或测量清理显式零 padding。完整目标宽度、全进位传播、规范输入范围与任意测量记录的相位恢复均保留。每方向行计数为 `3k−1`，三角平方总计为 `(m−1)*(3m−2)/2`。整机各省 65,536 个 Toffoli 和测量；当前相对基线净省 327,680 个 Toffoli（4.55%）。

短来源平方的完整远程验证在 `/root/ecdsadd-exact/square-stage2-pod` 通过：2,245 构建任务、476 项公开公理检查（475 个不同声明），只允许既有三项白名单公理。耗时 219 秒，分为构建 142 秒及公理审计 77 秒。11 个实现/验证脚本文件与提交候选 SHA-256 一致，公开点加规格逐字未变。本次相同依赖缓存下的增量验证时间不包含首次环境准备。

## 回放接入验证证据

- 用户提供的 pod：`ssh root@216.243.220.86 -p 14114`，32 CPU、64,000,000,000 字节 cgroup 内存上限。
- 远程项目：`/root/ecdsadd-exact/ECDSAAdd`。本阶段没有在本地执行 Lean。
- 工具链：Lean `v4.28.0`，Mathlib `fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42`。
- 基线确认与接入后均执行 `scripts/verify.sh`，两次退出状态均为 0。
- 接入后 `lake --wfail build` 完成 2,244 项构建。脚本的 468 项公开入口检查（467 个不同声明）及传递依赖均通过白名单，只允许 `propext`、`Classical.choice`、`Quot.sound`。
- 8 个修改的 Lean 文件与远程验证副本 SHA-256 一致。未添加 `sorry`、新公理或 `native_decide`。
- 本地证据位于工作区 `outputs/lean-exact-campaign-20261002/`，远程日志为 `/root/ecdsadd-exact/logs/stage1-verify.log`，退出状态文件为 `stage1.exit`。

## 参考与后续候选

参考 ECDSA.Fail Q×T 轨道的 Skywalk。初始快照为 `1c185d1`，运行中更新至 `cc530e2`（sky14）。更新主要是近似折叠窗口的误差交换和平方门流的局部 SAT 重写。本阶段不接入任何近似窗口或只在选定测试支持上正确的构造。

精确短来源加减法、终态常量保护的 Clifford 移位、保守整数宽度界与相邻交换融合已准备独立候选。短加减原语及平方行已完成整机接入与完整远程验证。保护移位原语仅通过独立检查，尚未接入整机。其他候选的编译修复和接入验证仍在进行。候选源码单独保存在工作区 `outputs/lean-exact-campaign-20261002/candidates/`，不纳入本次已证整机资源，也不计入已完成的节省。


## Complete exact Skywalk stage

The October 2, 2026 exact Skywalk point program is fully verified under the unchanged original all-valid-input `controlledPointAdd_spec`. It has 3,636,669 static Toffolis, 2,845,373 measurements and a proved static support upper bound of 2,994 distinct logical sites. This is not an independently proved peak-live/physical-qubit result. All 512 rounds and full carry propagation are retained. The complete remote build (3,475 jobs) and all 483 public entry-point axiom audits passed in 330 seconds (228 build, 102 audit). See [the exact Skywalk verification record](SKYWALK_EXACT_20261002.md); earlier numerical stages above remain historical. Matt Zweil and the challenge contributors are credited for the Skywalk construction. No sampled schedule, clipped carry window, new axiom, `sorry` or `native_decide` is used. The sub-1.5M target and unconnected fused-kernel budgets remain future work.
