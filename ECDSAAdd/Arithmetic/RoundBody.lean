import ECDSAAdd.Arithmetic.RoundFrame
import ECDSAAdd.Math.KaliskiRound

namespace ECDSAAdd.Arithmetic

/-- 数据寄存器承载 u/v/r/s，其他字段均为本轮清零的工作区；k 由独立计数器处理。 -/
def roundDataValues (z : KState) : RoundField → Nat
  | .u => z.u | .v => z.v | .r => z.r | .s => z.s | _ => 0

private theorem data_updates (z : KState) (X : Nat) :
    Function.update (roundDataValues z) .u X = roundDataValues {z with u:=X} ∧
    Function.update (roundDataValues z) .r X = roundDataValues {z with r:=X} ∧
    Function.update (roundDataValues z) .s X = roundDataValues {z with s:=X} := by
  refine ⟨?_,?_,?_⟩ <;> funext f <;> cases f <;> rfl

def swapDataPairs (L : RoundDataLayout) (c : Wire) : Program :=
  swapRegisters c L.u L.v ++ swapRegisters c L.r L.s

private theorem swap_pairs_frame (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (z : KState) (base : BasisState) :
    Triple (RoundFrame L (roundDataValues z) base) (swapDataPairs L c)
      (RoundFrame L (roundDataValues (kaliskiSwap (base c) z)) base) := by
  let v := roundDataValues z
  let v1 := Function.update (Function.update v .u (if base c then v .v else v .u))
    .v (if base c then v .u else v .v)
  have h1 := RoundFrame.swap L c hnd v base .u .v (by decide)
  have h2 := RoundFrame.swap L c hnd v1 base .r .s (by decide)
  have he : Function.update (Function.update v1 .r (if base c then v1 .s else v1 .r))
      .s (if base c then v1 .r else v1 .s) = roundDataValues (kaliskiSwap (base c) z) := by
    cases hc : base c <;> funext f <;> cases f <;> simp [v1,v,roundDataValues,kaliskiSwap,hc]
  have h := h1.seq h2
  simpa only [swapDataPairs, RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.r,RoundDataLayout.s,he] using h

/-- 四分支统一为交换、减/加、移位和交换回来；控制值不改变门或测量的顺序。 -/
def kaliskiBodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapDataPairs L swap ++ inplaceArithmetic L .u .v subtract true ++
  inplaceArithmetic L .r .s subtract false ++ shiftRight active L.u ++ shiftLeft active L.s ++
  swapDataPairs L swap

/-- 逆体使用前向加减与反向交换网络；不逆序执行任何测量指令。 -/
def kaliskiUnbodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapDataPairs L swap ++ shiftRight active L.s ++ shiftLeft active L.u ++
  inplaceArithmetic L .r .s subtract true ++ inplaceArithmetic L .u .v subtract false ++
  swapDataPairs L swap

private theorem control_nodup (L : RoundDataLayout) (cs : List Wire)
    (hnd : (cs++L.wires).Nodup) (c : Wire) (hc : c∈cs) : (c::L.wires).Nodup := by
  have h := List.nodup_append'.mp hnd
  exact List.nodup_cons.mpr ⟨List.disjoint_left.mp h.2.2 hc,h.2.1⟩

/-- 统一正体的布局级证明；范围条件正好来自 I1 的整数不变量。 -/
theorem kaliskiBodyProgram_frame (L : RoundDataLayout) (active swap subtract : Wire)
    (hnd : ([active,swap,subtract]++L.wires).Nodup) (hpos : 0<L.width)
    (z : KState) (base : BasisState)
    (hU : (kaliskiSwap (base swap) z).u<2^L.width)
    (hsub : (if base subtract then (kaliskiSwap (base swap) z).v else 0)≤(kaliskiSwap (base swap) z).u)
    (hR : (kaliskiSwap (base swap) z).r+(if base subtract then (kaliskiSwap (base swap) z).s else 0)<2^L.width)
    (heven : base active=true → ((kaliskiSwap (base swap) z).u-
      (if base subtract then (kaliskiSwap (base swap) z).v else 0))%2=0)
    (hfit : base active=true → 2*(kaliskiSwap (base swap) z).s<2^L.width) :
    Triple (RoundFrame L (roundDataValues z) base) (kaliskiBodyProgram L active swap subtract)
      (RoundFrame L (roundDataValues (kaliskiBody (base active) (base swap,base subtract) z)) base) := by
  have ha := control_nodup L [active,swap,subtract] hnd active (by simp)
  have hs := control_nodup L [active,swap,subtract] hnd swap (by simp)
  have hd := control_nodup L [active,swap,subtract] hnd subtract (by simp)
  let t := kaliskiSwap (base swap) z
  let U := t.u-(if base subtract then t.v else 0)
  let R := t.r+(if base subtract then t.s else 0)
  change t.u<2^L.width at hU
  change (if base subtract then t.v else 0)≤t.u at hsub
  change R<2^L.width at hR
  let z1 : KState := {t with u:=U}
  let z2 : KState := {z1 with r:=R}
  let z3 : KState := {z2 with u:=if base active then U/2 else U}
  let z4 : KState := {z3 with s:=if base active then 2*t.s else t.s}
  have hdiff : (t.u+2^L.width-(if base subtract then t.v else 0))%2^L.width=U := by
    rw [show t.u+2^L.width-(if base subtract then t.v else 0)=U+2^L.width by dsimp [U]; omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (show U<2^L.width by dsimp [U]; omega)]
  have h0 := swap_pairs_frame L swap hs z base
  have h1 : Triple (RoundFrame L (roundDataValues t) base) (inplaceArithmetic L .u .v subtract true)
      (RoundFrame L (roundDataValues z1) base) := by
    have h := RoundFrame.inplace L subtract hd hpos (roundDataValues t) base .u .v
      (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl true
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues t) .u
      ((t.u+2^L.width-(if base subtract then t.v else 0))%2^L.width)) base) at h
    rw [hdiff,(data_updates t U).1] at h
    exact h
  have h2 : Triple (RoundFrame L (roundDataValues z1) base) (inplaceArithmetic L .r .s subtract false)
      (RoundFrame L (roundDataValues z2) base) := by
    have h := RoundFrame.inplace L subtract hd hpos (roundDataValues z1) base .r .s
      (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl false
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z1) .r (R%2^L.width)) base) at h
    rw [Nat.mod_eq_of_lt hR,(data_updates z1 R).2.1] at h
    exact h
  have h3 : Triple (RoundFrame L (roundDataValues z2) base) (shiftRight active L.u)
      (RoundFrame L (roundDataValues z3) base) := by
    have h := RoundFrame.shift_right L active ha (roundDataValues z2) base .u heven
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z2) .u (if base active then U/2 else U)) base) at h
    rw [(data_updates z2 (if base active then U/2 else U)).1] at h
    exact h
  have h4 : Triple (RoundFrame L (roundDataValues z3) base) (shiftLeft active L.s)
      (RoundFrame L (roundDataValues z4) base) := by
    have h := RoundFrame.shift_left L active ha (roundDataValues z3) base .s hfit
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z3) .s (if base active then 2*t.s else t.s)) base) at h
    rw [(data_updates z3 (if base active then 2*t.s else t.s)).2.2] at h
    exact h
  have h5 := swap_pairs_frame L swap hs z4 base
  have he : roundDataValues (kaliskiSwap (base swap) z4) =
      roundDataValues (kaliskiBody (base active) (base swap,base subtract) z) := by
    cases hc : base swap <;> funext f <;> cases f <;>
      simp [roundDataValues,kaliskiBody,kaliskiSwap,z4,z3,z2,z1,U,R,t,hc]
  rw [he] at h5
  simpa only [kaliskiBodyProgram,List.append_assoc] using h0.seq (h1.seq (h2.seq (h3.seq (h4.seq h5))))

/-- 对应逆体恢复正体前的四份数据与工作区，始终读保存的分支位。 -/
theorem kaliskiUnbodyProgram_frame (L : RoundDataLayout) (active swap subtract : Wire)
    (hnd : ([active,swap,subtract]++L.wires).Nodup) (hpos : 0<L.width)
    (z : KState) (base : BasisState)
    (hU : (kaliskiSwap (base swap) z).u<2^L.width)
    (hsub : (if base subtract then (kaliskiSwap (base swap) z).v else 0)≤(kaliskiSwap (base swap) z).u)
    (hR : (kaliskiSwap (base swap) z).r+(if base subtract then (kaliskiSwap (base swap) z).s else 0)<2^L.width)
    (heven : base active=true → ((kaliskiSwap (base swap) z).u-
      (if base subtract then (kaliskiSwap (base swap) z).v else 0))%2=0) :
    Triple (RoundFrame L (roundDataValues (kaliskiBody (base active) (base swap,base subtract) z)) base)
      (kaliskiUnbodyProgram L active swap subtract) (RoundFrame L (roundDataValues z) base) := by
  have ha := control_nodup L [active,swap,subtract] hnd active (by simp)
  have hs := control_nodup L [active,swap,subtract] hnd swap (by simp)
  have hd := control_nodup L [active,swap,subtract] hnd subtract (by simp)
  let t := kaliskiSwap (base swap) z
  let U := t.u-(if base subtract then t.v else 0)
  let R := t.r+(if base subtract then t.s else 0)
  change t.u<2^L.width at hU
  change (if base subtract then t.v else 0)≤t.u at hsub
  change R<2^L.width at hR
  let z0 : KState :=
    { t with
      u := if base active then U/2 else U
      r := R
      s := if base active then 2*t.s else t.s }
  let z1 : KState := {z0 with s:=t.s}
  let z2 : KState := {z1 with u:=U}
  let z3 : KState := {z2 with r:=t.r}
  have hsHalf : (if base active then (if base active then 2*t.s else t.s)/2
      else (if base active then 2*t.s else t.s))=t.s := by
    cases base active <;> simp
  have huDouble : (if base active then 2*(if base active then U/2 else U)
      else (if base active then U/2 else U))=U := by
    cases hc : base active
    · rfl
    · have he := heven hc
      simp only [if_true]
      dsimp [U,t] at *
      omega
  have hswap : roundDataValues (kaliskiSwap (base swap)
      (kaliskiBody (base active) (base swap,base subtract) z)) = roundDataValues z0 := by
    cases hc : base swap <;> funext f <;> cases f <;>
      simp [roundDataValues,kaliskiBody,kaliskiSwap,z0,U,R,t,hc]
  have h0 := swap_pairs_frame L swap hs (kaliskiBody (base active) (base swap,base subtract) z) base
  rw [hswap] at h0
  have h1 : Triple (RoundFrame L (roundDataValues z0) base) (shiftRight active L.s)
      (RoundFrame L (roundDataValues z1) base) := by
    have he : base active=true → roundDataValues z0 .s%2=0 := by
      intro hc
      simp [roundDataValues,z0,hc]
    have h := RoundFrame.shift_right L active ha (roundDataValues z0) base .s he
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z0) .s
      (if base active then (if base active then 2*t.s else t.s)/2 else (if base active then 2*t.s else t.s))) base) at h
    rw [hsHalf,(data_updates z0 t.s).2.2] at h
    exact h
  have h2 : Triple (RoundFrame L (roundDataValues z1) base) (shiftLeft active L.u)
      (RoundFrame L (roundDataValues z2) base) := by
    have hf : base active=true → 2*roundDataValues z1 .u<2^L.width := by
      intro hc
      change 2*(if base active then U/2 else U)<2^L.width
      rw [hc,if_pos rfl]
      have hu : U≤t.u := Nat.sub_le _ _
      have hhalf : 2*(U/2)≤U := by omega
      omega
    have h := RoundFrame.shift_left L active ha (roundDataValues z1) base .u hf
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z1) .u
      (if base active then 2*(if base active then U/2 else U) else (if base active then U/2 else U))) base) at h
    rw [huDouble,(data_updates z1 U).1] at h
    exact h
  have hdiff : (R+2^L.width-(if base subtract then t.s else 0))%2^L.width=t.r := by
    rw [show R+2^L.width-(if base subtract then t.s else 0)=t.r+2^L.width by dsimp [R]; omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (show t.r<2^L.width by dsimp [R] at hR; omega)]
  have h3 : Triple (RoundFrame L (roundDataValues z2) base) (inplaceArithmetic L .r .s subtract true)
      (RoundFrame L (roundDataValues z3) base) := by
    have h := RoundFrame.inplace L subtract hd hpos (roundDataValues z2) base .r .s
      (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl true
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z2) .r
      ((R+2^L.width-(if base subtract then t.s else 0))%2^L.width)) base) at h
    rw [hdiff,(data_updates z2 t.r).2.1] at h
    exact h
  have hsum : (U+(if base subtract then t.v else 0))%2^L.width=t.u := by
    rw [show U+(if base subtract then t.v else 0)=t.u from Nat.sub_add_cancel hsub,
      Nat.mod_eq_of_lt hU]
  have h4 : Triple (RoundFrame L (roundDataValues z3) base) (inplaceArithmetic L .u .v subtract false)
      (RoundFrame L (roundDataValues t) base) := by
    have h := RoundFrame.inplace L subtract hd hpos (roundDataValues z3) base .u .v
      (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl false
    change Triple _ _ (RoundFrame L (Function.update (roundDataValues z3) .u
      ((U+(if base subtract then t.v else 0))%2^L.width)) base) at h
    rw [hsum,(data_updates z3 t.u).1] at h
    exact h
  have h5 := swap_pairs_frame L swap hs t base
  have he : kaliskiSwap (base swap) t=z := by cases hc : base swap <;> simp [t,kaliskiSwap,hc]
  rw [he] at h5
  simpa only [kaliskiUnbodyProgram,List.append_assoc] using h0.seq (h1.seq (h2.seq (h3.seq (h4.seq h5))))

end ECDSAAdd.Arithmetic
