import ECDSAAdd.Arithmetic.RoundSpec
import ECDSAAdd.Math.ValueWalk

namespace ECDSAAdd.Arithmetic

/-- 旧布局中的r/s/out不属于值走门列的支持，保持其原值。 -/
def valueBodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapRegisters swap L.u L.v ++ inplaceArithmetic L .u .v subtract true ++
  shiftRight active L.u ++ swapRegisters swap L.u L.v

def valueUnbodyProgram (L : RoundDataLayout) (active swap subtract : Wire) : Program :=
  swapRegisters swap L.u L.v ++ shiftLeft active L.u ++
  inplaceArithmetic L .u .v subtract false ++ swapRegisters swap L.u L.v

private def bodyValues (z : KState) (A S T : Bool) : KState :=
  let u := if S then z.v else z.u
  let v := if S then z.u else z.v
  let r := u - if T then v else 0
  let q := if A then r/2 else r
  { z with u := if S then v else q, v := if S then q else v }

private theorem controls_nodup (L : RoundDataLayout) (a s t : Wire)
    (hn : ([a,s,t]++L.wires).Nodup) (c : Wire) (hc : c∈[a,s,t]) :
    (c::L.wires).Nodup := by
  have h := List.nodup_append'.mp hn
  exact List.nodup_cons.mpr ⟨List.disjoint_left.mp h.2.2 hc,h.2.1⟩

private theorem swap_frame (L : RoundDataLayout) (c : Wire) (hn : (c::L.wires).Nodup)
    (z : KState) (base : BasisState) :
    Triple (RoundFrame L (roundDataValues z) base) (swapRegisters c L.u L.v)
      (RoundFrame L (roundDataValues { z with
        u := if base c then z.v else z.u, v := if base c then z.u else z.v }) base) := by
  have h := RoundFrame.swap L c hn (roundDataValues z) base .u .v (by decide)
  have he : Function.update (Function.update (roundDataValues z) .u
      (if base c then z.v else z.u)) .v (if base c then z.u else z.v) =
      roundDataValues {z with u := if base c then z.v else z.u, v := if base c then z.u else z.v} := by
    funext f; cases f <;> simp [roundDataValues]
  simpa only [RoundDataLayout.u,RoundDataLayout.v,roundDataValues,he] using h

private theorem body_frame (L : RoundDataLayout) (a s t : Wire)
    (hn : ([a,s,t]++L.wires).Nodup) (hw : 0<L.width) (z : KState) (base : BasisState)
    (hu : (if base s then z.v else z.u)<2^L.width)
    (hsub : (if base t then (if base s then z.u else z.v) else 0)≤
      (if base s then z.v else z.u))
    (heven : base a=true → ((if base s then z.v else z.u)-
      (if base t then (if base s then z.u else z.v) else 0))%2=0) :
    Triple (RoundFrame L (roundDataValues z) base) (valueBodyProgram L a s t)
      (RoundFrame L (roundDataValues (bodyValues z (base a) (base s) (base t))) base) := by
  have ha := controls_nodup L a s t hn a (by simp)
  have hs := controls_nodup L a s t hn s (by simp)
  have ht := controls_nodup L a s t hn t (by simp)
  let z1 : KState := {z with u := if base s then z.v else z.u, v := if base s then z.u else z.v}
  let U := z1.u - if base t then z1.v else 0
  let z2 : KState := {z1 with u := U}
  let z3 : KState := {z2 with u := if base a then U/2 else U}
  have h1 := swap_frame L s hs z base
  have h2 := RoundFrame.inplace L t ht hw (roundDataValues z1) base .u .v
    (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl true
  have hm : (z1.u+2^L.width-(if base t then z1.v else 0))%2^L.width=U := by
    rw [show z1.u+2^L.width-(if base t then z1.v else 0)=U+2^L.width by dsimp [U,z1]; omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (show U<2^L.width by dsimp [U,z1]; omega)]
  change Triple _ _ (RoundFrame L (Function.update (roundDataValues z1) .u
    ((z1.u+2^L.width-(if base t then z1.v else 0))%2^L.width)) base) at h2
  rw [hm] at h2
  have he2 : Function.update (roundDataValues z1) .u U=roundDataValues z2 := by
    funext f; cases f <;> simp [roundDataValues,z2]
  rw [he2] at h2
  have h3 := RoundFrame.shift_right L a ha (roundDataValues z2) base .u heven
  have he3 : Function.update (roundDataValues z2) .u (if base a then U/2 else U)=roundDataValues z3 := by
    funext f; cases f <;> simp [roundDataValues,z3]
  change Triple _ _ (RoundFrame L (Function.update (roundDataValues z2) .u
    (if base a then U/2 else U)) base) at h3
  rw [he3] at h3
  have h4 := swap_frame L s hs z3 base
  have h := ((h1.seq h2).seq h3).seq h4
  have hout : {z3 with u := if base s then z3.v else z3.u, v := if base s then z3.u else z3.v}=bodyValues z (base a) (base s) (base t) := by
    cases hS : base s <;> simp [z3,z2,z1,U,bodyValues,hS]
  simpa only [valueBodyProgram,hout] using h

private theorem unbody_frame (L : RoundDataLayout) (a s t : Wire)
    (hn : ([a,s,t]++L.wires).Nodup) (hw : 0<L.width) (z : KState) (base : BasisState)
    (hu : (if base s then z.v else z.u)<2^L.width)
    (hsub : (if base t then (if base s then z.u else z.v) else 0)≤
      (if base s then z.v else z.u))
    (heven : base a=true → ((if base s then z.v else z.u)-
      (if base t then (if base s then z.u else z.v) else 0))%2=0) :
    Triple (RoundFrame L (roundDataValues (bodyValues z (base a) (base s) (base t))) base)
      (valueUnbodyProgram L a s t) (RoundFrame L (roundDataValues z) base) := by
  have ha := controls_nodup L a s t hn a (by simp)
  have hs := controls_nodup L a s t hn s (by simp)
  have ht := controls_nodup L a s t hn t (by simp)
  let z1 : KState := {z with u := if base s then z.v else z.u, v := if base s then z.u else z.v}
  let U := z1.u - if base t then z1.v else 0
  let z2 : KState := {z1 with u := U}
  let z3 : KState := {z2 with u := if base a then U/2 else U}
  let z4 := bodyValues z (base a) (base s) (base t)
  have h1 := swap_frame L s hs z4 base
  have he1 : {z4 with u := if base s then z4.v else z4.u, v := if base s then z4.u else z4.v}=z3 := by
    cases hS : base s <;> simp [z4,z3,z2,z1,U,bodyValues,hS]
  rw [he1] at h1
  have hrestore : (if base a then 2*z3.u else z3.u)=U := by
    cases hA : base a
    · simp [z3,hA]
    · have he := heven hA
      change U%2=0 at he
      simp only [z3,hA,if_true]
      omega
  have hfit : base a=true → 2*z3.u<2^L.width := by
    intro hA
    have h := hrestore
    simp only [hA,ite_true] at h
    rw [h]
    dsimp [U,z1]
    omega
  have h2 := RoundFrame.shift_left L a ha (roundDataValues z3) base .u hfit
  change Triple _ _ (RoundFrame L (Function.update (roundDataValues z3) .u
    (if base a then 2*z3.u else z3.u)) base) at h2
  rw [hrestore] at h2
  have he2 : Function.update (roundDataValues z3) .u U=roundDataValues z2 := by
    funext f; cases f <;> simp [roundDataValues,z3,z2]
  rw [he2] at h2
  have h3 := RoundFrame.inplace L t ht hw (roundDataValues z2) base .u .v
    (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) rfl rfl false
  have hm : (U+(if base t then z1.v else 0))%2^L.width=z1.u := by
    rw [show U+(if base t then z1.v else 0)=z1.u by dsimp [U,z1]; omega]
    exact Nat.mod_eq_of_lt hu
  change Triple _ _ (RoundFrame L (Function.update (roundDataValues z2) .u
    ((U+(if base t then z1.v else 0))%2^L.width)) base) at h3
  rw [hm] at h3
  have he3 : Function.update (roundDataValues z2) .u z1.u=roundDataValues z1 := by
    funext f; cases f <;> simp [roundDataValues,z2]
  rw [he3] at h3
  have h4 := swap_frame L s hs z1 base
  have he4 : {z1 with u := if base s then z1.v else z1.u, v := if base s then z1.u else z1.v}=z := by
    cases hS : base s <;> simp [z1,hS]
  rw [he4] at h4
  exact ((h1.seq h2).seq h3).seq h4

/-- 幽灵系数只用于复用原布局的断言，不参与程序；其值逐线保持。 -/
def valueKStep (z : KState) : KState :=
  let t := valueStep z.value
  {z with u := t.u, v := t.v, k := t.k}

private theorem value_body_step (z : KState) :
    roundDataValues (bodyValues z (decide (z.v ≠ 0)) (kaliskiCode z).1 (kaliskiCode z).2)=
      roundDataValues (valueKStep z) := by
  unfold kaliskiCode
  split_ifs <;> funext f <;> cases f <;>
    simp_all [bodyValues,valueKStep,valueStep,KState.value,roundDataValues] <;>
    split_ifs <;> simp_all <;> omega

private theorem value_controls (L : KaliskiRoundLayout) (hn : L.wires.Nodup) :
    ([L.active,L.swap,L.subtract]++L.data.wires).Nodup := by
  have hh := L.controls_data_nodup hn
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hh w
  simp only [KaliskiRoundLayout.controls,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

private theorem value_body_bounds (L : KaliskiRoundLayout) (z : KState)
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    let S := (kaliskiCode z).1
    let T := (kaliskiCode z).2
    (if S then z.v else z.u)<2^L.data.width ∧
    (if T then (if S then z.u else z.v) else 0)≤(if S then z.v else z.u) ∧
    (decide (z.v ≠ 0)=true → ((if S then z.v else z.u)-
      (if T then (if S then z.u else z.v) else 0))%2=0) := by
  unfold kaliskiCode
  split_ifs <;> simp_all <;> omega

/-- 与既有控制断言组合，但门列完全不读写r/s/out。 -/
theorem valueBodyProgram_state (L : KaliskiRoundLayout) (hn : L.wires.Nodup)
    (z : KState) (K N : Nat) (D : Bool)
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    Triple (RoundState L z K N (decide (z.v ≠ 0)) D (kaliskiCode z).1 (kaliskiCode z).2)
      (valueBodyProgram L.data L.active L.swap L.subtract)
      (RoundState L (valueKStep z) K N (decide (z.v ≠ 0)) D (kaliskiCode z).1 (kaliskiCode z).2) := by
  intro s m h
  have hh := body_frame L.data L.active L.swap L.subtract (value_controls L hn)
    (by simp [KaliskiRoundLayout.data,RoundDataLayout.width]) z s.basis
  simp only [h.2.active,h.2.swap,h.2.subtract] at hh
  obtain ⟨hu',hs,he⟩ := value_body_bounds L z hu hv
  obtain ⟨hp,hv'⟩ := hh hu' hs he s m ⟨h.1,fun _ _ => rfl⟩
  rw [value_body_step] at hv'
  exact ⟨hp,hv'.1,RoundAuxValues.congr L hn K N _ D _ _ _ _ h.2 hv'.2⟩

theorem valueUnbodyProgram_state (L : KaliskiRoundLayout) (hn : L.wires.Nodup)
    (z : KState) (K N : Nat) (D : Bool)
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    Triple (RoundState L (valueKStep z) K N (decide (z.v ≠ 0)) D (kaliskiCode z).1 (kaliskiCode z).2)
      (valueUnbodyProgram L.data L.active L.swap L.subtract)
      (RoundState L z K N (decide (z.v ≠ 0)) D (kaliskiCode z).1 (kaliskiCode z).2) := by
  intro s m h
  have hh := unbody_frame L.data L.active L.swap L.subtract (value_controls L hn)
    (by simp [KaliskiRoundLayout.data,RoundDataLayout.width]) z s.basis
  simp only [h.2.active,h.2.swap,h.2.subtract] at hh
  obtain ⟨hu',hs,he⟩ := value_body_bounds L z hu hv
  have hin : RoundFrame L.data (roundDataValues (bodyValues z (decide (z.v ≠ 0))
      (kaliskiCode z).1 (kaliskiCode z).2)) s.basis s.basis := by
    rw [value_body_step]
    exact ⟨h.1,fun _ _ => rfl⟩
  obtain ⟨hp,hv'⟩ := hh hu' hs he s m hin
  exact ⟨hp,hv'.1,RoundAuxValues.congr L hn K N _ D _ _ _ _ h.2 hv'.2⟩

end ECDSAAdd.Arithmetic
