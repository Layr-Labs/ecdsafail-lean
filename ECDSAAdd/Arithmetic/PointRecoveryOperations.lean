import ECDSAAdd.Arithmetic.PointRecoveryLayout

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointRecoveryConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  compactRecoveryConstant (L.recoveryConstant r) L.core.generic SquareReduction.c p k.val
def pointRecoveryReflection (L : ControlledPointLayout) : Program :=
  L.recoveryNegate.reflection L.core.generic p

def pointRecoveryNegate (L : ControlledPointLayout) : Program :=
  L.recoveryNegate.program L.core.generic p SquareReduction.c

theorem pointRecoveryConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue r s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryConstantAdd L r k) records s).phase=s.phase ∧
    regValue r (run (pointRecoveryConstantAdd L r k) records s).basis=(X+(if B then k.val else 0))%p ∧
    ∀q,q∉r → (run (pointRecoveryConstantAdd L r k) records s).basis q=s.basis q := by
  let K := L.recoveryConstant r
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  have widths := L.recoveryConstant_widths hw r len
  have nd := L.recoveryConstant_nodup hw hn r hr
  have aux (q : Wire) (hq : q∈K.src++K.carry++[K.high,K.cin,K.flag]) : s.basis q=false := by
    change q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag] at hq
    rw [L.recoveryConstant_pool hw r] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have source : regValue K.src s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have carries : ∀q∈K.carry,s.basis q=false := fun q hq => aux q (by simp [hq])
  have result := compactRecoveryConstant_correct K L.core.generic 256 SquareReduction.c p k.val widths nd
    (by decide) (by norm_num [p,SquareReduction.c]) (by norm_num [SquareReduction.c]) k.isLt X hX s records
    source hx (aux _ (by simp)) (aux _ (by simp)) carries (aux _ (by simp))
  simpa only [pointRecoveryConstantAdd,K,hb] using result

theorem pointRecoveryNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryNegate L) records s).phase=s.phase ∧
    regValue L.point.x (run (pointRecoveryNegate L) records s).basis=(if B then (p-X)%p else X) ∧
    ∀q,q∉L.point.x → (run (pointRecoveryNegate L) records s).basis q=s.basis q := by
  let K := L.recoveryNegate
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have work : regValue K.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have npos : 0<K.word.length := by simp [K,recoveryNegate,point,hw.inputX]
  have pc : p+SquareReduction.c=2^K.word.length := by simp [K,recoveryNegate,point,hw.inputX];norm_num [p,SquareReduction.c]
  have result := K.program_correct L.core.generic (L.recoveryNegate_nodup hw hn) sizes npos p SquareReduction.c X
    pc (by norm_num [SquareReduction.c]) hX s records hx work (aux _ (by simp)) (aux _ (by simp))
  simpa only [pointRecoveryNegate,K,recoveryNegate,hb] using result

theorem pointRecoveryReflection_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X : Nat) (B : Bool) (hX : X<p) (s : State) (records : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X) (hc : regValue L.dialogPool s.basis=0) :
    (run (pointRecoveryReflection L) records s).phase=s.phase ∧
    regValue L.point.x (run (pointRecoveryReflection L) records s).basis=(if B then p-1-X else X) ∧
    ∀q,q∉L.point.x → (run (pointRecoveryReflection L) records s).basis q=s.basis q := by
  let K := L.recoveryNegate
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have work : regValue K.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have npos : 0<K.word.length := by simp [K,recoveryNegate,point,hw.inputX]
  have result := K.reflection_correct L.core.generic (L.recoveryNegate_nodup hw hn) sizes npos p X
    (by simp [K,recoveryNegate,point,hw.inputX];norm_num [p]) hX s records hx work
    (aux _ (by simp)) (aux _ (by simp))
  simpa only [pointRecoveryNegate,K,recoveryNegate,hb] using result

theorem pointRecoveryConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (pointRecoveryConstantAdd L r k)=1023 ∧ measurementCount (pointRecoveryConstantAdd L r k)=1023 := by
  have len : r.length=256 := by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY
  exact compactRecoveryConstant_counts _ _ 256 _ _ _ (L.recoveryConstant_widths hw r len) (by decide)

theorem pointRecoveryNegate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointRecoveryNegate L)=1022 ∧ measurementCount (pointRecoveryNegate L)=1022 := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by
    simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have h := L.recoveryNegate.program_counts L.core.generic p SquareReduction.c sizes (by simp [recoveryNegate,point,hw.inputX])
  simpa [pointRecoveryNegate,recoveryNegate,point,hw.inputX] using h

theorem pointRecoveryConstantAdd_support (L : ControlledPointLayout) (hw : L.Widths) (r : List Wire) (k : Fp) :
    wires (pointRecoveryConstantAdd L r k)⊆(L.core.generic::r++L.dialogPool.take 515).toFinset := by
  have support := compactRecoveryConstant_support (L.recoveryConstant r) L.core.generic SquareReduction.c p k.val
  intro q hq
  have h := support hq
  rw [←L.recoveryConstant_pool hw r]
  simp only [recoveryConstant,MeasuredCanonicalModLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

theorem pointRecoveryNegate_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (pointRecoveryNegate L)⊆(L.core.generic::L.point.x++L.dialogPool.take 258).toFinset := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have support := L.recoveryNegate.program_support L.core.generic p SquareReduction.c sizes
  intro q hq
  have h := support hq
  rw [←L.recoveryNegate_pool hw]
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

theorem pointRecoveryReflection_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointRecoveryReflection L)=255 ∧ measurementCount (pointRecoveryReflection L)=255 := by
  have sizes : L.recoveryNegate.work.length=L.recoveryNegate.word.length := by
    simp [recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have h := L.recoveryNegate.reflection_counts L.core.generic p sizes (by simp [recoveryNegate,point,hw.inputX])
  simpa [pointRecoveryReflection,recoveryNegate,point,hw.inputX] using h

theorem pointRecoveryReflection_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (pointRecoveryReflection L)⊆(L.core.generic::L.point.x++L.dialogPool.take 258).toFinset := by
  have support := L.recoveryNegate.reflection_support L.core.generic p
  intro q hq
  have h := support hq
  rw [←L.recoveryNegate_pool hw]
  simp only [recoveryNegate,CompactRecoveryNegateLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  tauto

end ECDSAAdd.Arithmetic
