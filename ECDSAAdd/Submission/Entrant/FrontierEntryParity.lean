import ECDSAAdd.Submission.Entrant.FrontierEntryHalfMath
import ECDSAAdd.Submission.Entrant.FrontierEntryCarryResources
import ECDSAAdd.Submission.Entrant.FrontierEntrySignMath

/-! Unary-half parity recovery from the target magnitude. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run DiagonalCarry5.chain

def parityBits : List Bool := DiagonalCarry5.literal 255 literalValue
def prepareMagnitude (L : Layout) : Program := BalancedCleanup.prepareSign L.toLayout
def parityCarry (L : Layout) (ctl : Wire) : Program :=
  DiagonalCarry5.chain parityBits L.low (L.carry.take 255) L.lower ctl L.parity
def positiveParity (L : Layout) (ctl : Wire) : Program :=
  prepareMagnitude L++(parityCarry L ctl++(prepareMagnitude L).reverse)
def recoverParity (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParity L J++[.X J]

theorem prepare_counts (L : Layout) :
    toffoliCount (prepareMagnitude L)=0 ∧ measurementCount (prepareMagnitude L)=0 := by
  have h := signComplement_counts L.lower L.r
  simp only [prepareMagnitude,BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    h.1,h.2,toffoliCount,measurementCount]
  exact ⟨trivial,trivial⟩

theorem parity_counts (L : Layout) (hw : L.Widths) (ctl : Wire) :
    toffoliCount (positiveParity L ctl)=256 ∧ measurementCount (positiveParity L ctl)=255 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have h := DiagonalCarry5.counts parityBits L.low (L.carry.take 255) L.lower ctl L.parity
    (by simp [parityBits,DiagonalCarry5.literal_length,w.1])
    (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have hk : toffoliCount (parityCarry L ctl)=256 ∧ measurementCount (parityCarry L ctl)=255 := by
    simpa only [parityCarry,parityBits,DiagonalCarry5.literal_length] using h
  constructor
  · rw [positiveParity,toffoliCount_append,toffoliCount_append,toffoliCount_reverse,
      (prepare_counts L).1,hk.1]
  · rw [positiveParity,measurementCount_append,measurementCount_append,measurementCount_reverse,
      (prepare_counts L).2,hk.2]

theorem carry_nodup (L : Layout) (hn : L.wires.Nodup) (ctl : Wire) (hctl : ctl∉L.wires) :
    (ctl::L.parity::L.lower::(L.low++L.carry.take 255)).Nodup := by
  have nd := List.nodup_cons.mpr ⟨hctl,hn⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  have t := (List.take_sublist 255 L.carry).count_le q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.low,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem prepare_low_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    let t := run (prepareMagnitude L) m s
    regValue L.low t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) := by
  have nd := (List.nodup_append'.mp hn).2.1
  have h := BalancedCleanup.prepareSign_value L.toLayout hw nd R hr s m hR hz
  let t := run (prepareMagnitude L) m s
  change regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) at h
  have b := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg b.1
  have c := constants
  have bound : (magnitude R).toNat<2^255 := by norm_num only [Nat.reducePow] at ⊢; omega
  have split : regValue L.r t.basis=regValue L.low t.basis+2^255*(t.basis L.rmsb).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append,(BalancedCleanup.widths L.toLayout hw).1]
    cases k : t.basis L.rmsb <;> simp [regValue,k]
  have low : regValue L.low t.basis=(magnitude R).toNat := by
    rw [h.1] at split
    cases k : t.basis L.rmsb <;> simp only [k,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at split <;> omega
  exact ⟨low,h.2.1,h.2.2⟩

theorem positiveParity_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (B : Bool) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hS : s.basis ctl=B) (hz : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParity L ctl) m s=
      ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ (B && decide (threshold<R.natAbs)))⟩ := by
  let c := run (prepareMagnitude L) [] s
  let z := run (parityCarry L ctl) m c
  let tail := m.drop 255
  have pv := prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have nd0 := (List.nodup_append'.mp hn).2.1
  have prep : ProperProgram (prepareMagnitude L) := BalancedCleanup.prepareSign_proper _ nd0
  have pa : L.parity∉wires (prepareMagnitude L) :=
    (BalancedCleanup.clifford_parity_away _ hw nd0).1
  have nd := carry_nodup L hn ctl hctl
  have ay (a : Wire) (ha : a∈L.carry) : a∉L.r := by
    intro bad
    have h := List.nodup_iff_count.mp hn a
    have ca := List.count_pos_iff.mpr ha
    have cb := List.count_pos_iff.mpr bad
    simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h cb
    omega
  have al (a : Wire) (ha : a∈L.carry) : a≠L.lower := by
    intro eq
    exact flagAway L hn L.lower (by simp) (by simp [←eq,ha])
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    exact (pv.2.2 a (ay a (List.mem_of_mem_take ha)) (al a (List.mem_of_mem_take ha))).trans
      (hc a (List.mem_of_mem_take ha))
  have sp : c.basis L.parity=s.basis L.parity := run_preserves_outside _ [] s _ pa
  have sy : ctl∉L.r := by
    intro bad
    have zero := List.count_eq_zero.mpr hctl
    have pos := List.count_pos_iff.mpr bad
    simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at zero pos
    omega
  have sl : ctl≠L.lower := fun eq => hctl (by simp [eq,Layout.wires,BalancedCleanup.Layout.wires])
  have ss : c.basis ctl=B := (pv.2.2 ctl sy sl).trans hS
  have one := DiagonalCarry5.correct parityBits L.low (L.carry.take 255) L.lower ctl L.parity nd
    (by simp [parityBits,DiagonalCarry5.literal_length,(BalancedCleanup.widths L.toLayout hw).1])
    (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) c m clean
  have cp : z.basis L.parity=(s.basis L.parity ^^ (B && decide (threshold<R.natAbs))) := by
    change (run (DiagonalCarry5.chain parityBits L.low (L.carry.take 255) L.lower ctl L.parity) m c).basis L.parity=_
    rw [one.2.2,sp,ss]
    simp only [parityBits,DiagonalCarry5.literal_length,DiagonalCarry5.literal_value _ _ literal_bound,
      pv.1,pv.2.1,carry_predicate R]
  have ex : BalancedCleanup.Except L.parity z (run (prepareMagnitude L) [] s) := ⟨one.1,one.2.1⟩
  have restore := BalancedCleanup.inverse_except (prepareMagnitude L) prep L.parity pa s z [] tail ex
  have actual : run (positiveParity L ctl) m s=run (prepareMagnitude L).reverse tail z := by
    rw [positiveParity,run_append,(prepare_counts L).2,List.take_zero,List.drop_zero,run_append,run_take]
    have cp := DiagonalCarry5.counts parityBits L.low (L.carry.take 255) L.lower ctl L.parity
      (by simp [parityBits,DiagonalCarry5.literal_length,(BalancedCleanup.widths L.toLayout hw).1])
      (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
    rw [show measurementCount (parityCarry L ctl)=255 from by
      simpa only [parityCarry,parityBits,DiagonalCarry5.literal_length] using cp.2]
  rw [actual]
  apply State.extensionality
  · exact restore.1
  · funext a
    by_cases ap : a=L.parity
    · subst a
      have keep := run_preserves_outside (prepareMagnitude L).reverse tail z L.parity (by rwa [wires_reverse])
      simpa only [writeBit,Function.update_self] using keep.trans cp
    · simpa only [writeBit,Function.update_of_ne ap] using restore.2 a ap

theorem recoverParity_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (recoverParity L J)=256 ∧ measurementCount (recoverParity L J)=255 := by
  have h := parity_counts L hw J
  simpa only [recoverParity,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    Nat.zero_add,Nat.add_zero] using h

/-- The control is negated only for the magnitude test. -/
theorem recoverParity_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (B : Bool) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hS : s.basis J=B) (hz : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParity L J) m s=
      ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ ((!B) && decide (threshold<R.natAbs)))⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have hp : L.parity≠J := away _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])
  have a := positiveParity_xor L hw hn J hJ (!B) R hr u m sameR
    (by simp [u,writeBit,hS]) (by rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz)
    (fun q hq => (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq))
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  rw [recoverParity,run_append,run_append,show measurementCount [.X J]=0 from rfl,
    List.take_zero,List.drop_zero,first,measurementCount_append,show measurementCount [.X J]=0 from rfl,Nat.zero_add,run_take,a]
  simp only [run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qj : q=J
    · subst q
      simp [u,writeBit,hp,Ne.symm hp]
    · by_cases qp : q=L.parity
      · subst q
        simp [u,writeBit,hp]
      · simp [u,writeBit,qj,qp]

end ECDSAAdd.Entrant.EntryHalf5
