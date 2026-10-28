import ECDSAAdd.Arithmetic.RecordedRailDeferBareProof

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

def TwoReady (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire) (bits : BasisState) : Prop :=
  RecordedRailVented.Aligned a0 b0 bank ∧ RecordedRailVented.Aligned a1 b1 bank ∧
    ([cin,q0,q1]++a0++b0++a1++b1++bank).Nodup ∧
    (∀q∈bank,bits q=false) ∧ bits q0=false ∧ bits q1=false

theorem two_layout (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (nd : ([cin,q0,q1]++a0++b0++a1++b1++bank).Nodup) :
    ([cin]++a0++b0++bank++[q0]).Nodup ∧
    ([q0]++a1++b1++bank++[q1]).Nodup ∧
    (cin::q1::(a0++a1++b1++bank)).Disjoint (b0++[q0]) ∧
    (cin::q0::(a0++b0++a1++bank)).Disjoint (b1++[q1]) ∧
    q0∉(b0++b1)++[q1] := by
  have first : ([cin]++a0++b0++bank++[q0]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have second : ([q0]++a1++b1++bank++[q1]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cross0 : ((cin::q1::(a0++a1++b1++bank))++(b0++[q0])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cross1 : ((cin::q0::(a0++b0++a1++bank))++(b1++[q1])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  refine ⟨first,second,(List.nodup_append'.mp cross0).2.2,
    (List.nodup_append'.mp cross1).2.2,?_⟩
  intro hmem
  have h := List.nodup_iff_count.mp nd q0
  have positive := List.count_pos_iff.mpr hmem
  simp only [List.count_cons,List.count_append,List.count_nil] at h positive
  simp only [beq_self_eq_true,if_true] at h
  omega

/-- Low-word remainder plus the next word and the old carry is the exact
concatenated original sum. This pure lemma adds no execution hypothesis. -/
theorem concatenate_value (A0 B0 A1 B1 cin M : Nat) :
    (A0+B0+cin)%M+M*(A1+B1+(A0+B0+cin)/M)=
      (A0+M*A1)+(B0+M*B1)+cin := by
  have split := Nat.mod_add_div (A0+B0+cin) M
  calc
    _=((A0+B0+cin)%M+M*((A0+B0+cin)/M))+M*(A1+B1) := by ring
    _=(A0+B0+cin)+M*(A1+B1) := by rw [split]
    _=_ := by ring

def firstCarry (a0 b0 : List Wire) (cin : Wire) (bits : BasisState) : Bool :=
  decide (2^b0.length ≤ regValue a0 bits+regValue b0 bits+(bits cin).toNat)

/-- The actual vented carry is the original first-prefix overflow Boolean. -/
theorem first_carry (a0 b0 bank : List Wire) (cin q0 : Wire)
    (bits : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : RecordedRailVented.Ready a0 b0 (some cin) bank q0 bits) :
    (runWithTape (RecordedRailVented.vented a0 b0 (some cin) bank q0) m cursor ⟨phase,bits⟩).basis q0=
      firstCarry a0 b0 cin bits := by
  let t := runWithTape (RecordedRailVented.vented a0 b0 (some cin) bank q0) m cursor ⟨phase,bits⟩
  have h := RecordedRailVented.correct a0 b0 (some cin) bank q0 bits phase m cursor ready
  have sum := h.2.2.1
  have high := regValue_highBit b0 q0 t.basis
  rw [sum] at high
  cases hc : t.basis q0 with
  | false =>
    have hn : ¬(2^b0.length ≤ regValue a0 bits+regValue b0 bits+(bits cin).toNat) := by
      intro hp
      have ht := high.mpr hp
      simp only [hc,Bool.false_eq_true] at ht
    simp only [firstCarry,decide_eq_false hn]
  | true =>
    have quotient := h.2.2.2.2.1
    change (t.basis q0).toNat=
      (regValue a0 bits+regValue b0 bits+(bits cin).toNat)/2^b0.length at quotient
    rw [hc] at quotient
    have bound : 2^b0.length ≤ regValue a0 bits+regValue b0 bits+(bits cin).toNat := by
      by_contra hn
      have less := Nat.lt_of_not_ge hn
      rw [Nat.div_eq_of_lt less] at quotient
      norm_num at quotient
    simp [firstCarry,bound]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.two_layout
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.concatenate_value
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.first_carry
