import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- Exact strict comparison with a threshold divisible by eight.
All high bits are compared; low bits cannot affect this predicate. -/
def compareLtMultipleEight (x T carry : List Wire) (cin target : Wire) (K : Nat) : Program :=
  compareLtConst none (x.drop 3) (T.take (x.length-3)) (carry.take (x.length-3)) cin target (K/8)

theorem multipleEight_comparison (X K : Nat) (hK : K%8=0) : X<K ↔ X/8<K/8 := by omega

theorem regValue_drop_three (x : List Wire) (hx : 3≤x.length) (s : BasisState) :
    regValue (x.drop 3) s=regValue x s/8 := by
  have he := regValue_append (x.take 3) (x.drop 3) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hx] at he
  have hb := regValue_lt (x.take 3) s
  simp only [List.length_take,Nat.min_eq_left hx] at hb
  norm_num at he hb
  omega

private theorem compareEight_lengths (x T carry : List Wire)
    (hT : T.length=x.length) (hc : carry.length=x.length) :
    (x.drop 3).length=(T.take (x.length-3)).length ∧
      (carry.take (x.length-3)).length=(T.take (x.length-3)).length := by
  simp [hT,hc,List.length_drop,List.length_take]

/-- The optimized exact comparator uses three fewer Toffolis and measurements. -/
theorem compareLtMultipleEight_counts (x T carry : List Wire) (cin target : Wire) (K : Nat)
    (hT : T.length=x.length) (hc : carry.length=x.length) :
    toffoliCount (compareLtMultipleEight x T carry cin target K)=x.length-3 ∧
    measurementCount (compareLtMultipleEight x T carry cin target K)=x.length-3 := by
  have hl := compareEight_lengths x T carry hT hc
  have hh := (compareLt_counts none (x.drop 3) (T.take (x.length-3))
    (carry.take (x.length-3)) cin target hl.1 hl.2).2.2 (K/8)
  simpa [compareLtMultipleEight,hT,List.length_take,Nat.min_eq_left (Nat.sub_le _ _)] using hh

/-- All-record phase/frame correctness, preserving both full scratch arrays and the unused low bits. -/
theorem compareLtMultipleEight_correct (x T carry : List Wire) (cin target : Wire) (K : Nat)
    (hn : (target::cin::(x++T++carry)).Nodup) (hx : 3≤x.length)
    (hT : T.length=x.length) (hc : carry.length=x.length)
    (hK : K<2^x.length) (hm : K%8=0) (s : State) (m : List Bool)
    (hT0 : regValue T s.basis=0) (hc0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (compareLtMultipleEight x T carry cin target K) m s).phase=s.phase ∧
    (∀ w,w≠target → (run (compareLtMultipleEight x T carry cin target K) m s).basis w=s.basis w) ∧
    (run (compareLtMultipleEight x T carry cin target K) m s).basis target=
      (s.basis target ^^ decide (regValue x s.basis<K)) := by
  let xs := x.drop 3
  let ts := T.take (x.length-3)
  let cs := carry.take (x.length-3)
  have hl := compareEight_lengths x T carry hT hc
  have hnd : (target::cin::(xs++ts++cs)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    have ha := (List.drop_sublist 3 x).count_le w
    have ht := (List.take_sublist (x.length-3) T).count_le w
    have hk := (List.take_sublist (x.length-3) carry).count_le w
    simp only [xs,ts,cs,List.count_cons,List.count_append] at hh ⊢
    omega
  have ht0 : regValue ts s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hT0 w (List.mem_of_mem_take hw))
  have hk0 : regValue cs s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hc0 w (List.mem_of_mem_take hw))
  have hpow : 2^x.length=8*2^(x.length-3) := by
    rw [show x.length=3+(x.length-3) by omega,pow_add]
    norm_num
  have hsmall : K/8<2^ts.length := by
    have hlen : ts.length=x.length-3 := by simp [ts,hT]
    rw [hlen]
    rw [hpow] at hK
    omega
  have hs := compareLtConst_spec xs ts cs cin target hnd hl.1 hl.2 (K/8) hsmall
    (regValue xs s.basis) (s.basis target) s m ⟨⟨⟨⟨rfl,ht0⟩,hk0⟩,hi⟩,rfl⟩
  obtain ⟨hf,hv⟩ := hs
  simp only [Holds.holds] at hv
  change (run (compareLtConst none xs ts cs cin target (K/8)) m s).phase=s.phase ∧ _
  refine ⟨hf,?_,?_⟩
  · intro w hw
    by_cases hxs : w∈xs
    · exact (regValue_eq_iff _ _ _).mp hv.1.1.1.1 w hxs
    by_cases hts : w∈ts
    · exact (regValue_eq_iff _ _ _).mp (hv.1.1.1.2.trans ht0.symm) w hts
    by_cases hcs : w∈cs
    · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans hk0.symm) w hcs
    by_cases hci : w=cin
    · subst w; exact hv.1.2.trans hi.symm
    apply run_preserves_outside
    change w∉wires (compareLtConst none xs ts cs cin target (K/8))
    rw [(compareLt_wires none xs ts cs cin target hl.1 hl.2).2 (K/8)]
    simp [hw,hxs,hts,hcs,hci]
  · have he : decide (regValue xs s.basis<K/8)=decide (regValue x s.basis<K) := by
      rw [regValue_drop_three x hx s.basis]
      exact decide_eq_decide.mpr (multipleEight_comparison _ K hm).symm
    exact hv.2.trans (congrArg (fun b : Bool => s.basis target ^^ b) he)

end ECDSAAdd.Arithmetic
