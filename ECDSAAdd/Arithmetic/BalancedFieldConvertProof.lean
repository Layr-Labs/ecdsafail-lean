import ECDSAAdd.Arithmetic.BalancedFieldConvertMath
import ECDSAAdd.Arithmetic.LiteralConstAddProof
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit Secp256k1
attribute [local irreducible] run literalConstAdd mappedAdd mappedSub

theorem cx_view (L : Layout) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    let t := run [.CX L.msb L.flag] m s
    t.phase=s.phase ∧ regValue L.word t.basis=regValue L.word s.basis ∧
    t.basis L.flag=(s.basis L.flag ^^ s.basis L.msb) ∧
    ∀q,q≠L.flag → t.basis q=s.basis q := by
  have af := layout_away L hn L.flag (by simp)
  dsimp only
  simp only [run]
  refine ⟨True.intro,?_,?_,?_⟩
  · apply regValue_congr
    intro q hq
    simp only [writeBit,Function.update_of_ne (show q≠L.flag from fun e => af (e ▸ hq))]
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

theorem predicate_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hi : s.basis L.cin=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (predicate L) m s=⟨s.phase,writeBit s.basis L.flag (s.basis L.flag ^^ threshold x)⟩ := by
  let m₁ := m.drop (measurementCount (literalConstAdd L.word L.carry L.cin L.one bias))
  generalize eu : run (literalConstAdd L.word L.carry L.cin L.one bias) m s=u
  generalize ev : run [.CX L.msb L.flag] m₁ u=v
  generalize ew : run (literalConstAdd L.word L.carry L.cin L.one inverseBias) m₁ v=w
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have h1 := literalConstAdd_correct L.word L.carry L.cin L.one bias (layout_literal L hn) cy s m ho hc
  rw [eu] at h1
  have uval : regValue L.word u.basis=x.val+bias := by
    rw [h1.2.2,hx,hi,len,Bool.toNat_false,Nat.add_zero]
    exact Nat.mod_eq_of_lt (biased_value x).1
  have umsb := word_msb L hw u.basis _ (threshold x) uval (biased_value x).2
  have h2 := cx_view L hn u m₁
  rw [ev] at h2
  have clean2 (q : Wire) (hq : q∈scratch L) : v.basis q=s.basis q :=
    (h2.2.2.2 q (scratch_away L hn q hq).2).trans (h1.2.1 q (scratch_away L hn q hq).1)
  have vi : v.basis L.cin=false := (clean2 _ (by simp [scratch])).trans hi
  have vo : v.basis L.one=false := (clean2 _ (by simp [scratch])).trans ho
  have vc : ∀q∈L.carry,v.basis q=false := fun q hq => (clean2 q (by simp [scratch,hq])).trans (hc q hq)
  have h3 := literalConstAdd_correct L.word L.carry L.cin L.one inverseBias (layout_literal L hn) cy v m₁ vo vc
  rw [ew] at h3
  have wval : regValue L.word w.basis=x.val := by
    rw [h3.2.2,h2.2.1,uval,vi,len,Bool.toNat_false,Nat.add_zero]
    exact generic_unbias wordModulus bias x.val bias_le_modulus (canonical_word_bound x)
  have af := layout_away L hn L.flag (by simp)
  have wf : w.basis L.flag=(s.basis L.flag ^^ threshold x) := by
    rw [h3.2.1 _ af,h2.2.2.1,h1.2.1 _ af,umsb]
  have actual : run (predicate L) m s=w := by
    simp only [predicate,List.append_assoc,run_append]
    simp only [run_take]
    simp only [measurementCount_append,
      show measurementCount [.CX L.msb L.flag]=0 from rfl,Nat.add_zero,List.drop_zero]
    rw [eu,ev,ew]
  rw [actual]
  apply State.extensionality
  · exact h3.1.trans (h2.1.trans h1.1)
  · funext q
    by_cases hf : q=L.flag
    · subst q
      simpa only [writeBit,Function.update_self] using wf
    · simp only [writeBit,Function.update_of_ne hf]
      by_cases hq : q∈L.word
      · exact (regValue_eq_iff L.word w.basis s.basis).mp (wval.trans hx.symm) q hq
      · exact (h3.2.1 q hq).trans ((h2.2.2.2 q hf).trans (h1.2.1 q hq))

theorem predicate_view (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hi : s.basis L.cin=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    let t := run (predicate L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=x.val ∧
    t.basis L.flag=(s.basis L.flag ^^ threshold x) ∧
    ∀q,q≠L.flag → t.basis q=s.basis q := by
  dsimp only
  rw [predicate_run L hw hn x s m hx hi ho hc]
  refine ⟨rfl,?_,?_,?_⟩
  · apply Eq.trans _ hx
    apply regValue_congr
    intro q hq
    have af := layout_away L hn L.flag (by simp)
    simp only [writeBit,Function.update_of_ne (show q≠L.flag from fun e => af (e ▸ hq))]
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

theorem work_of_frame (L : Layout) (hn : L.wires.Nodup) (s t : State)
    (hc : ∀q∈work L,s.basis q=false) (hf : ∀q,q∉L.word → t.basis q=s.basis q) :
    ∀q∈work L,t.basis q=false := by
  intro q hq
  have ha : q∉L.word := layout_away L hn q (by
    simp only [work,scratch,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢; tauto)
  exact (hf q ha).trans (hc q hq)

/-- Actual canonical-to-centered boundary conversion, with all work restored,
all measurement records and arbitrary incoming phase. -/
theorem center_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (center L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=centerWord x ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  let m₁ := m.drop (measurementCount (predicate L))
  let m₂ := m₁.drop (measurementCount (mappedAdd (correction L) L.word L.carry L.cin))
  generalize eu : run (predicate L) m s=u
  generalize ev : run (mappedAdd (correction L) L.word L.carry L.cin) m₁ u=v
  generalize et : run [.CX L.msb L.flag] m₂ v=t
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have p1 := predicate_view L hw hn x s m hx (hc _ (by simp [work,scratch]))
    (hc _ (by simp [work,scratch])) (fun q hq => hc q (by simp [work,scratch,hq]))
  rw [eu] at p1
  have cleanU (q : Wire) (hq : q∈scratch L) : u.basis q=false :=
    (p1.2.2.2 q (scratch_away L hn q hq).2).trans (hc q (by simp [work,hq]))
  have uf : u.basis L.flag=threshold x := by
    rw [p1.2.2.1,hc _ (by simp [work]),Bool.false_xor]
  have p2 := mappedAdd_correct (correction L) L.word L.carry L.cin (layout_add L hn)
    (fun q hq => (correction_sources L q hq).symm ▸ flag_away L hn)
    (by simp [correction,len]) cy u m₁ (fun q hq => cleanU q (by simp [scratch,hq]))
  rw [ev] at p2
  have vval : regValue L.word v.basis=centerWord x := by
    rw [p2.2.2,correction_value,uf,p1.2.1,cleanU _ (by simp [scratch]),len,
      Bool.toNat_false,Nat.add_zero,Nat.add_comm (if threshold x then sparseF else 0) x.val]
    exact center_add_value x
  have vf : v.basis L.flag=threshold x :=
    (p2.2.1 _ (layout_away L hn _ (by simp))).trans uf
  have vm := word_msb L hw v.basis _ (threshold x) vval (center_threshold x)
  have p3 := cx_view L hn v m₂
  rw [et] at p3
  have tf : t.basis L.flag=false := by rw [p3.2.2.1,vf,vm,Bool.xor_self]
  have frame : ∀q,q∉L.word → t.basis q=s.basis q := by
    intro q hq
    by_cases he : q=L.flag
    · subst q
      exact tf.trans (hc _ (by simp [work])).symm
    · exact (p3.2.2.2 q he).trans ((p2.2.1 q hq).trans (p1.2.2.2 q he))
  have actual : run (center L) m s=t := by
    simp only [center,List.append_assoc,run_append,run_take,measurementCount_append]
    rw [eu,ev]
    simpa only [m₂,m₁,List.drop_drop,Nat.add_comm] using et
  rw [actual]
  exact ⟨p3.1.trans (p2.1.trans p1.1),p3.2.1.trans vval,work_of_frame L hn s t hc frame,frame⟩

/-- Actual inverse conversion of every valid centered field word. -/
theorem canonical_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=centerWord x)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (canonical L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=x.val ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  let m₁ := m.drop (measurementCount (mappedSub (correction L) L.word L.carry L.cin))
  generalize eu : run [.CX L.msb L.flag] m s=u
  generalize ev : run (mappedSub (correction L) L.word L.carry L.cin) m u=v
  generalize et : run (predicate L) m₁ v=t
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have sm := word_msb L hw s.basis _ (threshold x) hx (center_threshold x)
  have p1 := cx_view L hn s m
  rw [eu] at p1
  have cleanU (q : Wire) (hq : q∈scratch L) : u.basis q=false :=
    (p1.2.2.2 q (scratch_away L hn q hq).2).trans (hc q (by simp [work,hq]))
  have uf : u.basis L.flag=threshold x := by
    rw [p1.2.2.1,hc _ (by simp [work]),sm,Bool.false_xor]
  have p2 := mappedSub_correct (correction L) L.word L.carry L.cin (layout_add L hn)
    (fun q hq => (correction_sources L q hq).symm ▸ flag_away L hn)
    (by simp [correction,len]) cy u m (fun q hq => cleanU q (by simp [scratch,hq]))
    (cleanU _ (by simp [scratch]))
  rw [ev] at p2
  have vval : regValue L.word v.basis=x.val := by
    rw [p2.2.2,correction_value,uf,p1.2.1,hx,len]
    exact canonical_sub_value x
  have cleanV (q : Wire) (hq : q∈scratch L) : v.basis q=false :=
    (p2.2.1 q (scratch_away L hn q hq).1).trans (cleanU q hq)
  have vf : v.basis L.flag=threshold x :=
    (p2.2.1 _ (layout_away L hn _ (by simp))).trans uf
  have p3 := predicate_view L hw hn x v m₁ vval (cleanV _ (by simp [scratch]))
    (cleanV _ (by simp [scratch])) (fun q hq => cleanV q (by simp [scratch,hq]))
  rw [et] at p3
  have tf : t.basis L.flag=false := by rw [p3.2.2.1,vf,Bool.xor_self]
  have frame : ∀q,q∉L.word → t.basis q=s.basis q := by
    intro q hq
    by_cases he : q=L.flag
    · subst q
      exact tf.trans (hc _ (by simp [work])).symm
    · exact (p3.2.2.2 q he).trans ((p2.2.1 q hq).trans (p1.2.2.2 q he))
  have actual : run (canonical L) m s=t := by
    simp only [canonical,List.append_assoc,run_append]
    simp only [run_take]
    simp only [measurementCount_append,
      show measurementCount [.CX L.msb L.flag]=0 from rfl,Nat.zero_add,List.drop_zero]
    rw [eu,ev,et]
  rw [actual]
  exact ⟨p3.1.trans (p2.1.trans p1.1),p3.2.1,work_of_frame L hn s t hc frame,frame⟩
end ECDSAAdd.Arithmetic.BalancedConvert
#print axioms ECDSAAdd.Arithmetic.BalancedConvert.predicate_run
#print axioms ECDSAAdd.Arithmetic.BalancedConvert.center_correct
#print axioms ECDSAAdd.Arithmetic.BalancedConvert.canonical_correct
