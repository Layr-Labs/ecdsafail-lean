import ECDSAAdd.Arithmetic.BalancedFieldConvertProof
import ECDSAAdd.Arithmetic.BalancedConvertPhysical
import ECDSAAdd.Arithmetic.ConstantBorrow
import ECDSAAdd.Arithmetic.TrailingZeroCompare
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Baselines.SlotBalanced

/-! Lane A balanced converter.  The exact threshold predicate
`flag ^= [q < x]` of `BalancedConvert` is computed by two literal 256-bit
additions (510 Toffoli).  Here it is computed by one literal comparison
`compareConstantGe` against `(q+1)/8` on the high 253 bits
(253 Toffoli, measurement-erased borrows).  The predicate has the identical
State-level effect, so both conversions keep the original contracts. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.BalancedConvert.LaneA
open BalancedField BalancedCircuit Secp256k1
attribute [local irreducible] run literalConstAdd mappedAdd mappedSub compareConstantLt

/-- First canonical value strictly above the radius `q`. -/
def cutoff : Nat := wordHalf - bias

theorem cutoff_spec : (cutoff : Int) = q + 1 ∧ cutoff < 2^256 := by
  have c := convert_constants
  unfold cutoff
  constructor
  · have h1 : bias ≤ wordHalf := c.2.2.2.1.le
    rw [Nat.cast_sub h1]
    omega
  · have : wordHalf = 2^255 := rfl
    omega

theorem threshold_cutoff (x : Fp) : threshold x = !decide (x.val < cutoff) := by
  have c := cutoff_spec.1
  unfold threshold
  by_cases h : x.val < cutoff
  · have : ¬ (q < (x.val : Int)) := by omega
    rw [decide_eq_false this, decide_eq_true h]; rfl
  · have : q < (x.val : Int) := by omega
    rw [decide_eq_true this, decide_eq_false h]; rfl

def fastPredicate (L : Layout) : Program :=
  compareConstantGe (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8)

def fastCenter (L : Layout) : Program :=
  fastPredicate L++mappedAdd (correction L) L.word L.carry L.cin++[.CX L.msb L.flag]

def fastCanonical (L : Layout) : Program :=
  [.CX L.msb L.flag]++mappedSub (correction L) L.word L.carry L.cin++fastPredicate L

theorem layout_compare (L : Layout) (hn : L.wires.Nodup) : (L.flag::L.cin::(L.word++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem fastPredicate_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hi : s.basis L.cin=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (fastPredicate L) m s=⟨s.phase,writeBit s.basis L.flag (s.basis L.flag ^^ threshold x)⟩ := by
  have len := word_length L hw
  have cy : (L.carry.drop 3).length+1=(L.word.drop 3).length := by
    simp [hw.2,len]
  have nd : (L.flag::L.cin::(L.word.drop 3++L.carry.drop 3)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (layout_compare L hn) q
    have a := (List.drop_sublist 3 L.word).count_le q
    have b := (List.drop_sublist 3 L.carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have hk : cutoff/8 < 2^(L.word.drop 3).length := by
    rw [List.length_drop,len]
    decide
  have pred : decide (regValue (L.word.drop 3) s.basis<cutoff/8)=decide (x.val<cutoff) := by
    rw [regValue_drop_three L.word (by omega) s.basis,hx]
    exact decide_eq_decide.mpr (multipleEight_comparison x.val cutoff (by decide)).symm
  have r := compareConstantLt_correct (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8)
    nd cy hk s
    (m.take (measurementCount (compareConstantLt (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8))))
    (fun q hq => hc q (List.mem_of_mem_drop hq))
  generalize et : run (compareConstantLt (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8))
    (m.take (measurementCount (compareConstantLt (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8)))) s=t at r
  have actual : run (fastPredicate L) m s=⟨t.phase,writeBit t.basis L.flag (!t.basis L.flag)⟩ := by
    simp only [fastPredicate,compareConstantGe,run_append,et]
    simp only [run]
  rw [actual]
  apply State.extensionality
  · exact r.1
  · funext q
    by_cases hf : q=L.flag
    · subst q
      simp only [writeBit,Function.update_self,r.2.2,hi,Bool.toNat_false,Nat.add_zero,
        pred,threshold_cutoff]
      cases s.basis L.flag <;> cases decide (x.val < cutoff) <;> rfl
    · simp only [writeBit,Function.update_of_ne hf]
      exact r.2.1 q hf

theorem fastPredicate_view (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hi : s.basis L.cin=false) (hc : ∀q∈L.carry,s.basis q=false) :
    let t := run (fastPredicate L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=x.val ∧
    t.basis L.flag=(s.basis L.flag ^^ threshold x) ∧
    ∀q,q≠L.flag → t.basis q=s.basis q := by
  dsimp only
  rw [fastPredicate_run L hw hn x s m hx hi hc]
  refine ⟨rfl,?_,?_,?_⟩
  · apply Eq.trans _ hx
    apply regValue_congr
    intro q hq
    have af := layout_away L hn L.flag (by simp)
    simp only [writeBit,Function.update_of_ne (show q≠L.flag from fun e => af (e ▸ hq))]
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

theorem fastCenter_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (fastCenter L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=centerWord x ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  let m₁ := m.drop (measurementCount (fastPredicate L))
  let m₂ := m₁.drop (measurementCount (mappedAdd (correction L) L.word L.carry L.cin))
  generalize eu : run (fastPredicate L) m s=u
  generalize ev : run (mappedAdd (correction L) L.word L.carry L.cin) m₁ u=v
  generalize et : run [.CX L.msb L.flag] m₂ v=t
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have p1 := fastPredicate_view L hw hn x s m hx (hc _ (by simp [work,scratch]))
    (fun q hq => hc q (by simp [work,scratch,hq]))
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
  have actual : run (fastCenter L) m s=t := by
    simp only [fastCenter,List.append_assoc,run_append,run_take,measurementCount_append]
    rw [eu,ev]
    simpa only [m₂,m₁,List.drop_drop,Nat.add_comm] using et
  rw [actual]
  exact ⟨p3.1.trans (p2.1.trans p1.1),p3.2.1.trans vval,work_of_frame L hn s t hc frame,frame⟩

theorem fastCanonical_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=centerWord x)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (fastCanonical L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=x.val ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  let m₁ := m.drop (measurementCount (mappedSub (correction L) L.word L.carry L.cin))
  generalize eu : run [.CX L.msb L.flag] m s=u
  generalize ev : run (mappedSub (correction L) L.word L.carry L.cin) m u=v
  generalize et : run (fastPredicate L) m₁ v=t
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
  have p3 := fastPredicate_view L hw hn x v m₁ vval (cleanV _ (by simp [scratch]))
    (fun q hq => cleanV q (by simp [scratch,hq]))
  rw [et] at p3
  have tf : t.basis L.flag=false := by rw [p3.2.2.1,vf,Bool.xor_self]
  have frame : ∀q,q∉L.word → t.basis q=s.basis q := by
    intro q hq
    by_cases he : q=L.flag
    · subst q
      exact tf.trans (hc _ (by simp [work])).symm
    · exact (p3.2.2.2 q he).trans ((p2.2.1 q hq).trans (p1.2.2.2 q he))
  have actual : run (fastCanonical L) m s=t := by
    simp only [fastCanonical,List.append_assoc,run_append]
    simp only [run_take]
    simp only [measurementCount_append,
      show measurementCount [.CX L.msb L.flag]=0 from rfl,Nat.zero_add,List.drop_zero]
    rw [eu,ev,et]
  rw [actual]
  exact ⟨p3.1.trans (p2.1.trans p1.1),p3.2.1,work_of_frame L hn s t hc frame,frame⟩

/-- Two runs with the same converter contract end in the same State. -/
theorem converted_state_eq (L : Layout) (s t₁ t₂ : State) (V : Nat)
    (h₁ : t₁.phase=s.phase ∧ regValue L.word t₁.basis=V ∧
      (∀q∈work L,t₁.basis q=false) ∧ (∀q,q∉L.word → t₁.basis q=s.basis q))
    (h₂ : t₂.phase=s.phase ∧ regValue L.word t₂.basis=V ∧
      (∀q∈work L,t₂.basis q=false) ∧ (∀q,q∉L.word → t₂.basis q=s.basis q)) : t₁=t₂ := by
  apply State.extensionality
  · exact h₁.1.trans h₂.1.symm
  · funext q
    by_cases hq : q∈L.word
    · exact (regValue_eq_iff L.word t₁.basis t₂.basis).mp (h₁.2.1.trans h₂.2.1.symm) q hq
    · exact (h₁.2.2.2 q hq).trans (h₂.2.2.2 q hq).symm

theorem fastCenter_state_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m n : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈work L,s.basis q=false) : run (fastCenter L) m s=run (center L) n s :=
  converted_state_eq L s _ _ _ (fastCenter_correct L hw hn x s m hx hc)
    (center_correct L hw hn x s n hx hc)

theorem fastCanonical_state_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m n : List Bool) (hx : regValue L.word s.basis=centerWord x)
    (hc : ∀q∈work L,s.basis q=false) : run (fastCanonical L) m s=run (canonical L) n s :=
  converted_state_eq L s _ _ _ (fastCanonical_correct L hw hn x s m hx hc)
    (canonical_correct L hw hn x s n hx hc)

theorem fastPredicate_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (fastPredicate L)=253 ∧ measurementCount (fastPredicate L)=252 := by
  have len := word_length L hw
  have cy : (L.carry.drop 3).length+1=(L.word.drop 3).length := by simp [hw.2,len]
  have h := compareConstantGe_counts (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8) cy
  simpa [fastPredicate,List.length_drop,len] using h

theorem fast_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (fastCenter L)=508 ∧ measurementCount (fastCenter L)=507 ∧
    toffoliCount (fastCanonical L)=508 ∧ measurementCount (fastCanonical L)=507 := by
  have w : L.word.length=256 := by simp [Layout.word,hw.1]
  have cy : L.carry.length=255 := hw.2
  have len : (correction L).length=L.word.length := by simp [correction,w]
  have hc : L.carry.length+1=L.word.length := by omega
  have a := mappedAdd_counts (correction L) L.word L.carry L.cin len hc
  have b := mappedSub_counts (correction L) L.word L.carry L.cin len hc
  have p := fastPredicate_counts L hw
  simp [fastCenter,fastCanonical,a.1,a.2,b.1,b.2,p.1,p.2,w,toffoliCount,measurementCount]

theorem fastPredicate_wires (L : Layout) : wires (fastPredicate L) ⊆ L.wires.toFinset := by
  have h := compareConstantLt_wires_subset (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8)
  intro q hq
  simp only [fastPredicate,compareConstantGe,wires_append,Finset.mem_union] at hq
  apply List.mem_toFinset.mpr
  rcases hq with hq|hq
  · have m := List.mem_toFinset.mp (h hq)
    have a : q∈L.word.drop 3 → q∈L.word := List.mem_of_mem_drop
    have b : q∈L.carry.drop 3 → q∈L.carry := List.mem_of_mem_drop
    simp only [Layout.wires,Layout.word,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false] at a b m ⊢
    tauto
  · simp [wires,Instr.wires] at hq
    simp [Layout.wires,hq]

theorem fast_support (L : Layout) :
    wires (fastCenter L) ⊆ L.wires.toFinset ∧ wires (fastCanonical L) ⊆ L.wires.toFinset := by
  have s := BalancedConvert.support L
  have p := fastPredicate_wires L
  simp only [center,canonical,wires_append,Finset.union_subset_iff] at s
  simp only [fastCenter,fastCanonical,wires_append,Finset.union_subset_iff]
  tauto

theorem fast_physical (L : Layout) (hn : L.wires.Nodup) :
    GatePhysical (fastCenter L) ∧ GatePhysical (fastCanonical L) := by
  have old := balancedConverters_physical L hn
  simp only [center,canonical,gatePhysical_append] at old
  have nd : ([L.cin,L.flag]++L.word.drop 3++L.carry.drop 3).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (layout_compare L hn) q
    have a := (List.drop_sublist 3 L.word).count_le q
    have b := (List.drop_sublist 3 L.carry).count_le q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cmp := compareConstantLt_physical (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8) nd
  have x : GatePhysical [Instr.X L.flag] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have fp : GatePhysical (fastPredicate L) := by
    simp only [fastPredicate,compareConstantGe,gatePhysical_append]
    exact ⟨cmp,x⟩
  simp only [fastCenter,fastCanonical,gatePhysical_append]
  tauto

open Challenge Baselines in
theorem fast_gateSlots_le (L : Layout) (hw : L.Widths) :
    gateSlots (fastCenter L) ≤ 12000 ∧ gateSlots (fastCanonical L) ≤ 12000 := by
  have hl : L.word.length = 256 := by simp [Layout.word,hw.1]
  have hc : (correction L).length = 256 := by simp [correction]
  have a := compareConstant_gateSlots_le (L.word.drop 3) (L.carry.drop 3) L.cin L.flag (cutoff/8)
  have c := mappedAdd_gateSlots_le (correction L) L.word L.carry L.cin
  have d := mappedSub_gateSlots_le (correction L) L.word L.carry L.cin
  simp only [List.length_drop,hl] at a
  rw [hc] at c
  rw [hc,hl] at d
  simp only [fastCenter,fastCanonical,fastPredicate,compareConstantGe,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]; omega

end ECDSAAdd.Arithmetic.BalancedConvert.LaneA
