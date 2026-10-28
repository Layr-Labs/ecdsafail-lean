import ECDSAAdd.Arithmetic.ValueNarrow

namespace ECDSAAdd.Arithmetic

/-- 两位记录逐轮独占；共享字与计数银行交替复用。 -/
-- Width envelope: round i runs only on the low `valueWidth L.data.width i` data bits.
def valueLoop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => valueRound ((L.withRecord r).narrow (valueWidth L.data.width i)) i ++
      valueLoop L.swapCounter (i+1) rs

def valueUnloop (L : KaliskiRoundLayout) (i : Nat) : List RoundRecord → Program
  | [] => []
  | r::rs => valueUnloop L.swapCounter (i+1) rs ++
      valueUnround ((L.withRecord r).narrow (valueWidth L.data.width i)) i

/-- Sum of the data widths of n consecutive rounds starting at round i; resources are summed per round. -/
def valueWidthSum (w i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => valueWidth w i+valueWidthSum w (i+1) n

theorem valueWidth_bounds (w i : Nat) (hd : 2≤w) : 2≤valueWidth w i ∧ valueWidth w i≤w := by
  simp only [valueWidth]
  omega

/-- secp256k1 instance: width sum for 257-bit data over 512 rounds (full width would be 131,584). -/
theorem valueWidthSum_257 : valueWidthSum 257 0 512=98689 := by decide +kernel

theorem valueWidth_full (w i : Nat) (hd : 2≤w) (hi : i+w≤512) : valueWidth w i=w := by
  simp only [valueWidth]
  omega

def valueCodes : Nat → KState → List (Bool×Bool)
  | 0,_ => []
  | n+1,z => kaliskiCode z::valueCodes n (valueKStep z)

def KaliskiRoundLayout.valueSharedWires (L : KaliskiRoundLayout) : List Wire :=
  [L.done,L.oddWork,L.bothWork,L.compareCin]++L.data.valueUsedWires++L.counter.wires

def KaliskiRoundLayout.valueTapeWires (L : KaliskiRoundLayout) (rs : List RoundRecord) : List Wire :=
  rs.flatMap RoundRecord.wires++L.valueSharedWires

theorem KaliskiRoundLayout.valueTapeWires_sublist (L : KaliskiRoundLayout) (rs : List RoundRecord) :
    (L.valueTapeWires rs).Sublist (L.tapeWires rs) :=
  ((L.data.valueUsedWires_sublist.append_left _).append_right _).append_left _

private theorem usedRecord_perm (L : KaliskiRoundLayout) (r : RoundRecord) :
    (L.withRecord r).valueUsedWires.Perm (r.wires++L.valueSharedWires) := by
  apply List.perm_iff_count.mpr
  intro w
  simp [KaliskiRoundLayout.valueUsedWires,KaliskiRoundLayout.withRecord,KaliskiRoundLayout.valueSharedWires,
    RoundRecord.wires,List.count_cons,KaliskiRoundLayout.data,KaliskiRoundLayout.counter]
  omega

private theorem usedShared_swap (L : KaliskiRoundLayout) :
    L.swapCounter.valueSharedWires.Perm L.valueSharedWires := by
  change (_++L.swapCounter.data.valueUsedWires++L.swapCounter.counter.wires).Perm
    (_++L.data.valueUsedWires++L.counter.wires)
  rw [L.swapCounter_data,L.swapCounter_counter]
  exact List.Perm.append_left _ L.counter.swapCounter_perm

theorem valueLoop_counts (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hnd : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    toffoliCount (valueLoop L i rs)=7*valueWidthSum L.data.width i rs.length+33*rs.length ∧
    measurementCount (valueLoop L i rs)=4*valueWidthSum L.data.width i rs.length+29*rs.length ∧
    toffoliCount (valueUnloop L i rs)=7*valueWidthSum L.data.width i rs.length+33*rs.length ∧
    measurementCount (valueUnloop L i rs)=4*valueWidthSum L.data.width i rs.length+29*rs.length := by
  induction rs generalizing L i with
  | nil => simp [valueLoop,valueUnloop,valueWidthSum,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hb := valueWidth_bounds L.data.width i hd
    have hW : (L.withRecord r).wires.Nodup := L.withRecord_nodup r rs hnd
    have hN := ((L.withRecord r).narrow_nodup _ (by omega) hb.2 hW).1
    have hr := valueRound_counts ((L.withRecord r).narrow (valueWidth L.data.width i)) hN hw i
    rw [(L.withRecord r).narrow_width _ (by omega) hb.2] at hr
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) (L.tail_nodup r rs hnd) hnw hd
    change _=7*valueWidthSum L.data.width (i+1) rs.length+33*rs.length ∧
      _=4*valueWidthSum L.data.width (i+1) rs.length+29*rs.length ∧
      _=7*valueWidthSum L.data.width (i+1) rs.length+33*rs.length ∧
      _=4*valueWidthSum L.data.width (i+1) rs.length+29*rs.length at ht
    simp only [valueLoop,valueUnloop,toffoliCount_append,measurementCount_append,hr.1,hr.2.1,
      hr.2.2.1,hr.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,List.length_cons,valueWidthSum]
    refine ⟨?_,?_,?_,?_⟩ <;> ring

/-- A narrowed round touches a subset of the full-width round support; record and control wires are unchanged. -/
private theorem narrow_used_sublist (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).valueUsedWires.Sublist L.valueUsedWires := by
  have hd : (L.narrow m).data.valueUsedWires.Sublist L.data.valueUsedWires := by
    rw [L.narrow_data m h1 hm]
    apply List.Sublist.cons₂
    conv_rhs => rw [← List.take_append_drop m L.data.bits]
    rw [List.flatMap_append]
    exact List.sublist_append_left _ _
  exact (hd.append_left _).append_right _

/-- Support of the narrowed round i: contained in the full-width round support and covering both record wires of the round. -/
theorem valueNarrowRound_wires (L : KaliskiRoundLayout) (r : RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    (wires (valueRound ((L.withRecord r).narrow (valueWidth L.data.width i)) i)=
        ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset ∧
      wires (valueUnround ((L.withRecord r).narrow (valueWidth L.data.width i)) i)=
        ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset) ∧
    ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset ⊆
        (L.withRecord r).valueUsedWires.toFinset ∧
    (r.wires).toFinset ⊆ ((L.withRecord r).narrow (valueWidth L.data.width i)).valueUsedWires.toFinset := by
  have hb := valueWidth_bounds L.data.width i hd
  have hnd : 2≤((L.withRecord r).narrow (valueWidth L.data.width i)).data.width := by
    rw [(L.withRecord r).narrow_width _ (by omega) hb.2]; exact hb.1
  refine ⟨valueRound_wires ((L.withRecord r).narrow (valueWidth L.data.width i)) hw hnd i,?_,?_⟩
  · intro w hm
    exact List.mem_toFinset.mpr ((narrow_used_sublist (L.withRecord r) _ (by omega) hb.2).subset
      (List.mem_toFinset.mp hm))
  · intro w hm
    apply List.mem_toFinset.mpr
    simp only [List.mem_toFinset,RoundRecord.wires,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- Any start round: loop support is contained in the shared layout plus the record tape, and touches every record wire. -/
theorem valueLoop_wires_subset (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    (wires (valueLoop L i rs)⊆(L.valueTapeWires rs).toFinset ∧
      wires (valueUnloop L i rs)⊆(L.valueTapeWires rs).toFinset) ∧
    ((rs.flatMap RoundRecord.wires).toFinset⊆wires (valueLoop L i rs) ∧
      (rs.flatMap RoundRecord.wires).toFinset⊆wires (valueUnloop L i rs)) := by
  induction rs generalizing L i with
  | nil => simp [valueLoop,valueUnloop,wires]
  | cons r rs ih =>
    have hr := valueNarrowRound_wires L r i hw hd
    have hp : (L.withRecord r).valueUsedWires.toFinset ⊆ (r.wires++L.valueSharedWires).toFinset := by
      intro w hm
      exact List.mem_toFinset.mpr ((usedRecord_perm L r).mem_iff.mp (List.mem_toFinset.mp hm))
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) hnw hd
    have hs : L.swapCounter.valueSharedWires.toFinset=L.valueSharedWires.toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedShared_swap L).mem_iff (a:=w)
    have htape : (L.swapCounter.valueTapeWires rs).toFinset ⊆ (L.valueTapeWires (r::rs)).toFinset := by
      intro w hm
      simp only [KaliskiRoundLayout.valueTapeWires,List.toFinset_append,Finset.mem_union,hs] at hm ⊢
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union]
      tauto
    have hhead : (r.wires++L.valueSharedWires).toFinset ⊆ (L.valueTapeWires (r::rs)).toFinset := by
      intro w hm
      simp only [KaliskiRoundLayout.valueTapeWires,List.flatMap_cons,List.toFinset_append,
        Finset.mem_union] at hm ⊢
      tauto
    simp only [valueLoop,valueUnloop,wires_append,hr.1.1,hr.1.2]
    refine ⟨⟨Finset.union_subset ((hr.2.1.trans hp).trans hhead) (ht.1.1.trans htape),
      Finset.union_subset (ht.1.2.trans htape) ((hr.2.1.trans hp).trans hhead)⟩,?_,?_⟩
    · intro w hm
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union] at hm
      rcases hm with hm|hm
      · exact Finset.mem_union_left _ (hr.2.2 hm)
      · exact Finset.mem_union_right _ (ht.2.1 hm)
    · intro w hm
      simp only [List.flatMap_cons,List.toFinset_append,Finset.mem_union] at hm
      rcases hm with hm|hm
      · exact Finset.mem_union_right _ (hr.2.2 hm)
      · exact Finset.mem_union_left _ (ht.2.2 hm)

/-- 空循环没有线路；非空循环恰好使用共享布局和整个两位记录带。 -/
-- With the width envelope, the equality needs a full-width first round (`i+L.data.width≤512`).
theorem valueLoop_wires (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) (hi : i+L.data.width≤512) :
    wires (valueLoop L i rs)=(if rs.isEmpty then ∅ else (L.valueTapeWires rs).toFinset) ∧
    wires (valueUnloop L i rs)=(if rs.isEmpty then ∅ else (L.valueTapeWires rs).toFinset) := by
  cases rs with
  | nil => simp [valueLoop,valueUnloop,wires]
  | cons r rs =>
    have hfull : (L.withRecord r).narrow (valueWidth L.data.width i)=L.withRecord r := by
      rw [valueWidth_full _ _ hd hi]
      exact (L.withRecord r).narrow_full
    have hr := valueRound_wires (L.withRecord r) hw hd i
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := valueLoop_wires_subset L.swapCounter rs (i+1) hnw hd
    have hp : (L.withRecord r).valueUsedWires.toFinset=(r.wires++L.valueSharedWires).toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedRecord_perm L r).mem_iff (a:=w)
    have hs : L.swapCounter.valueSharedWires.toFinset=L.valueSharedWires.toFinset := by
      ext w; simpa only [List.mem_toFinset] using (usedShared_swap L).mem_iff (a:=w)
    have htape : (L.swapCounter.valueTapeWires rs).toFinset=
        (rs.flatMap RoundRecord.wires).toFinset ∪ L.valueSharedWires.toFinset := by
      simp only [KaliskiRoundLayout.valueTapeWires,List.toFinset_append,hs]
    rw [htape] at ht
    simp only [valueLoop,valueUnloop,wires_append,hfull,hr.1,hr.2,hp,List.isEmpty_cons,
      Bool.false_eq_true,if_false,KaliskiRoundLayout.valueTapeWires,List.flatMap_cons,List.toFinset_append]
    obtain ⟨⟨h1,h2⟩,h3,h4⟩ := ht
    generalize wires (valueLoop L.swapCounter (i+1) rs)=T1 at h1 h3 ⊢
    generalize wires (valueUnloop L.swapCounter (i+1) rs)=T2 at h2 h4 ⊢
    generalize (rs.flatMap RoundRecord.wires).toFinset=R at h1 h2 h3 h4 ⊢
    generalize L.valueSharedWires.toFinset=Sh at h1 h2 ⊢
    generalize r.wires.toFinset=A
    constructor
    · ext w
      have a1 := @h1 w
      have a3 := @h3 w
      simp only [Finset.mem_union] at a1 ⊢
      constructor
      · rintro ((h|h)|h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · rcases a1 h with h'|h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
      · rintro ((h|h)|h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (a3 h)
        · exact Or.inl (Or.inr h)
    · ext w
      have a2 := @h2 w
      have a4 := @h4 w
      simp only [Finset.mem_union] at a2 ⊢
      constructor
      · rintro (h|(h|h))
        · rcases a2 h with h'|h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h|h)|h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (a4 h)
        · exact Or.inr (Or.inr h)

theorem valueLoop_qubits (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hnd : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width)
    (hi : i+L.data.width≤512) (hne : rs≠[]) :
    qubitCount (valueLoop L i rs)=5*L.data.width+46+2*rs.length ∧
    qubitCount (valueUnloop L i rs)=5*L.data.width+46+2*rs.length := by
  have ht (rs : List RoundRecord) : (rs.flatMap RoundRecord.wires).length=2*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [RoundRecord.wires,ih]; omega
  have hdw (bs : List RoundBit) : (bs.flatMap RoundBit.valueUsedWires).length=5*bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [RoundBit.valueUsedWires,ih]; omega
  have hlen : (L.valueTapeWires rs).length=5*L.data.width+46+2*rs.length := by
    simp only [KaliskiRoundLayout.valueTapeWires,KaliskiRoundLayout.valueSharedWires,List.length_append,ht,
      List.length_cons,List.length_nil,RoundDataLayout.valueUsedWires,hdw,AdderLayout.wires,addWires_length]
    change L.counter.bits.length=10 at hw
    simp only [RoundDataLayout.width]
    omega
  have h := valueLoop_wires L rs i hw hd hi
  have he : rs.isEmpty=false := by cases rs <;> simp_all
  simp only [he,Bool.false_eq_true,if_false] at h
  simp only [qubitCount,h.1,h.2,List.toFinset_card_of_nodup ((L.valueTapeWires_sublist rs).nodup hnd),hlen,and_self]

end ECDSAAdd.Arithmetic
