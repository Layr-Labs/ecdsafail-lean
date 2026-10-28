import ECDSAAdd.Arithmetic.InverseScaleState

namespace ECDSAAdd.Arithmetic

/-- 原位写回r并清常量，518位历史跨中段存活，B归零供乘法借用。 -/
def inverseCompute (L : InverseLoopLayout) (q : Nat) : Program :=
  oneBitRecordLoop L.first 0 L.records ++ terminalConstants L q ++
  negativeEven L.compactNeg q ++ L.compactScaling.prepare q

/-- 缩放恢复、完整r恢复、常量写回后，才进入Kaliski逆轮。 -/
def inverseUncompute (L : InverseLoopLayout) (q : Nat) : Program :=
  L.compactScaling.restore q ++ restoreNegativeEven L.compactNeg q ++
  terminalConstants L q ++ oneBitRecordUnloop L.first 0 L.records

def inverseLoop (L : InverseLoopLayout) (q : Nat) : Program :=
  inverseCompute L q ++ copyRegister none L.middle.r L.out ++ inverseUncompute L q

def InverseInitial (L : InverseLoopLayout) (q a : Nat) (s : BasisState) : Prop :=
  (LoopState L.first (kaliskiInit q a) s ∧ OneBitRecordsValues L.records (List.replicate L.records.length (false,false)) s) ∧
    InverseExtra L 0 s

theorem InverseExtra.congr (L : InverseLoopLayout) (A : Nat) (s t : BasisState)
    (h : InverseExtra L A s) (he : ∀ w∈L.extra,t w=s w) : InverseExtra L A t := by
  have keep (r : List Wire) (hr : r ⊆ L.extra) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => he w (hr hw))
  exact ⟨(keep L.a (by intro w hw; simp [InverseLoopLayout.extra,hw])).trans h.1,
    (keep L.temp (by intro w hw; simp [InverseLoopLayout.extra,hw])).trans h.2.1,
    (keep L.arithmetic.wires (by intro w hw; simp [InverseLoopLayout.extra,hw])).trans h.2.2⟩

theorem inverseFirst_values (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (q a : Nat) (hodd : q%2=1) (hq0 : 0<q) (hq : q<2^L.first.low.length) (ha : a<q) (hcop : q.Coprime a) :
    Triple (InverseInitial L q a) (oneBitRecordLoop L.first 0 L.records)
      (InverseMiddle L (kaliskiStep^[512] (kaliskiInit q a)) (kaliskiCodes 512 (kaliskiInit q a)) 0) ∧
    Triple (InverseMiddle L (kaliskiStep^[512] (kaliskiInit q a)) (kaliskiCodes 512 (kaliskiInit q a)) 0)
      (oneBitRecordUnloop L.first 0 L.records) (InverseInitial L q a) := by
  have hd : 2≤L.first.data.width := by
    have hpos : 0<L.first.low.length := by
      by_contra hh
      have hz : L.first.low.length=0 := by omega
      simp [hz] at hq
      omega
    simp only [KaliskiRoundLayout.data,RoundDataLayout.width,List.length_append,List.length_cons,List.length_nil]
    omega
  have hh := oneBitRecordLoop_correct L.first L.records 0 q a (kaliskiInit q a) (L.first_nodup hnd) hw hd
    (by omega) (kaliski_round_count_init q a) (kaliski_init_invariant q a hq0 hcop) hodd hq hq (lt_trans ha hq)
  have hwire := oneBitRecordLoop_wires L.first L.records 0 hw hd
  have hne : L.records.isEmpty=false := by
    cases he : L.records with
    | nil => rw [he] at hn; simp at hn
    | cons r rs => rfl
  simp only [hne] at hwire
  have hdis := (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).2.2
  have frame (circ : Program) (hc : wires circ=(L.first.usedRecordTapeWires L.records).toFinset)
      (s t : BasisState) (he : ∀ w,w∉wires circ → s w=t w) (h : InverseExtra L 0 s) :
      InverseExtra L 0 t := by
    apply InverseExtra.congr L 0 s t h
    intro w hw
    apply (he w ?_).symm
    rw [hc]
    exact fun hh => List.disjoint_left.mp hdis ((L.first.usedRecordTapeWires_sublist L.records).subset (List.mem_toFinset.mp hh)) hw
  have hf := hh.1.frame (frame _ hwire.1)
  have hb := hh.2.frame (frame _ hwire.2)
  have hm : loopEndLayout L.first 512=L.middle := by rw [InverseLoopLayout.middle,hn]
  rw [hn,hm] at hf hb
  refine ⟨Triple.conseq (fun _ h => by simpa only [InverseInitial,hn] using h) hf ?_,
    Triple.conseq ?_ hb (fun _ h => by simpa only [InverseInitial,hn] using h)⟩
  · intro s h; exact (InverseMiddle.iff L _ _ 0 s).mpr ⟨h.1.1,h.1.2,h.2⟩
  · intro s h; have hh := (InverseMiddle.iff L _ _ 0 s).mp h; exact ⟨⟨hh.1,hh.2.1⟩,hh.2.2⟩

theorem inverseCompute_values (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hl : L.first.low.length=256) (hm : L.arithmetic.width=256)
    (_ha : L.a.length=257) (_ht : L.temp.length=257)
    (q a : Nat) (hq : q<2^256) (ho : q%16=15) (hx : a<q) (hcop : q.Coprime a) :
    let z := kaliskiStep^[512] (kaliskiInit q a)
    let cs := kaliskiCodes 512 (kaliskiInit q a)
    let N := (-(z.r : ZMod q)).val
    Triple (InverseInitial L q a) (inverseCompute L q) (InverseScaledMiddle L q z cs N) ∧
    Triple (InverseScaledMiddle L q z cs N) (inverseUncompute L q) (InverseInitial L q a) := by
  dsimp only
  letI : NeZero q := ⟨by omega⟩
  let z := kaliskiStep^[512] (kaliskiInit q a)
  let cs := kaliskiCodes 512 (kaliskiInit q a)
  let N := (-(z.r : ZMod q)).val
  have hq1 : 1<q := by omega
  have hx0 : 0<a := by
    by_contra hh
    have he : a=0 := by omega
    simp [he,Nat.Coprime] at hcop
    omega
  have ht := kaliski_terminal_values q a 256 hq1 (by omega) hq hx0 hx hcop
  change z.u=1 ∧ z.v=0 ∧ z.s=q ∧ 0<z.r ∧ z.r<2*q ∧ z.r%2=0 at ht
  have hz : z=⟨1,0,z.r,q,z.k⟩ := by
    cases hz0 : z
    simp only [KState.mk.injEq]
    exact ⟨by simpa only [hz0] using ht.1,by simpa only [hz0] using ht.2.1,True.intro,
      by simpa only [hz0] using ht.2.2.1,True.intro⟩
  have hfirst := inverseFirst_values L hnd hn hw q a (by omega) (by omega) (by simpa only [hl] using hq) hx hcop
  have hc := compactConstants_values L hnd hl q z.r z.k hq cs
  have hg := compactNeg_values L hnd hm hl q z.r z.k hq (by omega)
    ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 cs
  have hs := compactScale_values L hnd hm hl hw q z.k N ho hq (ZMod.val_lt _) cs
  have hcs : Triple (InverseMiddle L z cs 0) (terminalConstants L q) (CompactReady L z.k z.r cs) := by
    rw [congrArg (fun zz => InverseMiddle L zz cs 0) hz]
    exact hc.1
  have hcb : Triple (CompactReady L z.k z.r cs) (terminalConstants L q) (InverseMiddle L z cs 0) := by
    rw [congrArg (fun zz => InverseMiddle L zz cs 0) hz]
    exact hc.2
  exact ⟨((hfirst.1.seq hcs).seq hg.1).seq hs.1,((hs.2.seq hg.2).seq hcb).seq hfirst.2⟩

end ECDSAAdd.Arithmetic
