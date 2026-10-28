import ECDSAAdd.Arithmetic.MontCounts

namespace ECDSAAdd.Arithmetic

private theorem montLookup_bounds (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hw : L.Widths) (ha : addr.length=4) :
    (addr++L.scratch).toFinset ⊆ wires (montLookup L addr K) ∧
    wires (montLookup L addr K) ⊆ (addr++L.scratch++L.table).toFinset := by
  cases addr with
  | nil => simp at ha
  | cons a rest =>
    have hr : rest.length=3 := by simpa using ha
    constructor
    · simpa [montLookup] using lookup_core_wires a rest L.scratch L.table (fun d => d*K) hr hw.scratch
    · simpa [montLookup] using lookup_wires_subset a rest L.scratch L.table (fun d => d*K)

theorem montLookupUpdate_wires (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hw : L.Widths) (ha : addr.length=4) :
    wires (montLookupAdd L addr K)=(L.cin::addr++L.scratch++L.table++L.acc++L.carry).toFinset ∧
    wires (montLookupSub L addr K)=(L.cin::addr++L.scratch++L.table++L.acc++L.carry).toFinset := by
  have hl := montLookup_bounds L addr K hw ha
  have hadd := addInPlace_wires L.table L.acc L.carry L.cin (hw.table.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  have hsub := subInPlace_wires L.table L.acc L.carry L.cin (hw.table.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  simp only [montLookupAdd,montLookupSub,wires_append,hadd,hsub]
  generalize he : wires (montLookup L addr K)=S at hl ⊢
  constructor <;> ext w
  all_goals
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    have lo := @hl.1 w
    have up := @hl.2 w
    simp only [List.mem_toFinset,List.mem_append] at lo up
    tauto


private theorem rotateBits_wires_subset (r : List Wire) (k : Nat) :
    wires (rotateRightBits r k) ⊆ r.toFinset ∧ wires (rotateLeftBits r k) ⊆ r.toFinset := by
  have hright : wires (rotateRight r) ⊆ r.toFinset := by rw [(rotate_wires r).1]; split <;> simp
  have hleft : wires (rotateLeft r) ⊆ r.toFinset := by rw [(rotate_wires r).2]; split <;> simp
  induction k with
  | zero => simp [rotateRightBits,rotateLeftBits,wires]
  | succ k ih =>
    simp only [rotateRightBits,rotateLeftBits,wires_append]
    exact ⟨Finset.union_subset hright ih.1,Finset.union_subset hleft ih.2⟩

theorem montReduce_wires (L : MontStageLayout) (p i : Nat) (hw : L.Widths) (hi : i<64) :
    wires (montReduce L p i)=(L.cin::L.record i++L.scratch++L.table++L.acc++L.carry).toFinset ∧
    wires (montRestoreReduce L p i)=(L.cin::L.record i++L.scratch++L.table++L.acc++L.carry).toFinset := by
  have hl := montLookupUpdate_wires L (L.record i) p hw (L.record_length hw i hi)
  have hc := copyRegister_wires none (L.acc.take 4) (L.record i) (by simp [hw.acc,L.record_length hw i hi])
  have hn : L.acc.take 4≠[] := by
    intro h
    have hlen := congrArg List.length h
    simp [hw.acc] at hlen
  simp only [Option.toList_none,List.nil_append,List.isEmpty_iff,hn,if_false] at hc
  have hr := rotateBits_wires_subset L.acc 4
  let S := (L.cin::L.record i++L.scratch++L.table++L.acc++L.carry).toFinset
  have hacc : L.acc.toFinset ⊆ S := by
    intro w h
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hcopy : wires (copyRegister none (L.acc.take 4) (L.record i)) ⊆ S := by
    rw [hc]
    intro w h
    simp only [List.mem_toFinset,List.mem_append] at h
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append]
    rcases h with h|h
    · have ha := List.mem_of_mem_take h
      tauto
    · tauto
  have hright := hr.1.trans hacc
  have hleft := hr.2.trans hacc
  change _=S ∧ _=S
  constructor
  · rw [montReduce,wires_append,wires_append,hl.1,Finset.union_eq_right.mpr hcopy,
      Finset.union_eq_left.mpr hright]
  · rw [montRestoreReduce,wires_append,wires_append,hl.2,Finset.union_eq_right.mpr hleft,
      Finset.union_eq_left.mpr hcopy]


private theorem mont_slice_map (r : List Wire) (start k : Nat) (fallback : Wire)
    (hk : start+k≤r.length) :
    (List.range k).map (fun j => r.getD (start+j) fallback)=(r.drop start).take k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ,List.map_append,ih (by omega),List.map_singleton,
      List.take_succ_eq_append_getElem (by simp only [List.length_drop]; omega)]
    congr 1
    simp [List.getD,List.getElem?_eq_getElem (show start+k<r.length by omega)]

private theorem mont_source_mem (L : MontStageLayout) (x : List Wire) (j : Nat) (w : Wire) :
    w∈L.source x j ↔ w∈x.take 256 ∨ w∈L.pad := by
  have h := List.take_append_drop j L.pad
  have hm : w∈L.pad.take j ∨ w∈L.pad.drop j ↔ w∈L.pad := by rw [←List.mem_append,h]
  simp only [MontStageLayout.source,List.mem_append]
  tauto

/-- 四个受控加减的精确支持，包含实际使用的五根零扩展位。 -/
theorem montDigit_wires (L : MontStageLayout) (x y : List Wire) (i : Nat)
    (hw : L.Widths) (hx : 256≤x.length) (hi : 4*i+4≤y.length) :
    wires (montAddDigit L x y i)=((y.drop (4*i)).take 4++[L.cin]++x.take 256++L.pad++L.mask++L.acc++L.carry).toFinset ∧
    wires (montSubDigit L x y i)=((y.drop (4*i)).take 4++[L.cin]++x.take 256++L.pad++L.mask++L.acc++L.carry).toFinset := by
  have hbit (j : Nat) := measuredMaskedInPlace_wires (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin
    (show (L.source x j).length=L.mask.length by
      simp only [MontStageLayout.source,List.length_append,List.length_take,List.length_drop,hw.pad,hw.mask,Nat.min_eq_left hx]; omega)
    (hw.mask.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  rw [←mont_slice_map y (4*i) 4 L.flag hi]
  simp only [montAddDigit,montSubDigit,show List.range 4=[0,1,2,3] from rfl,
    show ([0,1,2,3] : List Nat).reverse=[3,2,1,0] from rfl,
    List.flatMap_cons,List.flatMap_nil,wires_append,(hbit _).1,(hbit _).2,wires]
  constructor <;> ext w <;>
    simp only [Finset.mem_union,Finset.notMem_empty,List.mem_toFinset,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,mont_source_mem] <;> tauto



theorem montWindow_wires (L : MontStageLayout) (x y : List Wire) (p i : Nat)
    (hw : L.Widths) (hx : 256≤x.length) (hy : 256≤y.length) (hi : i<64) :
    wires (montWindow L x y p i)=(x.take 256++(y.drop (4*i)).take 4++L.record i++L.acc++L.work).toFinset ∧
    wires (montRestoreWindow L x y p i)=(x.take 256++(y.drop (4*i)).take 4++L.record i++L.acc++L.work).toFinset := by
  have hd := montDigit_wires L x y i hw hx (by omega)
  have hr := montReduce_wires L p i hw hi
  simp only [montWindow,montRestoreWindow,wires_append,hd.1,hd.2,hr.1,hr.2]
  constructor <;> ext w <;> simp only [MontStageLayout.work,Finset.mem_union,List.mem_toFinset,
    List.mem_append,List.mem_cons,List.not_mem_nil] <;> tauto

theorem constWindow_wires (L : MontStageLayout) (y : List Wire) (p K i : Nat)
    (hw : L.Widths) (hy : 256≤y.length) (hi : i<64) :
    wires (constMontWindow L y p K i)=((y.drop (4*i)).take 4++L.record i++L.acc++L.table++L.carry++[L.cin]++L.scratch).toFinset ∧
    wires (constMontRestoreWindow L y p K i)=((y.drop (4*i)).take 4++L.record i++L.acc++L.table++L.carry++[L.cin]++L.scratch).toFinset := by
  have hl : ((y.drop (4*i)).take 4).length=4 := by simp only [List.length_take,List.length_drop]; omega
  have hd := montLookupUpdate_wires L ((y.drop (4*i)).take 4) K hw hl
  have hr := montReduce_wires L p i hw hi
  simp only [constMontWindow,constMontRestoreWindow,wires_append,hd.1,hd.2,hr.1,hr.2]
  constructor <;> ext w <;> simp only [Finset.mem_union,List.mem_toFinset,
    List.mem_append,List.mem_cons,List.not_mem_nil] <;> tauto



theorem montRounds_wires (L : MontStageLayout) (x y : List Wire) (p k : Nat)
    (hw : L.Widths) (hx : 256≤x.length) (hy : 256≤y.length) (hk : k≤64) :
    wires (montPrepareRounds L x y p k)=(if k=0 then ∅ else (x.take 256++y.take (4*k)++L.history.take (4*k)++L.acc++L.work).toFinset) ∧
    wires (montRestoreRounds L x y p k)=(if k=0 then ∅ else (x.take 256++y.take (4*k)++L.history.take (4*k)++L.acc++L.work).toFinset) := by
  induction k with
  | zero => simp [montPrepareRounds,montRestoreRounds,wires]
  | succ k ih =>
    have h := ih (by omega)
    have hwin := montWindow_wires L x y p k hw hx hy (by omega)
    change wires (montPrepareRounds L x y p k ++ montWindow L x y p k)=_ ∧
      wires (montRestoreWindow L x y p k ++ montRestoreRounds L x y p k)=_
    simp only [wires_append,h.1,h.2,hwin.1,hwin.2,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    have hychunk := @List.take_add Wire y (4*k) 4
    have hhchunk := @List.take_add Wire L.history (4*k) 4
    rw [show 4*(k+1)=4*k+4 by omega,hychunk,hhchunk]
    clear ih h hwin
    by_cases hz : k=0
    · subst k
      simp only [if_true,Nat.mul_zero,List.take_zero,List.drop_zero,MontStageLayout.record,
        List.nil_append,Finset.empty_union,Finset.union_empty]
      trivial
    · simp only [if_neg hz]
      constructor <;> ext w <;> simp only [MontStageLayout.record,Finset.mem_union,List.mem_toFinset,List.mem_append] <;> tauto


theorem constRounds_wires (L : MontStageLayout) (y : List Wire) (p K k : Nat)
    (hw : L.Widths) (hy : 256≤y.length) (hk : k≤64) :
    wires (constPrepareRounds L y p K k)=(if k=0 then ∅ else (y.take (4*k)++L.history.take (4*k)++L.acc++L.table++L.carry++[L.cin]++L.scratch).toFinset) ∧
    wires (constRestoreRounds L y p K k)=(if k=0 then ∅ else (y.take (4*k)++L.history.take (4*k)++L.acc++L.table++L.carry++[L.cin]++L.scratch).toFinset) := by
  induction k with
  | zero => simp [constPrepareRounds,constRestoreRounds,wires]
  | succ k ih =>
    have h := ih (by omega)
    have hwin := constWindow_wires L y p K k hw hy (by omega)
    change wires (constPrepareRounds L y p K k ++ constMontWindow L y p K k)=_ ∧
      wires (constMontRestoreWindow L y p K k ++ constRestoreRounds L y p K k)=_
    simp only [wires_append,h.1,h.2,hwin.1,hwin.2,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    have hychunk := @List.take_add Wire y (4*k) 4
    have hhchunk := @List.take_add Wire L.history (4*k) 4
    rw [show 4*(k+1)=4*k+4 by omega,hychunk,hhchunk]
    clear ih h hwin
    by_cases hz : k=0
    · subst k
      simp only [if_true,Nat.mul_zero,List.take_zero,List.drop_zero,MontStageLayout.record,
        List.nil_append,Finset.empty_union,Finset.union_empty]
      trivial
    · simp only [if_neg hz]
      constructor <;> ext w <;> simp only [MontStageLayout.record,Finset.mem_union,List.mem_toFinset,List.mem_append] <;> tauto


private theorem montConstant_wires (L : MontStageLayout) (p : Nat) (hw : L.Widths) :
    wires (montConstantAdd L p)=(L.cin::L.table++L.acc++L.carry).toFinset ∧
    wires (montConstantSub L p)=(L.cin::L.table++L.acc++L.carry).toFinset := by
  have ha := addInPlace_wires L.table L.acc L.carry L.cin (hw.table.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  have hs := subInPlace_wires L.table L.acc L.carry L.cin (hw.table.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  have hx : wires (xorConstant L.table p) ⊆ (L.cin::L.table++L.acc++L.carry).toFinset := by
    intro w h
    have ht := xorConstant_wires_subset L.table p h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at ht ⊢
    tauto
  simp only [List.cons_append] at hx
  simp only [montConstantAdd,montConstantSub,wires_append,ha,hs,List.cons_append,
    Finset.union_eq_right.mpr hx,Finset.union_eq_left.mpr hx,and_self]

private theorem normalize_support_union (S A B : Finset Wire) (f h : Wire)
    (hh : h∈S) (ha : A⊆insert f S) (hb : B⊆insert f S) :
    (S∪{h,f})∪A=insert f S ∧ (B∪{h,f})∪S=insert f S := by
  constructor <;> ext w
  all_goals
    have hhigh : w=h → w∈S := fun he => he ▸ hh
    have ha' := @ha w
    have hb' := @hb w
    simp only [Finset.mem_insert] at ha' hb'
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto

theorem montNormalize_wires (L : MontStageLayout) (p : Nat) (hw : L.Widths) :
    wires (montNormalize L p)=(L.flag::L.cin::L.table++L.acc++L.carry).toFinset ∧
    wires (montDenormalize L p)=(L.flag::L.cin::L.table++L.acc++L.carry).toFinset := by
  have hc := montConstant_wires L p hw
  have hm := maskedConst_wires_subset L.flag L.table L.acc L.carry L.cin p
    (hw.table.trans hw.acc.symm) (by simp [hw.carry,hw.acc])
  have hh : L.acc.getD 260 L.flag ∈ L.acc := mont_bit_mem _ _ _ (by simp [hw.acc])
  have hcx : wires [.CX (L.acc.getD 260 L.flag) L.flag]={L.acc.getD 260 L.flag,L.flag} := by simp [wires,Instr.wires]
  simp only [montNormalize,montDenormalize,wires_append,hc.1,hc.2,hcx]
  simp only [List.cons_append,List.toFinset_cons] at hm ⊢
  exact normalize_support_union _ _ _ L.flag (L.acc.getD 260 L.flag)
    (by simp only [Finset.mem_insert,List.mem_toFinset,List.mem_append]; tauto) hm.1 hm.2



theorem montStage_wires (L : MontStageLayout) (x y : List Wire) (p : Nat)
    (hw : L.Widths) (hx : 256≤x.length) (hy : 256≤y.length) :
    wires (montPrepare L x y p)=(x.take 256++y.take 256++L.wires).toFinset ∧
    wires (montRestore L x y p)=(x.take 256++y.take 256++L.wires).toFinset := by
  have hr := montRounds_wires L x y p 64 hw hx hy (by omega)
  have hn := montNormalize_wires L p hw
  simp only [montPrepare,montRestore,wires_append,hr.1,hr.2,hn.1,hn.2,
    show (64 : Nat)≠0 by omega,if_false,show 4*64=256 from rfl,
    List.take_of_length_le (show L.history.length≤256 by simp [hw.history])]
  clear hr hn
  constructor <;> ext w <;> simp only [MontStageLayout.wires,MontStageLayout.work,
    Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] <;> tauto

theorem constStage_wires (L : MontStageLayout) (y : List Wire) (p K : Nat)
    (hw : L.Widths) (hy : 256≤y.length) :
    wires (constPrepare L y p K)=(y.take 256++L.acc++L.history++[L.flag]++L.table++L.carry++[L.cin]++L.scratch).toFinset ∧
    wires (constRestore L y p K)=(y.take 256++L.acc++L.history++[L.flag]++L.table++L.carry++[L.cin]++L.scratch).toFinset := by
  have hr := constRounds_wires L y p K 64 hw hy (by omega)
  have hn := montNormalize_wires L p hw
  simp only [constPrepare,constRestore,wires_append,hr.1,hr.2,hn.1,hn.2,
    show (64 : Nat)≠0 by omega,if_false,show 4*64=256 from rfl,
    List.take_of_length_le (show L.history.length≤256 by simp [hw.history])]
  clear hr hn
  constructor <;> ext w <;> simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.not_mem_nil] <;> tauto

/-- 输出字和 X 的高位从未被 P/Q 触及；实际支持为两个输入低256位和全部工作区。 -/
theorem montPQ_wires (M : MontLayout) (p : Nat) (hw : M.Widths) :
    wires (montP M p)=(M.x.take 256++M.y++M.work).toFinset ∧
    wires (montQ M p)=(M.x.take 256++M.y++M.work).toFinset := by
  have h1 := montStage_wires M.first M.x M.y p hw.first (by simp [hw.x]) (by simp [hw.y])
  have h2 := constStage_wires M.second M.a p (montgomeryConversion p) (M.second_widths hw) (by simp [MontLayout.a,hw.first.acc])
  simp only [montP,montQ,wires_append,h1.1,h1.2,h2.1,h2.2,
    List.take_of_length_le (show M.y.length≤256 by simp [hw.y])]
  clear h1 h2
  constructor <;> ext w
  all_goals
    have ha : w∈M.a.take 256 → w∈M.first.acc := List.mem_of_mem_take
    simp only [MontLayout.work,MontLayout.activeA,MontLayout.activeZ,MontLayout.shared,
      MontLayout.a,MontLayout.hA,MontLayout.fA,MontLayout.second,MontStageLayout.wires,MontStageLayout.work,
      Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto

end ECDSAAdd.Arithmetic
