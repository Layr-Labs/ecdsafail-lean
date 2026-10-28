import ECDSAAdd.Arithmetic.SquareReduce

namespace ECDSAAdd.Arithmetic

/-- 常数受控加减的完整逐线规格；临时常数及进位均归零。 -/
theorem maskedConst_frame (sub : Bool) (c cin : Wire) (T y carry : List Wire)
    (hn : (c::cin::(T++y++carry)).Nodup) (hT : T.length=y.length)
    (hc : carry.length+1=y.length) (K : Nat) (hK : K<2^T.length)
    (base : BasisState) (hz : regValue (T++carry) base=0) (hi : base cin=false) (A : Nat) :
    Triple (SquareFrame y base A)
      (if sub then maskedSubConst c T y carry cin K else maskedAddConst c T y carry cin K)
      (SquareFrame y base (if sub then (A+2^y.length-(if base c then K else 0))%2^y.length
        else (A+(if base c then K else 0))%2^y.length)) := by
  have outside (w : Wire) (hw : w∈c::cin::(T++carry)) : w∉y := by
    intro hy
    have h := List.nodup_iff_count.mp hn w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at h h1
    omega
  intro s m h
  have keep (w : Wire) (hw : w∈c::cin::(T++carry)) := h.2 w (outside w hw)
  have ct : s.basis c=base c := keep c (by simp)
  have ci : s.basis cin=false := (keep cin (by simp)).trans hi
  have clean (r : List Wire) (hr : r⊆T++carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hw
    have hh := hr hw
    rw [keep w (by simp only [List.mem_cons,List.mem_append] at hh ⊢; tauto)]
    exact (regValue_zero _ _).mp hz w hh
  have tz := clean T (by simp)
  have cz := clean carry (by simp)
  have frame (prg : Program)
      (ws : wires prg⊆(c::cin::(T++y++carry)).toFinset)
      (pc : (run prg m s).basis c=base c) (pi : (run prg m s).basis cin=false)
      (pt : regValue T (run prg m s).basis=0) (pk : regValue carry (run prg m s).basis=0) :
      ∀w,w∉y → (run prg m s).basis w=base w := by
    intro w hw
    by_cases ht : w∈T
    · exact ((regValue_zero _ _).mp pt w ht).trans ((regValue_zero _ _).mp hz w (by simp [ht])).symm
    by_cases hk : w∈carry
    · exact ((regValue_zero _ _).mp pk w hk).trans ((regValue_zero _ _).mp hz w (by simp [hk])).symm
    by_cases hcw : w=c
    · subst w; exact pc
    by_cases hiw : w=cin
    · subst w; exact pi.trans hi.symm
    have ho : w∉wires prg := fun hh => by
      have hm := ws hh
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm
      tauto
    exact (run_preserves_outside prg m s w ho).trans (h.2 w hw)
  cases sub
  · have specs := maskedAddConst_spec c cin T y carry hn hT hc K hK (base c) A s m ⟨⟨⟨⟨ct,tz⟩,h.1⟩,ci⟩,cz⟩
    simp only [Bool.false_eq_true,↓reduceIte]
    exact ⟨specs.1,specs.2.1.1.2,frame _ (maskedConst_wires_subset c T y carry cin K hT hc).1
      specs.2.1.1.1.1 specs.2.1.2 specs.2.1.1.1.2 specs.2.2⟩
  · have specs := maskedSubConst_spec c cin T y carry hn hT hc K hK (base c) A s m ⟨⟨⟨⟨ct,tz⟩,h.1⟩,ci⟩,cz⟩
    simp only [↓reduceIte]
    exact ⟨specs.1,specs.2.1.1.2,frame _ (maskedConst_wires_subset c T y carry cin K hT hc).2
      specs.2.1.1.1.1 specs.2.1.2 specs.2.1.1.1.2 specs.2.2⟩

/-- 规范化只改变低256位及其保留标志。 -/
def SquareNormFrame (L : SquareReduceLayout) (base : BasisState) (V : Nat) (F : Bool)
    (s : BasisState) : Prop :=
  regValue L.value s=V ∧ s L.flag=F ∧ ∀w,w∉L.value++[L.flag] → s w=base w

private theorem norm_nd (L : SquareReduceLayout) (hn : L.wires.Nodup) :
    (L.flag::L.cin::(L.value++L.mask++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have hv := (List.take_sublist 256 L.r).count_le w
  simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
  simp only [List.count_cons,List.count_append,SquareReduceLayout.value]
  omega

private theorem norm_outside (L : SquareReduceLayout) (hn : L.wires.Nodup) (w : Wire)
    (hw : w∈L.cin::(L.mask++L.carry)) : w∉L.value++[L.flag] := by
  intro hh
  have h := List.nodup_iff_count.mp (norm_nd L hn) w
  have h1 := List.count_pos_iff.mpr hw
  have h2 := List.count_pos_iff.mpr hh
  simp only [List.count_cons,List.count_append,List.count_nil] at h h1 h2
  omega

private theorem norm_compare (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F)
      (compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p)
      (SquareNormFrame L base W (F ^^ decide (W<SquareReduction.p))) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have nd : (L.flag::L.cin::(L.value++L.mask++L.carry.take 256)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp (norm_nd L hn) w
    have hc := (List.take_sublist 256 L.carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ht : L.value.length=L.mask.length := hv.trans hw.mask.symm
  have hc : (L.carry.take 256).length=L.mask.length := by simp [hw.carry,hw.mask]
  have hp : SquareReduction.p<2^L.mask.length := by norm_num [hw.mask,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  intro s m h
  have keep (w : Wire) (hh : w∈L.cin::(L.mask++L.carry)) := h.2.2 w (norm_outside L hn w hh)
  have ci : s.basis L.cin=false := (keep _ (by simp)).trans hi
  have clean (r : List Wire) (hr : r⊆L.mask++L.carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    have hmem := hr hh
    rw [keep w (by simp only [List.mem_cons] ; exact Or.inr hmem)]
    exact (regValue_zero _ _).mp hz w hmem
  have tz := clean L.mask (by simp)
  have cz := clean (L.carry.take 256) (by intro w hh; simp [List.mem_of_mem_take hh])
  have sp := compareLtConst_spec L.value L.mask (L.carry.take 256) L.cin L.flag
    nd ht hc SquareReduction.p hp W F s m ⟨⟨⟨⟨h.1,tz⟩,cz⟩,ci⟩,h.2.1⟩
  refine ⟨sp.1,sp.2.1.1.1.1,sp.2.2,?_⟩
  intro w hh
  have hval : w∉L.value := fun hm => hh (by simp [hm])
  have hflag : w≠L.flag := fun he => hh (by simp [he])
  by_cases hm : w∈L.mask
  · exact ((regValue_zero _ _).mp sp.2.1.1.1.2 w hm).trans ((regValue_zero _ _).mp hz w (by simp [hm])).symm
  by_cases hcy : w∈L.carry.take 256
  · exact ((regValue_zero _ _).mp sp.2.1.1.2 w hcy).trans
      ((regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hcy])).symm
  by_cases hci : w=L.cin
  · subst w; exact sp.2.1.2.trans hi.symm
  have ho : w∉wires (compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p) := by
    rw [(compareLt_wires none L.value L.mask (L.carry.take 256) L.cin L.flag ht hc).2]
    simpa using (show w∉L.flag::L.cin::(L.value++L.mask++L.carry.take 256) by simp [hflag,hci,hval,hm,hcy])
  exact (run_preserves_outside _ m s w ho).trans (h.2.2 w hh)

private theorem norm_flip (L : SquareReduceLayout) (hn : L.wires.Nodup)
    (base : BasisState) (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F) [.X L.flag] (SquareNormFrame L base W (!F)) := by
  have hf : L.flag∉L.value := by
    have hh := (List.nodup_cons.mp (norm_nd L hn)).1
    intro hm; exact hh (by simp [hm])
  intro s m h
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue L.value (writeBit s.basis L.flag (!(s.basis L.flag)))=W
    rw [regValue_congr L.value _ s.basis (fun w hw => by simp [writeBit,Function.update,show w≠L.flag from fun he => hf (he ▸ hw)])]
    exact h.1
  · simpa [run,writeBit] using congrArg Bool.not h.2.1
  · intro w hw
    have hf : w≠L.flag := fun he => hw (by simp [he])
    simpa [run,writeBit,hf] using h.2.2 w hw

private theorem norm_arith (sub : Bool) (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (F : Bool) :
    Triple (SquareNormFrame L base W F)
      (if sub then maskedSubConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p
       else maskedAddConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p)
      (SquareNormFrame L base
        (if sub then (W+2^256-(if F then SquareReduction.p else 0))%2^256
         else (W+(if F then SquareReduction.p else 0))%2^256) F) := by
  have hv : L.value.length=256 := by simp [SquareReduceLayout.value,hw.r]
  have nd : (L.flag::L.cin::(L.mask++L.value++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp (norm_nd L hn) w
    have hc := (List.take_sublist 255 L.carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ht : L.mask.length=L.value.length := hw.mask.trans hv.symm
  have hc : (L.carry.take 255).length+1=L.value.length := by simp [hw.carry,hv]
  have hp : SquareReduction.p<2^L.mask.length := by norm_num [hw.mask,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  intro s m h
  have keep (w : Wire) (hh : w∈L.cin::(L.mask++L.carry)) := h.2.2 w (norm_outside L hn w hh)
  have ci : s.basis L.cin=false := (keep _ (by simp)).trans hi
  have clean : regValue (L.mask++L.carry.take 255) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    have hmem : w∈L.mask++L.carry := by
      simp only [List.mem_append] at hh ⊢
      exact hh.elim Or.inl (fun h => Or.inr (List.mem_of_mem_take h))
    rw [keep w (by simp only [List.mem_cons]; exact Or.inr hmem)]
    exact (regValue_zero _ _).mp hz w hmem
  have sp := maskedConst_frame sub L.flag L.cin L.mask L.value (L.carry.take 255)
    nd ht hc SquareReduction.p hp s.basis clean ci W s m ⟨h.1,fun _ _ => rfl⟩
  have hf : L.flag∉L.value := by
    have hh := (List.nodup_cons.mp (norm_nd L hn)).1
    intro hm; exact hh (by simp [hm])
  refine ⟨sp.1,?_,(sp.2.2 L.flag hf).trans h.2.1,?_⟩
  · simpa only [hv,h.2.1] using sp.2.1
  · intro w hh
    exact (sp.2.2 w (fun hm => hh (by simp [hm]))).trans (h.2.2 w hh)

/-- 规范化及独立前向恢复；保留标志精确记录是否试减 p。 -/
theorem squareNormalize_correct (L : SquareReduceLayout) (hn : L.wires.Nodup) (hw : L.Widths)
    (base : BasisState) (hz : regValue (L.mask++L.carry) base=0) (hi : base L.cin=false)
    (W : Nat) (hW : W<SquareReduction.B) :
    Triple (SquareNormFrame L base W false) (squareNormalize L)
      (SquareNormFrame L base (W%SquareReduction.p) (decide (SquareReduction.p≤W))) ∧
    Triple (SquareNormFrame L base (W%SquareReduction.p) (decide (SquareReduction.p≤W)))
      (squareDenormalize L) (SquareNormFrame L base W false) := by
  have hW' : W<2^256 := hW
  have hc : (!(decide (W<SquareReduction.p)))=decide (SquareReduction.p≤W) := by
    by_cases h : W<SquareReduction.p <;> simp [h, show (SquareReduction.p≤W)↔¬W<SquareReduction.p by omega]
  have hc' : (!(decide (SquareReduction.p≤W)))=decide (W<SquareReduction.p) := by
    rw [←hc,Bool.not_not]
  have hnumb : (W+2^256-(if decide (SquareReduction.p≤W) then SquareReduction.p else 0))%2^256=
      W%SquareReduction.p := by
    have hh := SquareReduction.normalize W hW
    by_cases h : SquareReduction.p≤W
    · simp only [h,decide_true,↓reduceIte] at hh ⊢
      have he : W+2^256-SquareReduction.p=(W-SquareReduction.p)+2^256 := by omega
      rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by change W-SquareReduction.p<SquareReduction.B; omega)]
      exact hh
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,Nat.sub_zero,Nat.add_mod_right] at hh ⊢
      rw [Nat.mod_eq_of_lt hW']
      exact hh
  have hnuma : (W%SquareReduction.p+(if decide (SquareReduction.p≤W) then SquareReduction.p else 0))%2^256=W := by
    have hh := SquareReduction.normalize W hW
    by_cases h : SquareReduction.p≤W
    · simp only [h,decide_true,↓reduceIte] at hh ⊢
      rw [←hh,Nat.sub_add_cancel h,Nat.mod_eq_of_lt hW']
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,Nat.sub_zero] at hh ⊢
      rw [←hh,Nat.add_zero,Nat.mod_eq_of_lt hW']
  have cmp := norm_compare L hn hw base hz hi W false
  simp only [Bool.false_xor] at cmp
  have flip := norm_flip L hn base W (decide (W<SquareReduction.p))
  rw [hc] at flip
  have sb := norm_arith true L hn hw base hz hi W (decide (SquareReduction.p≤W))
  simp only [↓reduceIte,hnumb] at sb
  have ad := norm_arith false L hn hw base hz hi (W%SquareReduction.p) (decide (SquareReduction.p≤W))
  simp only [Bool.false_eq_true,↓reduceIte,hnuma] at ad
  have fl := norm_flip L hn base W (decide (SquareReduction.p≤W))
  rw [hc'] at fl
  have cm := norm_compare L hn hw base hz hi W (decide (W<SquareReduction.p))
  simp only [Bool.xor_self] at cm
  constructor
  · simpa only [squareNormalize,List.append_assoc] using cmp.seq (flip.seq sb)
  · simpa only [squareDenormalize,List.append_assoc] using ad.seq (fl.seq cm)

end ECDSAAdd.Arithmetic
