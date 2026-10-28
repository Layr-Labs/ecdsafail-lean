import ECDSAAdd.Arithmetic.SquareSubLayout
import ECDSAAdd.Arithmetic.KaratsubaSquareState
import ECDSAAdd.Arithmetic.SquareReduceSpec
import ECDSAAdd.Arithmetic.SignedKaratsubaSquareState

namespace ECDSAAdd.Arithmetic

private theorem reduce_values_congr (R : SquareReduceLayout) (lo hi v q : Nat) (b f : Bool)
    (s t : BasisState) (h : SquareReduceValues R lo hi v q b f s)
    (he : ∀ w,w∈R.wires→t w=s w) : SquareReduceValues R lo hi v q b f t := by
  have re (r : List Wire) (hr : r⊆R.wires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw=>he w (hr hw))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.low
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.high
  · exact (re _ (by intro w hw; have hm:=List.mem_of_mem_take hw; simp [SquareReduceLayout.wires,hm])).trans h.value
  · exact (re _ (by intro w hw; have hm:=List.mem_of_mem_drop hw; simp [SquareReduceLayout.wires,hm])).trans h.quotient
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.pad
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.mask
  · exact (re _ (by intro w hw; simp [SquareReduceLayout.wires,hw])).trans h.carry
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.cin
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.bit
  · exact (he _ (by simp [SquareReduceLayout.wires])).trans h.flag

private theorem reduce_strong_frame (R : SquareReduceLayout) (_hw : R.Widths)
    (lo hi v q v' q' : Nat) (b f b' f' : Bool) (s t : BasisState)
    (hs : SquareReduceValues R lo hi v q b f s)
    (ht : SquareReduceValues R lo hi v' q' b' f' t)
    (ho : ∀ w,w∉R.wires→t w=s w) :
    ∀ w,w∉R.r++[R.b,R.flag]→t w=s w := by
  intro w hw'
  have eqv (r : List Wire) (he : regValue r t=regValue r s) (hm : w∈r) : t w=s w :=
    (regValue_eq_iff r t s).mp he w hm
  by_cases hl : w∈R.low
  · exact eqv _ (ht.low.trans hs.low.symm) hl
  by_cases hh : w∈R.high
  · exact eqv _ (ht.high.trans hs.high.symm) hh
  by_cases hp : w∈R.pad
  · exact eqv _ (ht.pad.trans hs.pad.symm) hp
  by_cases hm : w∈R.mask
  · exact eqv _ (ht.mask.trans hs.mask.symm) hm
  by_cases hk : w∈R.carry
  · exact eqv _ (ht.carry.trans hs.carry.symm) hk
  by_cases hc : w=R.cin
  · subst w; exact ht.cin.trans hs.cin.symm
  apply ho
  simpa only [SquareReduceLayout.wires,List.mem_append,List.mem_cons,List.not_mem_nil,
    hl,hh,hp,hm,hk,hc,false_or,or_false] using hw'

private theorem count_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup)
    (a b : List Wire) (hc : ∀w,a.count w+b.count w≤L.wires.count w) : List.Disjoint a b := by
  apply List.disjoint_left.mpr
  intro w ha hb
  have hh:=List.nodup_iff_count.mp hn w
  have h1:=List.count_pos_iff.mpr ha
  have h2:=List.count_pos_iff.mpr hb
  have h3:=hc w
  omega

private theorem out_reduction_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint L.out L.reduction.wires := by
  apply count_disjoint L hn
  intro w
  have hz:=congrArg (List.count w) (List.take_append_drop 256 L.z)
  simp only [SquareSubLayout.reduction,SquareReduceLayout.wires,SquareSubLayout.wires,
    SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil] at hz ⊢
  omega

/-- The output update restores its extended high bit as well as all arithmetic work. -/
theorem squareSub_output_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (A O : Nat)
    (ha : regValue (L.r.take 256) base=A) (hs : base L.sourceHigh=false)
    (hh : base L.outputHigh=false) (hz : regValue L.output.work base=0)
    (hA : A≤SquareReduction.p) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (modSubInPlace L.output SquareReduction.p)
      (SquareFrame L.out base ((O+SquareReduction.p-A)%SquareReduction.p)) := by
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hpn : SquareReduction.p<2^256 := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have ds : List.Disjoint L.output.a L.out := by
    apply count_disjoint L hn; intro w
    have hc:=(List.take_sublist 256 L.r).count_le w
    simp only [SquareSubLayout.output,SquareSubLayout.wires,SquareSubLayout.work,
      List.count_append,List.count_cons,List.count_nil]; omega
  have dw : List.Disjoint L.output.work L.out := by
    apply count_disjoint L hn; intro w
    have hc:=(List.take_sublist 256 L.carry).count_le w
    simp only [SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
      SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil]; omega
  have dh : L.outputHigh∉L.out := by
    intro ho
    have hh:=List.nodup_iff_count.mp hn L.outputHigh
    have hc:=List.count_pos_iff.mpr ho
    simp only [SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil] at hh
    simp only [beq_self_eq_true,ite_true] at hh
    omega
  intro s m h
  have sa : regValue L.output.a s.basis=A := by
    rw [regValue_congr _ _ _ (fun w hw=>h.2 w (fun ho=>List.disjoint_left.mp ds hw ho))]
    change regValue (L.r.take 256++[L.sourceHigh]) base=A
    rw [regValue_append,ha]
    have hb : regValue [L.sourceHigh] base=0 := by simp [regValue,hs]
    simp only [hb,Nat.mul_zero,Nat.add_zero]
  have sh : s.basis L.outputHigh=false := (h.2 _ dh).trans hh
  have sz : regValue L.output.z s.basis=O := by
    change regValue (L.out++[L.outputHigh]) s.basis=O
    rw [regValue_append,h.1]
    have hb : regValue [L.outputHigh] s.basis=0 := by simp [regValue,sh]
    simp only [hb,Nat.mul_zero,Nat.add_zero]
  have sw : regValue L.output.work s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw=>h.2 w (fun ho=>List.disjoint_left.mp dw hw ho))).trans hz
  have hr:=modSubInPlace_spec L.output 256 SquareReduction.p A O
    (L.output_widths hw) (L.output_nodup hn) hp hpn hA hO s m ⟨⟨sa,sz⟩,sw⟩
  have hv:=hr.2.1.2
  change regValue L.output.z (run (modSubInPlace L.output SquareReduction.p) m s).basis=
    (O+SquareReduction.p-A)%SquareReduction.p at hv
  have hb : (O+SquareReduction.p-A)%SquareReduction.p<2^256 :=
    (Nat.mod_lt _ hp).trans hpn
  change regValue (L.out++[L.outputHigh]) _=_ at hv
  rw [regValue_append,hw.out] at hv
  have one : regValue [L.outputHigh] (run (modSubInPlace L.output SquareReduction.p) m s).basis=
      if (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh then 1 else 0 := by
    simp [regValue]
  rw [one] at hv
  have hf : (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh=false := by
    cases he : (run (modSubInPlace L.output SquareReduction.p) m s).basis L.outputHigh <;> (simp [he] at hv ⊢; try omega)
  refine ⟨hr.1,?_,?_⟩
  · simpa [hf] using hv
  · intro w ho
    by_cases he : w=L.outputHigh
    · subst w; exact hf.trans hh.symm
    apply Eq.trans _ (h.2 w ho)
    apply modSubInPlace_frame L.output 256 SquareReduction.p A O
      (L.output_widths hw) (L.output_nodup hn) hp hpn hA hO s m sa sz sw
    simpa [ModInPlaceLayout.z,ModAddCoreLayout.z,SquareSubLayout.output] using And.intro ho he


private def reduceDirty (L : SquareSubLayout) := L.r++[L.b,L.flag]
private def outputClean (L : SquareSubLayout) := L.output.work++[L.sourceHigh,L.outputHigh]
private def ReduceStage (L : SquareSubLayout) (P : BasisState→Prop) (base : BasisState)
    (O : Nat) (s : BasisState) :=
  P s ∧ regValue L.out s=O ∧ ∀ w,w∉L.out++reduceDirty L→s w=base w

private theorem outputClean_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint (outputClean L) (L.out++reduceDirty L) := by
  apply count_disjoint L hn; intro w
  have hc:=(List.take_sublist 256 L.carry).count_le w
  simp only [outputClean,reduceDirty,SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
    SquareSubLayout.wires,SquareSubLayout.work,List.count_append,List.count_cons,List.count_nil]
  omega

private theorem reduceDirty_zero (L : SquareSubLayout) (hw : L.Widths) (lo hi : Nat)
    (s : BasisState) (h : SquareReduceValues L.reduction lo hi 0 0 false false s) :
    regValue (reduceDirty L) s=0 := by
  have hr := h.r_read (L.reduction_widths hw)
  have rb : regValue L.r s=0 := by simpa [SquareSubLayout.reduction] using hr
  change regValue (L.r++[L.b,L.flag]) s=0
  rw [regValue_append,rb]
  have hb : s L.b=false := h.bit
  have hf : s L.flag=false := h.flag
  simp [regValue,hb,hf]

/-- Reduction history survives the output update and is then completely restored. -/
theorem squareSub_middle (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (lo hi O : Nat)
    (hc : SquareReduceValues L.reduction lo hi 0 0 false false base)
    (hz : regValue (outputClean L) base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (SquareFrame L.out base ((O+SquareReduction.p-(lo+SquareReduction.B*hi)%SquareReduction.p)%SquareReduction.p)) := by
  let R := L.reduction
  let A := (lo+SquareReduction.B*hi)%SquareReduction.p
  let O' := (O+SquareReduction.p-A)%SquareReduction.p
  have wr := L.reduction_widths hw
  have nr := L.reduction_nodup hn
  have dis := out_reduction_disjoint L hn
  have hlo : lo<SquareReduction.B := by
    have hh:=regValue_lt R.low base
    rw [hc.low,wr.low] at hh; exact hh
  have hhi : hi<SquareReduction.B := by
    have hh:=regValue_lt R.high base
    rw [hc.high,wr.high] at hh; exact hh
  have sp:=squareReduce_correct R wr nr lo hi hlo hhi
  have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have dn : ∀w,w∈L.out→w∉R.r++[R.b,R.flag] := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simpa only [R,SquareSubLayout.reduction] using
      (show w∈L.reduction.wires from by
        simp only [SquareReduceLayout.wires,List.mem_append,List.mem_cons,List.not_mem_nil] at hd ⊢
        tauto)
  have first : Triple (SquareFrame L.out base O) (squareReduce R)
      (ReduceStage L (SquareReduced R lo hi) base O) := by
    intro s m hs
    have pre:=reduce_values_congr R lo hi 0 0 false false base s.basis hc
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sr:=sp.1 s m pre
    have fr:=reduce_strong_frame R wr _ _ _ _ _ _ _ _ _ _ s.basis _ pre sr.2
      (fun w hw=>(squareReduce_frame R wr m s w hw).1)
    refine ⟨sr.1,sr.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have second : Triple (ReduceStage L (SquareReduced R lo hi) base O)
      (modSubInPlace L.output SquareReduction.p)
      (ReduceStage L (SquareReduced R lo hi) base O') := by
    intro s m hs
    have clean : regValue (outputClean L) s.basis=0 :=
      (regValue_congr _ _ _ (fun w hw=>hs.2.2 w
        (fun hd=>List.disjoint_left.mp (outputClean_disjoint L hn) hw hd))).trans hz
    have cw := (regValue_zero _ _).mp clean
    have hwork : regValue L.output.work s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw=>cw w (by simp [outputClean,hw]))
    have sbit : s.basis L.sourceHigh=false := cw _ (by simp [outputClean])
    have obit : s.basis L.outputHigh=false := cw _ (by simp [outputClean])
    have ha : regValue (L.r.take 256) s.basis=A := hs.1.value
    have op:=squareSub_output_frame L hw hn s.basis A O ha sbit obit hwork
      (Nat.le_of_lt (Nat.mod_lt _ hp)) hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    refine ⟨op.1,?_,op.2.1,?_⟩
    · exact reduce_values_congr R _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>op.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      have ho : w∉L.out := fun ho=>hw' (by simp [ho])
      exact (op.2.2 w ho).trans (hs.2.2 w hw')
  have third : Triple (ReduceStage L (SquareReduced R lo hi) base O')
      (squareReduceClear R) (SquareFrame L.out base O') := by
    intro s m hs
    have sr:=sp.2 s m hs.1
    have fr:=reduce_strong_frame R wr _ _ _ _ _ _ _ _ _ _ s.basis _ hs.1 sr.2
      (fun w hw=>(squareReduce_frame R wr m s w hw).2)
    refine ⟨sr.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈reduceDirty L
      · have hf:=reduceDirty_zero L hw lo hi _ sr.2
        have hb:=reduceDirty_zero L hw lo hi _ hc
        exact ((regValue_eq_iff _ _ _).mp (hf.trans hb.symm)) w hd
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  exact (first.seq second).seq third


private def integerDirty (L : SquareSubLayout) := L.a++L.d++L.z
private def integerClean (L : SquareSubLayout) := L.r++L.mask++L.carry++[L.cin]++L.pad++
  [L.b,L.flag,L.sourceHigh,L.outputHigh,L.constantHigh,L.maskHigh,L.layoutFlag,L.sumHigh]

private theorem integerClean_sub (L : SquareSubLayout) : integerClean L⊆L.work := by
  intro w hw
  simp only [integerClean,SquareSubLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢
  tauto

private theorem outputClean_sub (L : SquareSubLayout) : outputClean L⊆integerClean L := by
  intro w hw
  have hc : w∈L.carry.take 256→w∈L.carry := fun hh=>List.mem_of_mem_take hh
  simp only [outputClean,SquareSubLayout.output,ModInPlaceLayout.work,ModAddCoreLayout.work,
    integerClean,List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢
  tauto

private theorem integerClean_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint (integerClean L) (L.out++integerDirty L) := by
  apply count_disjoint L hn; intro w
  simp only [integerClean,integerDirty,SquareSubLayout.work,SquareSubLayout.wires,
    List.count_append,List.count_cons,List.count_nil]
  omega

private theorem out_integer_disjoint (L : SquareSubLayout) (hn : L.wires.Nodup) :
    List.Disjoint L.out L.integer.wires := by
  apply count_disjoint L hn; intro w
  have hx:=congrArg (List.count w) (List.take_append_drop 128 L.x)
  have hp:=congrArg (List.count w) (List.take_append_drop 128 L.pad)
  have hr:=(List.take_sublist 258 L.r).count_le w
  simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,SquareSubLayout.work,
    SquareSubLayout.wires,List.count_append,List.count_cons,List.count_nil] at hx hp ⊢
  omega

private theorem integer_values_congr (K : KaratsubaSquareLayout) (lo hi av dv cv zv sv : Nat)
    (s t : BasisState) (hs : KaratsubaValues K lo hi av dv cv zv sv s)
    (he : ∀ w,w∈K.wires→t w=s w) : KaratsubaValues K lo hi av dv cv zv sv t := by
  have re (r : List Wire) (hr : r⊆K.wires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw=>he w (hr hw))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.low
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.high
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.a
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.d
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.c
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.z
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.sum
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.pad
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.mask
  · exact (re _ (by intro w hw; simp [KaratsubaSquareLayout.wires,hw])).trans hs.carry
  · exact (he _ (by simp [KaratsubaSquareLayout.wires])).trans hs.cin

private theorem integer_initial (L : SquareSubLayout) (base : BasisState)
    (hz : regValue L.work base=0) :
    KaratsubaValues L.integer (regValue (L.x.take 128) base) (regValue (L.x.drop 128) base)
      0 0 0 0 0 base := by
  have zero (r : List Wire) (hr : r⊆L.work) : regValue r base=0 :=
    (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hz w (hr hw))
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_take hw
    simp [SquareSubLayout.work,hr]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · apply zero; intro w hw
    change w∈L.pad.drop 128++[L.sumHigh] at hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw | hw
    · have hp:=List.mem_of_mem_drop hw; simp [SquareSubLayout.work,hp]
    · simp [SquareSubLayout.work,hw]
  · apply zero; intro w hw
    have hp : w∈L.pad := List.mem_of_mem_take hw
    simp [SquareSubLayout.work,hp]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.integer,SquareSubLayout.work] at hw ⊢; tauto)
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.work,SquareSubLayout.integer])

private theorem reduction_initial (L : SquareSubLayout) (s : BasisState)
    (hz : regValue (integerClean L) s=0) :
    SquareReduceValues L.reduction (regValue (L.z.take 256) s) (regValue (L.z.drop 256) s)
      0 0 false false s := by
  have zero (r : List Wire) (hr : r⊆integerClean L) : regValue r s=0 :=
    (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hz w (hr hw))
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_take hw
    simp [integerClean,hr]
  · apply zero; intro w hw
    have hr : w∈L.r := List.mem_of_mem_drop hw
    simp [integerClean,hr]
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact zero _ (by intro w hw; simp [SquareSubLayout.reduction,integerClean] at hw ⊢; tauto)
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])
  · exact (regValue_zero _ _).mp hz _ (by simp [SquareSubLayout.reduction,integerClean])

private def IntegerStage (L : SquareSubLayout) (P : BasisState→Prop) (base : BasisState)
    (O : Nat) (s : BasisState) :=
  P s ∧ regValue L.out s=O ∧ ∀ w,w∉L.out++integerDirty L→s w=base w

/-- Full square-subtract correctness with an explicit target-only frame. -/
theorem squareSub_correct (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (X O : Nat) (hx : regValue L.x base=X)
    (hz : regValue L.work base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (squareSub L)
      (SquareFrame L.out base ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) := by
  let lo:=regValue (L.x.take 128) base
  let hi:=regValue (L.x.drop 128) base
  let K:=L.integer
  let O':=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p
  have wk:=L.integer_valid hw hn
  have dis:=out_integer_disjoint L hn
  have pre:=integer_initial L base hz
  have xsum : lo+2^128*hi=X := by
    have he:=regValue_append (L.x.take 128) (L.x.drop 128) base
    rw [List.take_append_drop,hx,List.length_take,hw.x] at he
    simpa only [Nat.min_eq_left (by decide : 128≤256)] using he.symm
  have dn : ∀w,w∈L.out→w∉integerDirty L := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simp only [integerDirty,List.mem_append] at hd
    simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append]
    tauto
  have first : Triple (SquareFrame L.out base O) (karatsubaSquare K)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O) := by
    intro s m hs
    have ps:=integer_values_congr K lo hi 0 0 0 0 0 base s.basis pre
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sp:=karatsubaSquare_spec K wk lo hi s m ps
    rw [xsum] at sp
    have fr:=karatsubaSquare_frame K wk lo hi s m ps
    refine ⟨sp.1,sp.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have middle : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O') := by
    intro s m hs
    have cz : regValue (integerClean L) s.basis=0 := by
      apply (regValue_zero _ _).mpr; intro w hw'
      rw [hs.2.2 w (fun hm=>List.disjoint_left.mp (integerClean_disjoint L hn) hw' hm)]
      exact (regValue_zero _ _).mp hz w (integerClean_sub L hw')
    have oz : regValue (outputClean L) s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw'=>(regValue_zero _ _).mp cz w (outputClean_sub L hw'))
    have rp:=reduction_initial L s.basis cz
    have sp:=squareSub_middle L hw hn s.basis _ _ O rp oz hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    have zsum : regValue (L.z.take 256) s.basis+SquareReduction.B*regValue (L.z.drop 256) s.basis=X^2 := by
      have he:=regValue_append (L.z.take 256) (L.z.drop 256) s.basis
      rw [List.take_append_drop,List.length_take,hw.z] at he
      have hv : regValue L.z s.basis=X^2 := hs.1.z
      rw [hv] at he
      simpa only [Nat.min_eq_left (by decide : 256≤512),SquareReduction.B] using he.symm
    rw [zsum] at sp
    refine ⟨sp.1,?_,sp.2.1,?_⟩
    · exact integer_values_congr K _ _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>sp.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      exact (sp.2.2 w (fun ho=>hw' (by simp [ho]))).trans (hs.2.2 w hw')
  have last : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O')
      (karatsubaSquareClear K) (SquareFrame L.out base O') := by
    intro s m hs
    have ps : KaratsubaValues K lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis := by
      simpa only [xsum] using hs.1
    have sp:=karatsubaSquareClear_spec K wk lo hi s m ps
    have fr:=karatsubaSquareClear_frame K wk lo hi s m ps
    refine ⟨sp.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈integerDirty L
      · have dz : regValue (integerDirty L) (run (karatsubaSquareClear K) m s).basis=0 := by
          simp only [integerDirty,regValue_append]
          have ha : regValue L.a (run (karatsubaSquareClear K) m s).basis=0 := sp.2.a
          have hd : regValue L.d (run (karatsubaSquareClear K) m s).basis=0 := sp.2.d
          have hz : regValue L.z (run (karatsubaSquareClear K) m s).basis=0 := sp.2.z
          simp only [ha,hd,hz,Nat.mul_zero,Nat.add_zero]
        have hb : base w=false := (regValue_zero _ _).mp hz w (by
          simp only [integerDirty,List.mem_append] at hd
          simp only [SquareSubLayout.work,List.mem_append]; tauto)
        exact ((regValue_zero _ _).mp dz w hd).trans hb.symm
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  simpa only [squareSub,List.append_assoc] using (first.seq middle).seq last


/-- Any 256-bit input may be squared; only the subtracted-from output must be canonical. -/
theorem squareSub_spec (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) :
    {{ L.x=X,L.out=O,L.work=0 }} squareSub L
    {{ L.x=X,L.out=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p,L.work=0 }} := by
  intro s m hs
  have sp:=squareSub_correct L hw hn s.basis X O hs.1.1 hs.2 hO s m
    ⟨hs.1.2,fun _ _=>rfl⟩
  have dx : List.Disjoint L.x L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  have dw : List.Disjoint L.work L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  refine ⟨sp.1,⟨?_,sp.2.1⟩,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dx hw ho))).trans hs.1.1
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dw hw ho))).trans hs.2

/-- Target-only frame, including the aliased padding, retained reduction history and all extra bits. -/
theorem squareSub_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) (s : State) (m : List Bool)
    (hx : regValue L.x s.basis=X) (ho : regValue L.out s.basis=O)
    (hz : regValue L.work s.basis=0) (w : Wire) (hwout : w∉L.out) :
    (run (squareSub L) m s).basis w=s.basis w :=
  (squareSub_correct L hw hn s.basis X O hx hz hO s m ⟨ho,fun _ _=>rfl⟩).2.2 w hwout

/-- Full exact signed-row square-subtract correctness with an explicit target-only frame. -/
theorem signedSquareSub_correct (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (X O : Nat) (hx : regValue L.x base=X)
    (hz : regValue L.work base=0) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.out base O) (signedSquareSub L)
      (SquareFrame L.out base ((O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p)) := by
  let lo:=regValue (L.x.take 128) base
  let hi:=regValue (L.x.drop 128) base
  let K:=L.integer
  let O':=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p
  have wk:=L.integer_valid hw hn
  have dis:=out_integer_disjoint L hn
  have pre:=integer_initial L base hz
  have xsum : lo+2^128*hi=X := by
    have he:=regValue_append (L.x.take 128) (L.x.drop 128) base
    rw [List.take_append_drop,hx,List.length_take,hw.x] at he
    simpa only [Nat.min_eq_left (by decide : 128≤256)] using he.symm
  have dn : ∀w,w∈L.out→w∉integerDirty L := by
    intro w ho hd
    apply List.disjoint_left.mp dis ho
    simp only [integerDirty,List.mem_append] at hd
    simp only [SquareSubLayout.integer,KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append]
    tauto
  have first : Triple (SquareFrame L.out base O) (signedKaratsubaSquare K)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O) := by
    intro s m hs
    have ps:=integer_values_congr K lo hi 0 0 0 0 0 base s.basis pre
      (fun w hw=>hs.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    have sp:=signedKaratsubaSquare_spec K wk lo hi s m ps
    rw [xsum] at sp
    have fr:=signedKaratsubaSquare_frame K wk lo hi s m ps
    refine ⟨sp.1,sp.2,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.1
    · intro w hw'
      simp only [List.mem_append,not_or] at hw'
      exact (fr w hw'.2).trans (hs.2 w hw'.1)
  have middle : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O)
      (squareReduce L.reduction ++ modSubInPlace L.output SquareReduction.p ++ squareReduceClear L.reduction)
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O') := by
    intro s m hs
    have cz : regValue (integerClean L) s.basis=0 := by
      apply (regValue_zero _ _).mpr; intro w hw'
      rw [hs.2.2 w (fun hm=>List.disjoint_left.mp (integerClean_disjoint L hn) hw' hm)]
      exact (regValue_zero _ _).mp hz w (integerClean_sub L hw')
    have oz : regValue (outputClean L) s.basis=0 :=
      (regValue_zero _ _).mpr (fun w hw'=>(regValue_zero _ _).mp cz w (outputClean_sub L hw'))
    have rp:=reduction_initial L s.basis cz
    have sp:=squareSub_middle L hw hn s.basis _ _ O rp oz hO s m ⟨hs.2.1,fun _ _=>rfl⟩
    have zsum : regValue (L.z.take 256) s.basis+SquareReduction.B*regValue (L.z.drop 256) s.basis=X^2 := by
      have he:=regValue_append (L.z.take 256) (L.z.drop 256) s.basis
      rw [List.take_append_drop,List.length_take,hw.z] at he
      have hv : regValue L.z s.basis=X^2 := hs.1.z
      rw [hv] at he
      simpa only [Nat.min_eq_left (by decide : 256≤512),SquareReduction.B] using he.symm
    rw [zsum] at sp
    refine ⟨sp.1,?_,sp.2.1,?_⟩
    · exact integer_values_congr K _ _ _ _ _ _ _ s.basis _ hs.1
        (fun w hw=>sp.2.2 w (fun ho=>List.disjoint_left.mp dis ho hw))
    · intro w hw'
      exact (sp.2.2 w (fun ho=>hw' (by simp [ho]))).trans (hs.2.2 w hw')
  have last : Triple
      (IntegerStage L (KaratsubaValues K lo hi (lo^2) (hi^2) 0 (X^2) 0) base O')
      (signedKaratsubaSquareClear K) (SquareFrame L.out base O') := by
    intro s m hs
    have ps : KaratsubaValues K lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis := by
      simpa only [xsum] using hs.1
    have sp:=signedKaratsubaSquareClear_spec K wk lo hi s m ps
    have fr:=signedKaratsubaSquareClear_frame K wk lo hi s m ps
    refine ⟨sp.1,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw=>fr w (dn w hw))).trans hs.2.1
    · intro w ho
      by_cases hd : w∈integerDirty L
      · have dz : regValue (integerDirty L) (run (signedKaratsubaSquareClear K) m s).basis=0 := by
          simp only [integerDirty,regValue_append]
          have ha : regValue L.a (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.a
          have hd : regValue L.d (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.d
          have hz : regValue L.z (run (signedKaratsubaSquareClear K) m s).basis=0 := sp.2.z
          simp only [ha,hd,hz,Nat.mul_zero,Nat.add_zero]
        have hb : base w=false := (regValue_zero _ _).mp hz w (by
          simp only [integerDirty,List.mem_append] at hd
          simp only [SquareSubLayout.work,List.mem_append]; tauto)
        exact ((regValue_zero _ _).mp dz w hd).trans hb.symm
      · exact (fr w hd).trans (hs.2.2 w (by simp [ho,hd]))
  simpa only [signedSquareSub,List.append_assoc] using (first.seq middle).seq last


/-- Signed-row Step 4 is exact for every 256-bit input; only the output must be canonical. -/
theorem signedSquareSub_spec (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) :
    {{ L.x=X,L.out=O,L.work=0 }} signedSquareSub L
    {{ L.x=X,L.out=(O+SquareReduction.p-X^2%SquareReduction.p)%SquareReduction.p,L.work=0 }} := by
  intro s m hs
  have sp:=signedSquareSub_correct L hw hn s.basis X O hs.1.1 hs.2 hO s m
    ⟨hs.1.2,fun _ _=>rfl⟩
  have dx : List.Disjoint L.x L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  have dw : List.Disjoint L.work L.out := by
    apply count_disjoint L hn; intro w
    simp only [SquareSubLayout.wires,List.count_append]; omega
  refine ⟨sp.1,⟨?_,sp.2.1⟩,?_⟩
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dx hw ho))).trans hs.1.1
  · exact (regValue_congr _ _ _ (fun w hw=>sp.2.2 w
      (fun ho=>List.disjoint_left.mp dw hw ho))).trans hs.2

/-- Target-only frame for the signed-row Step 4 implementation. -/
theorem signedSquareSub_frame (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X O : Nat) (hO : O<SquareReduction.p) (s : State) (m : List Bool)
    (hx : regValue L.x s.basis=X) (ho : regValue L.out s.basis=O)
    (hz : regValue L.work s.basis=0) (w : Wire) (hwout : w∉L.out) :
    (run (signedSquareSub L) m s).basis w=s.basis w :=
  (signedSquareSub_correct L hw hn s.basis X O hx hz hO s m ⟨ho,fun _ _=>rfl⟩).2.2 w hwout

theorem signedSquareSub_wires_subset (L : SquareSubLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : wires (signedSquareSub L)⊆L.wires.toFinset := by
  have ik : L.integer.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hx := congrArg (List.count w) (List.take_append_drop 128 L.x)
    have hp := congrArg (List.count w) (List.take_append_drop 128 L.pad)
    have hr := (List.take_sublist 258 L.r).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.integer,
      KaratsubaSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hx hp ⊢
    omega
  have ir : L.reduction.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hz := congrArg (List.count w) (List.take_append_drop 256 L.z)
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.reduction,
      SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h hz ⊢
    omega
  have io : L.output.toModAddCoreLayout.wires.toFinset⊆L.wires.toFinset := by
    intro w hm
    have h := List.count_pos_iff.mpr (List.mem_toFinset.mp hm)
    have hr := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 256 L.carry).count_le w
    apply List.mem_toFinset.mpr
    apply List.count_pos_iff.mp
    simp only [SquareSubLayout.wires,SquareSubLayout.work,SquareSubLayout.output,
      ModAddCoreLayout.wires,ModAddCoreLayout.z,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hk := signedKaratsubaSquare_wires_subset L.integer (L.integer_valid hw hn)
  have hr := squareReduce_wires_subset L.reduction (L.reduction_widths hw)
  have ho : wires (modSubInPlace L.output SquareReduction.p)⊆L.wires.toFinset := by
    rw [modSubInPlace_wires L.output 256 SquareReduction.p (L.output_widths hw) (by omega)]
    exact io
  simp only [signedSquareSub,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hk.1.trans ik,hr.1.trans ir⟩,ho⟩,hr.2.trans ir⟩,hk.2.trans ik⟩

end ECDSAAdd.Arithmetic
