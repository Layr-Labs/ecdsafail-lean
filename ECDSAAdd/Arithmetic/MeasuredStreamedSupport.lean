import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.MeasuredStreamedResources
import ECDSAAdd.Arithmetic.PointStreamedSquare

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private def Contains (S : Finset Wire) (xs : List Wire) : Prop := ∀q∈xs,q∈S
private theorem Contains.take {S : Finset Wire} {xs : List Wire} (h : Contains S xs) (n : Nat) :
    Contains S (xs.take n) := fun q hq => h q (List.mem_of_mem_take hq)
private theorem Contains.drop {S : Finset Wire} {xs : List Wire} (h : Contains S xs) (n : Nat) :
    Contains S (xs.drop n) := fun q hq => h q (List.mem_of_mem_drop hq)
private theorem Contains.append {S : Finset Wire} {xs ys : List Wire}
    (hx : Contains S xs) (hy : Contains S ys) : Contains S (xs++ys) := by
  intro q hq
  rcases List.mem_append.mp hq with h|h
  · exact hx q h
  · exact hy q h

private theorem contains_finset {S : Finset Wire} {xs : List Wire} (h : Contains S xs) :
    xs.toFinset⊆S := fun q hq => h q (List.mem_toFinset.mp hq)

private def Ambient (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Finset Wire :=
  (control::L.wires).toFinset

private theorem measured_banks_contained (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    Contains (L.Ambient control) L.inputBank ∧
    Contains (L.Ambient control) L.leafCarry ∧
    Contains (L.Ambient control) L.leafPad ∧
    Contains (L.Ambient control) L.foldCarry ∧
    Contains (L.Ambient control) L.shortCarry := by
  have work : Contains (L.Ambient control) L.core.work := by
    intro q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have pad : Contains (L.Ambient control) L.foldPad := by
    intro q hq
    simp only [foldPad,List.mem_append] at hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires]
    tauto
  have carries : Contains (L.Ambient control) L.foldCarry := by
    intro q hq
    simp only [foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact pad q hq
    all_goals simp [Ambient,wires,CuccaroStreamedSquareLayout.wires]
  exact ⟨work.take 129,(work.drop 129).append ((pad.drop 1).take 130),
    pad.take 1,carries,carries.take 255⟩

theorem measured_small_support (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires L.normalizeSource⊆L.Ambient control ∧
    ECDSAAdd.wires L.restoreSource⊆L.Ambient control ∧
    ECDSAAdd.wires L.reflectOutput⊆L.Ambient control ∧
    ECDSAAdd.wires (L.measuredCore.program SquareReduction.c SquareReduction.p)⊆L.Ambient control := by
  have banks := L.measured_banks_contained control
  have w : Contains (L.Ambient control) L.core.work := by
    intro q hq; simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have o : Contains (L.Ambient control) L.core.out := by
    intro q hq; simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,hq]
  have bits : Contains (L.Ambient control)
      [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag] := by
    intro q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires] at hq ⊢
    tauto
  have embedWork : (L.core.work++L.shortCarry++[L.core.cin,L.core.normFlag]).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact (w.append banks.2.2.2.2).append (by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  have ge := (compareConstantGe_wires_subset L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p).trans embedWork
  have addEmbed : ((some L.core.normFlag).toList++L.core.work++L.shortCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    intro q hq
    apply embedWork
    simp at hq ⊢
    tauto
  have add := (mappedConstAdd_wires_subset (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c).trans addEmbed
  have undo := (mappedConstAdd_wires_subset (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p).trans addEmbed
  have reflected := mappedConstAdd_wires_subset none L.core.out L.shortCarry L.core.cin SquareReduction.p
  have refEmbed : (Option.toList (none : Option Wire)++L.core.out++L.shortCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    apply contains_finset
    simpa using (o.append banks.2.2.2.2).append (show Contains (L.Ambient control) [L.core.cin] from by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  have rr := reflected.trans refEmbed
  have core := L.measuredCore.program_wires_subset SquareReduction.c SquareReduction.p
  have coreEmbed : L.measuredCore.wires.toFinset⊆L.Ambient control := by
    apply contains_finset
    change Contains (L.Ambient control) (L.core.work++L.core.out++L.foldCarry++
      [L.core.outHigh,L.core.cin,L.core.modFlag])
    exact ((w.append o).append banks.2.2.2.1).append (by
      intro q hq; apply bits q; simp at hq ⊢; tauto)
  refine ⟨?_,?_,?_,core.trans coreEmbed⟩
  · simpa only [normalizeSource,wires_append,Finset.union_subset_iff] using And.intro ge add
  · simpa only [restoreSource,wires_append,Finset.union_subset_iff] using And.intro undo ge
  · simpa only [reflectOutput,wires_append,Finset.union_subset_iff,notRegister_wires] using
      And.intro (contains_finset o) rr

theorem measuredFold_support (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (f : MeasuredSquareFold) (hs : ∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (L.measuredFold f)⊆L.Ambient control := by
  have ops := L.measured_small_support control
  have cp := copyRegister_wires_subset none f.src (L.foldDestination f)
  have embed : (Option.toList (none : Option Wire)++f.src++L.foldDestination f).toFinset⊆L.Ambient control := by
    intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h := hs q hq
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
    · have h := List.mem_of_mem_drop (List.mem_of_mem_take hq)
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
  have copy := cp.trans embed
  cases h : f.canonical <;>
    simp only [measuredFold,h,if_false,if_true,wires_append,wires,Finset.union_subset_iff,Finset.empty_subset] <;>
    tauto

theorem measuredFolds_support (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (orientation : Bool) (items : List MeasuredSquareFold)
    (hs : ∀f∈items,∀q∈f.src,q∈L.core.product) :
    ECDSAAdd.wires (L.measuredFolds orientation items)⊆L.Ambient control := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,ECDSAAdd.wires]
  | cons f fs ih =>
    have fold := L.measuredFold_support control f (hs f (by simp))
    have tail := ih f.negative (by intro f hf; exact hs f (by simp [hf]))
    have reflect := (L.measured_small_support control).2.2.1
    by_cases same : orientation=f.negative <;>
      simp only [measuredFolds,same,if_false,if_true,wires_append,wires,Finset.union_subset_iff,Finset.empty_subset] <;>
      tauto

theorem withMeasuredSquare_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : 2≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length)
    (srcMem : ∀q∈src,q∈L.core.y++[L.core.sumCarry])
    (dstMem : ∀q∈dst,q∈L.core.product)
    (hb : ECDSAAdd.wires body⊆L.Ambient control) :
    ECDSAAdd.wires (L.withMeasuredSquare control src dst body)⊆L.Ambient control := by
  have bank := L.measured_banks_contained control
  have sizes := L.measured_bank_widths hw
  let input := L.inputBank.take src.length
  have inLen : input.length=src.length := by simp [input,sizes.1,hsmax]
  have source : Contains (L.Ambient control) src := by
    intro q hq
    have h := srcMem q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires] at h ⊢
    tauto
  have dest : Contains (L.Ambient control) dst := by
    intro q hq
    have h := dstMem q hq
    simp [Ambient,wires,CuccaroStreamedSquareLayout.wires,h]
  have inputSupport := bank.1.take src.length
  have leaf := mappedSignedSquare_wires_subset input dst L.leafPad L.leafCarry L.core.cin
    (by rw [inLen];exact hd) (by rw [sizes.2.2.1]) (by rw [sizes.2.1,hd];omega)
  have leafEmbed : (input++dst++L.leafPad++L.leafCarry++[L.core.cin]).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact (((inputSupport.append dest).append bank.2.2.1).append bank.2.1).append (by
      intro q hq; simp at hq; subst q
      simp [Ambient,wires,CuccaroStreamedSquareLayout.wires])
  have make := leaf.1.trans leafEmbed
  have clear := leaf.2.trans leafEmbed
  have copyEmbed : ((some control).toList++src++input).toFinset⊆L.Ambient control := by
    apply contains_finset
    exact ((show Contains (L.Ambient control) (some control).toList from by
      intro q hq; simp at hq; subst q; simp [Ambient]).append source).append inputSupport
  have copy := (copyRegister_wires_subset (some control) src input).trans copyEmbed
  have eraseEmbed : (control::src++input).toFinset⊆L.Ambient control := by simpa using copyEmbed
  have erase := (eraseMask_wires_subset control src input).trans eraseEmbed
  simpa only [withMeasuredSquare,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro copy make) erase) hb) copy) clear) erase

private theorem nafItems_inside (src product : List Wire) (negative : Bool)
    (hs : ∀q∈src,q∈product) :
    ∀f∈nafMinusOneItems negative src,∀q∈f.src,q∈product := by
  intro f hf q hq
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> exact hs q hq

private theorem shiftedItems_inside (src product : List Wire) (negative : Bool) (j : Nat)
    (hs : ∀q∈src,q∈product) :
    ∀f∈shiftedProductItems negative src j,∀q∈f.src,q∈product := by
  intro f hf q hq
  by_cases zero : j=0
  · simp [shiftedProductItems,zero] at hf
    subst f
    exact hs q hq
  · simp only [shiftedProductItems,zero,if_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|hf
    · simp only [rotateFull,List.mem_append] at hq
      rcases hq with hq|hq
      · exact hs q (List.mem_of_mem_drop hq)
      · exact hs q (List.mem_of_mem_take hq)
    · exact nafItems_inside (src.drop (256-j)) product negative
        (fun q hq => hs q (List.mem_of_mem_drop hq)) f hf q hq

theorem measured_items_support (L : CuccaroStreamedSquareWideLayout) :
    (∀f∈L.measuredAItems,∀q∈f.src,q∈L.core.product) ∧
    (∀f∈L.measuredBItems,∀q∈f.src,q∈L.core.product) ∧
    (∀f∈L.measuredCItems,∀q∈f.src,q∈L.core.product) := by
  have take : ∀q∈L.core.product.take 256,q∈L.core.product := fun _ h => List.mem_of_mem_take h
  have drop : ∀q∈L.core.product.drop 128,q∈L.core.product := fun _ h => List.mem_of_mem_drop h
  have rotate : ∀q∈L.rotated128,q∈L.core.product := by
    intro q hq
    simp only [rotated128,List.mem_append] at hq
    rcases hq with hq|hq
    · exact List.mem_of_mem_drop (List.mem_of_mem_take hq)
    · exact List.mem_of_mem_take hq
  have naf0 := nafItems_inside (L.core.product.drop 128) L.core.product false drop
  have naf1 := nafItems_inside (L.core.product.drop 128) L.core.product true drop
  have sh0 := shiftedItems_inside (L.core.product.take 256) L.core.product true 0 take
  have sh4 := shiftedItems_inside (L.core.product.take 256) L.core.product true 4 take
  have sh6 := shiftedItems_inside (L.core.product.take 256) L.core.product false 6 take
  have sh10 := shiftedItems_inside (L.core.product.take 256) L.core.product true 10 take
  have sh32 := shiftedItems_inside (L.core.product.take 256) L.core.product true 32 take
  refine ⟨?_,?_,?_⟩
  · intro f hf q hq
    simp only [measuredAItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (rfl|rfl)|hf
    · exact take q hq
    · exact rotate q hq
    · exact naf0 f hf q hq
  · intro f hf q hq
    simp only [measuredBItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (((((rfl|hf)|hf)|hf)|hf)|hf)|hf
    · exact rotate q hq
    · exact naf0 f hf q hq
    · exact sh0 f hf q hq
    · exact sh4 f hf q hq
    · exact sh6 f hf q hq
    · exact sh10 f hf q hq
    · exact sh32 f hf q hq
  · intro f hf q hq
    simp only [measuredCItems,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with (rfl|hf)|rfl
    · exact rotate q hq
    · exact naf1 f hf q hq
    · exact List.mem_of_mem_drop hq

theorem measuredProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (L.measuredProgram control)⊆(control::L.wires).toFinset := by
  have items := L.measured_items_support
  have a := L.measuredFolds_support control false L.measuredAItems items.1
  have b := L.measuredFolds_support control false L.measuredBItems items.2.1
  have c := L.measuredFolds_support control true L.measuredCItems items.2.2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa := L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb := L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc := L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems) (by omega) (by omega) (by rw [hw.core.product,sum])
    (by
      intro q hq
      simp only [CuccaroStreamedSquareLayout.sum,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl
      · exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq))
      · simp)
    (fun _ hq => hq) c
  have sumCert := L.sum_certified hw hn
  have embed : L.wires.toFinset⊆L.Ambient control := by intro q hq; simp [Ambient,hq]
  have prep := sumCert.1.2.trans embed
  have unprep := sumCert.2.2.trans embed
  have reflection := (L.measured_small_support control).2.2.1
  change ECDSAAdd.wires (L.measuredProgram control)⊆L.Ambient control
  simpa only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
