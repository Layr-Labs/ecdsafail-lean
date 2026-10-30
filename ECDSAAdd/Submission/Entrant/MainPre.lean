import Mathlib.Tactic.FinCases
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedConvertPhysical
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Arithmetic.EntryForwardSelectedPoolRestore
import ECDSAAdd.Arithmetic.PenultimateMappedForward
import ECDSAAdd.Arithmetic.PenultimateMappedInverse
import ECDSAAdd.Arithmetic.PenultimateMappedResources
import ECDSAAdd.Arithmetic.MappedFieldPhysical
import ECDSAAdd.Arithmetic.Registers
import ECDSAAdd.Arithmetic.PhysicalSupportRename
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.CompressedCompactSupport
import ECDSAAdd.Arithmetic.CompressedFieldFullEncoding
import ECDSAAdd.Arithmetic.CompressedPlacementTransport
import ECDSAAdd.Arithmetic.CompressedFieldWindowTransport
import ECDSAAdd.Arithmetic.PairFrameUnique
import ECDSAAdd.Arithmetic.MappedCompressedCleanTransport
import ECDSAAdd.Arithmetic.BalancedInverseComposeFold
import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProof
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseProof
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment
import ECDSAAdd.Baselines.SkywalkCertificate
import ECDSAAdd.Baselines.SlotField
import ECDSAAdd.Arithmetic.EndpointSwapTrimProof
import ECDSAAdd.Framework.RunThreeStates
import ECDSAAdd.Framework.PacketSequenceFrame
import ECDSAAdd.Arithmetic.EntrySelectedSwapFrame
import ECDSAAdd.Arithmetic.MeasuredStreamedSquare
import ECDSAAdd.Arithmetic.SwapLow
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.TriangularSquareProof
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Arithmetic.MeasuredStreamedSquareProof
import ECDSAAdd.Arithmetic.MeasuredStreamedSupport
import ECDSAAdd.Arithmetic.MeasuredStreamedPhysical
import ECDSAAdd.Baselines.SlotStreamedSquare
import ECDSAAdd.Arithmetic.MeasuredStreamedViews
import Mathlib.Tactic
import ECDSAAdd.Arithmetic.CompressedPointSquareCorrect
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SkywalkSlots
import Mathlib.Tactic.ReduceModChar
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.CompressedPointDialogSteps
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
import ECDSAAdd.Arithmetic.SkywalkPointPhysical
import ECDSAAdd.Arithmetic.BalancedFieldConvertProof
import ECDSAAdd.Arithmetic.ConstantBorrow
import ECDSAAdd.Arithmetic.TrailingZeroCompare
import ECDSAAdd.Baselines.SlotBalanced
import ECDSAAdd.Arithmetic.FieldRenameCells
import ECDSAAdd.Arithmetic.NativeFirstDirectCallerStates
import ECDSAAdd.Arithmetic.MappedKernelPhysical
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Arithmetic.MappedCompressedPointArithmetic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import ECDSAAdd.Arithmetic.CompressedCompactReverseProgram
import ECDSAAdd.Arithmetic.NativeFirstDirectTailRestore
import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Baselines.SlotCodec
import ECDSAAdd.Arithmetic.LiteralConstPhysical
import ECDSAAdd.Math.SquareReduction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import ECDSAAdd.Framework.CleanWireRebind
import ECDSAAdd.Arithmetic.CompressedCompactRestore
import ECDSAAdd.Arithmetic.CompressedCompactStage
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment
import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptReplay
import ECDSAAdd.Arithmetic.MappedCompressedConversionNaturality
import ECDSAAdd.Arithmetic.EntryInverseFirstGroupFrame
import ECDSAAdd.Arithmetic.MappedCompressedGroupsFrame
import ECDSAAdd.Arithmetic.EntryMappedFieldSegmentTrimForward
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptSupport
import ECDSAAdd.Arithmetic.ParametricPointDialogSteps
import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedFieldSupport
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptKernelSupport
import ECDSAAdd.Arithmetic.BalancedTranscriptReplay
import ECDSAAdd.Arithmetic.Constant
import ECDSAAdd.Arithmetic.FieldRenameKernels
import ECDSAAdd.Framework.FiniteUnitary
import ECDSAAdd.Arithmetic.PhysicalGateCheck
import ECDSAAdd.Math.SkywalkTerminalLastControls



section

/-! Codec-independent biased/short kernel proof cache. Experimental extraction only; never a gate for the already frozen submission. Public source and model credits remain in the candidate note. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 1024

section
-- ===== BiasedProgram =====
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.BiasedCircuit
open Arithmetic Arithmetic.BalancedField

abbrev Layout := Arithmetic.BalancedCircuit.Layout

def jh : Nat := 2^30+244

def biasBits (L : Layout) : List MappedBit :=
  (List.range 255).map (fun i => {wire:=some L.lower,flip:=jh.testBit i})++
    [{wire:=some L.one,flip:=false}]

def prepareFold (L : Layout) : Program :=
  [.CX L.one L.lower,.CCX L.parity L.lower L.minus,.CX L.parity L.r0]

def signView (L : Layout) : Program := [.CX L.parity L.one,.CX L.lower L.one]

def fold (L : Layout) : Program :=
  mappedAdd (biasBits L) L.r (L.carry.take 255) L.minus

def releaseSelectors (L : Layout) : Program :=
  [.CX L.parity L.lower,.CX L.rmsb L.lower,.CX L.rmsb L.one,
    .measureX L.minus [] [.Z L.parity,.CZ L.parity L.rmsb]]

def flipBias (L : Layout) : Program := [.X (L.rtail.getD 253 0)]

def biasedPrefix (L : Layout) : Program :=
  BalancedCircuit.seedViews L++(BalancedCircuit.rawAdd L++(prepareFold L++
    (rotateRight (BalancedCircuit.rawTarget L)++(signView L++(fold L++
      (releaseSelectors L++(BalancedCleanup.prepareSign L.toLayout++flipBias L)))))))

def cleanupSuffix (L : Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++
    (compareLt none L.y L.r L.carry L.one L.parity++
      ((BalancedCleanup.prepareCompare L.toLayout).reverse++
        (BalancedCleanup.unnormalize L.toLayout++
          ((BalancedCleanup.prepareSign L.toLayout).reverse++[.CX L.ymsb L.sourceGuard]))))

def program (L : Layout) : Program := biasedPrefix L++cleanupSuffix L

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1022 ∧ measurementCount (program L)=1022 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have rw := BalancedCircuit.widths L hw
  have ra := addInPlace_counts (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L)
    L.carry L.sign (by omega) (by omega)
  have fa := mappedAdd_counts (biasBits L) L.r (L.carry.take 255) L.minus
    (by simp [biasBits,w.2.1]) (by simp [List.length_take,hw.2.2,w.2.1])
  have cm := signComplement_counts L.sign (BalancedCircuit.rawSource L)
  have pc := signComplement_counts L.lower L.r
  have ps := signComplement_counts L.sign L.y
  have pl := signComplement_counts L.lower L.y
  have un := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.positiveLiteral (by omega)
  have co := compareLt_counts none L.y L.r L.carry L.one L.parity
    (by omega) (by unfold BalancedCircuit.Layout.Widths BalancedCleanup.Layout.Widths at hw; omega)
  simp only [program,biasedPrefix,cleanupSuffix,prepareFold,fold,signView,releaseSelectors,flipBias,
    BalancedCircuit.seedViews,BalancedCircuit.rawAdd,BalancedCleanup.prepareSign,
    BalancedCleanup.prepareCompare,BalancedCleanup.unnormalize,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    ra.1,ra.2,fa.1,fa.2,cm.1,cm.2,pc.1,pc.2,ps.1,ps.2,pl.1,pl.2,un.1,un.2,co.1,co.2,
    (rotate_counts (BalancedCircuit.rawTarget L)).1,(rotate_counts (BalancedCircuit.rawTarget L)).2.1,
    (rotate_counts L.r).2.2.1,(rotate_counts L.r).2.2.2]
  norm_num [toffoliCount,measurementCount,w.1,w.2.1,rw.2.1]

def virtualBias (N H : Bool) : Nat :=
  (List.range 255).foldr (fun i acc => (jh.testBit i ^^ N).toNat+2*acc) H.toNat

theorem virtualBias_value (N H : Bool) :
    virtualBias N H=(if N then 2^255-1-jh else jh)+2^255*H.toNat := by
  cases N <;> cases H <;> decide

theorem biasBits_value (L : Layout) (s : BasisState) :
    mappedValue (biasBits L) s=virtualBias (s L.lower) (s L.one) := by
  have aux (is : List Nat) :
      mappedValue (is.map (fun i => {wire:=some L.lower,flip:=jh.testBit i})++
        [{wire:=some L.one,flip:=false}]) s=
      is.foldr (fun i acc => (jh.testBit i ^^ s L.lower).toNat+2*acc) (s L.one).toNat := by
    induction is with
    | nil => simp [mappedValue,MappedBit.value]
    | cons i is ih => simp [mappedValue,MappedBit.value,ih]
  exact aux _

def biasedValue (R : Int) : Int := if negative R then R-(jh : Int)-1 else R+jh

theorem biased_bounds (R : Int) (hr : Centered R) :
    -((2^255 : Nat) : Int)≤biasedValue R ∧ biasedValue R<((2^255 : Nat) : Int) ∧
    (biasedValue R<0 ↔ R<0) := by
  have hp := constants
  unfold Centered at hr
  by_cases hn : R<0 <;> simp [biasedValue,negative,hn,jh] <;> norm_num [q,ECDSAAdd.p] at hr ⊢ <;> omega

theorem biased_magnitude (R : Int) (hr : Centered R) :
    (if negative R then 2^256-1-encodeWord 256 (biasedValue R)
      else encodeWord 256 (biasedValue R))=(|R|+(jh : Int)).toNat := by
  have hp := constants
  have ab : 0≤|R|+(jh : Int) ∧ |R|+(jh : Int)<((2^256 : Nat) : Int) := by
    unfold Centered at hr
    have ha : |R|≤q := abs_le.mpr hr
    have ha0 := abs_nonneg R
    norm_num [jh] at ⊢
    omega
  by_cases hn : R<0
  · simp only [negative,hn,decide_true,if_true]
    rw [BalancedCleanup.complement_encoded]
    have eq : -biasedValue R-1=|R|+(jh : Int) := by
      simp [biasedValue,negative,hn,abs_of_neg hn]; ring
    rw [eq]
    exact BalancedCleanup.encoded_nonnegative _ _ ab.1 ab.2
  · simp only [negative,hn,decide_false,Bool.false_eq_true,if_false]
    have eq : biasedValue R=|R|+(jh : Int) := by
      simp [biasedValue,negative,hn,abs_of_nonneg (show 0≤R by omega)]
    rw [eq]
    exact BalancedCleanup.encoded_nonnegative _ _ ab.1 ab.2

theorem fold_arithmetic (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    (encodeWord 257 T/2+virtualBias (decide (T<0)) (negative (halfResult T))+
      (originalParity T && decide (T<0)).toNat)%2^256=
      encodeWord 256 (biasedValue (halfResult T)) := by
  have hr := (halfResult_spec T ht).1
  have hb := biased_bounds (halfResult T) hr
  have a := BalancedFold.encode_shift 257 T (by
    norm_num [q,ECDSAAdd.p] at ht ⊢; omega)
  have b := BalancedFold.encode_shift 256 (biasedValue (halfResult T)) (by
    norm_num only [Nat.reducePow] at hb ⊢; omega)
  have par := originalParity_value T
  have half := (halfResult_spec T ht).2
  have sig := halfResult_sign T ht
  rw [virtualBias_value]
  by_cases he : T%2=0 <;> by_cases hn : T<0
  all_goals
    simp [evenLift,he,show (0≤T)↔¬T<0 by omega,hn] at half
    simp [negative,originalParity,he,hn] at sig
    by_cases hnR : halfResult T<0 <;>
      (try simp [hnR] at sig) <;>
      simp [biasedValue,negative,originalParity,he,hn,hnR] at a b ⊢ <;>
      norm_num [jh,q,ECDSAAdd.p] at a b ht par half ⊢ <;> omega


theorem biasBits_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (biasBits L)) :
    w=L.lower ∨ w=L.one := by
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hw
  rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hb
    subst b
    left
    simpa using hm
  · have he : b={wire:=some L.one,flip:=false} := by simpa using hb
    subst b
    right
    simpa using hm

theorem biased_sign (L : Layout) (hw : L.Widths) (R : Int) (hr : Centered R)
    (s : BasisState) (hs : regValue L.r s=encodeWord 256 (biasedValue R)) :
    s L.rmsb=negative R := by
  have hb := biased_bounds R hr
  have dec := decode_encodeWord 256 (by omega : 0<256) (biasedValue R)
    (by norm_num; exact ⟨hb.1,hb.2.1⟩)
  have val : signedRegValue L.r s=biasedValue R := by
    unfold signedRegValue
    rw [(BalancedCleanup.widths L.toLayout hw).2.1,hs,dec]
  have sign := BalancedCircuit.word_sign L.low L.rmsb s (biasedValue R) val
  rw [sign]
  exact decide_eq_decide.mpr hb.2.2

theorem low_split (L : Layout) (hw : L.Widths) :
    L.low.take 254++[L.rtail.getD 253 0]=L.low := by
  have h : 254<L.low.length := by rw [(BalancedCleanup.widths L.toLayout hw).1]; omega
  have e : L.low.take 254++[L.low.getD 254 0]=L.low.take 255 := by
    conv_rhs => rw [List.take_add_one]
    rw [List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
    rfl
  have d : L.low.getD 254 0=L.rtail.getD 253 0 := rfl
  rw [d,List.take_of_length_le (show L.low.length≤255 by
    rw [(BalancedCleanup.widths L.toLayout hw).1])] at e
  exact e

theorem flipBias_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hv : regValue L.r s.basis=(|R|+(jh : Int)).toNat) :
    regValue L.r (run (flipBias L) m s).basis=encodeWord 255 (normalizedR R) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have dr := (List.nodup_append'.mp (L.toLayout.dataND n0)).1
  have dl : L.low.Nodup := (List.nodup_append'.mp dr).1
  have split := low_split L hw
  have nsplit : (L.low.take 254++[L.rtail.getD 253 0]).Nodup := by rw [split]; exact dl
  have len : (L.low.take 254).length=254 := by simp [List.length_take,w.1]
  have v := BalancedCleanup.bias_value (L.low.take 254) (L.rtail.getD 253 0) nsplit s m
  rw [split,len] at v
  have hp := constants
  have absb : |R|≤q := abs_le.mpr hr
  have ab0 := abs_nonneg R
  have m0 : 0≤|R|+(jh : Int) := by norm_num [jh]; omega
  have m1 : |R|+(jh : Int)<((2^255 : Nat) : Int) := by
    norm_num [q,ECDSAAdd.p,jh] at absb ⊢; omega
  have cast := Int.toNat_of_nonneg m0
  have msb := regValue_highBit L.low L.rmsb s.basis
  rw [w.1] at msb
  change s.basis L.rmsb=true ↔ 2^255≤regValue L.r s.basis at msb
  have rm : s.basis L.rmsb=false := by
    rw [hv] at msb
    cases h : s.basis L.rmsb <;> simp_all <;> omega
  have low : regValue L.low s.basis=(|R|+(jh : Int)).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append] at hv
    simpa [regValue,rm] using hv
  rw [low] at v
  have normalized : normalizedR R=|R|-h := by
    by_cases hn : R<0
    · simp [normalizedR,magnitude,signBit,negative,hn,abs_of_neg hn]; ring
    · simp [normalizedR,magnitude,signBit,negative,hn,abs_of_nonneg (show 0≤R by omega)]
  have rel : h+(jh : Int)=((2^254 : Nat) : Int) := by decide
  have nr := normalizedR_bounds R hr
  have en := BalancedFold.encode_shift 255 (normalizedR R) (by norm_num; omega)
  have out := regValue_lt L.low (run (flipBias L) m s).basis
  rw [w.1] at out
  have fm : (run (flipBias L) m s).basis L.rmsb=false := by
    have away : L.rtail.getD 253 0∈L.low := by
      rw [←split]; simp
    have ne : L.rmsb≠L.rtail.getD 253 0 := by
      intro e
      exact List.disjoint_left.mp (List.nodup_append'.mp dr).2.2 (e ▸ away) (by simp)
    simp only [flipBias,run,writeBit,Function.update_of_ne ne,rm]
  have full : regValue L.r (run (flipBias L) m s).basis=
      regValue L.low (run (flipBias L) m s).basis := by
    simp [BalancedCleanup.Layout.r,regValue_append,regValue,fm]
  rw [full]
  change (regValue L.low (run (flipBias L) m s).basis : Int)=_ at v
  unfold signedDecode at v
  rw [cast] at v
  by_cases hm : (|R|+(jh : Int)).toNat<2^254 <;>
    simp only [hm,if_true,if_false] at v <;>
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at v en rel ⊢ <;>
    omega


theorem prepareFold_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false) (hm : s.basis L.minus=false) :
    run (prepareFold L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower N) L.minus (P && N)) L.r0 false⟩ := by
  have nd : [L.one,L.parity,L.r0,L.lower,L.minus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (BalancedCircuit.scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have n01 : L.one≠L.parity := by tauto
  have n10 := Ne.symm n01
  have n02 : L.one≠L.r0 := by tauto
  have n20 := Ne.symm n02
  have n03 : L.one≠L.lower := by tauto
  have n30 := Ne.symm n03
  have n04 : L.one≠L.minus := by tauto
  have n40 := Ne.symm n04
  have n12 : L.parity≠L.r0 := by tauto
  have n21 := Ne.symm n12
  have n13 : L.parity≠L.lower := by tauto
  have n31 := Ne.symm n13
  have n14 : L.parity≠L.minus := by tauto
  have n41 := Ne.symm n14
  have n23 : L.r0≠L.lower := by tauto
  have n32 := Ne.symm n23
  have n24 : L.r0≠L.minus := by tauto
  have n42 := Ne.symm n24
  have n34 : L.lower≠L.minus := by tauto
  have n43 := Ne.symm n34
  cases P <;> cases N
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqr : q=L.r0 <;>
      simp_all [prepareFold,run,writeBit,Function.update]

theorem signView_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=false)
    (hl : s.basis L.lower=N) :
    run (signView L) m s=⟨s.phase,writeBit s.basis L.one (P ^^ N)⟩ := by
  have nd : [L.one,L.parity,L.lower].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (BalancedCircuit.scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have n01 : L.one≠L.parity := by tauto
  have n10 := Ne.symm n01
  have n02 : L.one≠L.lower := by tauto
  have n20 := Ne.symm n02
  have n12 : L.parity≠L.lower := by tauto
  have n21 := Ne.symm n12
  cases P <;> cases N
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqo : q=L.one <;> simp_all [signView,run,writeBit,Function.update]

theorem releaseSelectors_run (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (hh : s.basis L.rmsb=H)
    (hl : s.basis L.lower=(H ^^ P)) (hm : s.basis L.minus=(P && !H))
    (ho : s.basis L.one=H) :
    run (releaseSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower false) L.one false) L.minus false⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.one,L.minus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (BalancedCircuit.scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have n01 : L.parity≠L.rmsb := by tauto
  have n10 := Ne.symm n01
  have n02 : L.parity≠L.lower := by tauto
  have n20 := Ne.symm n02
  have n03 : L.parity≠L.one := by tauto
  have n30 := Ne.symm n03
  have n04 : L.parity≠L.minus := by tauto
  have n40 := Ne.symm n04
  have n12 : L.rmsb≠L.lower := by tauto
  have n21 := Ne.symm n12
  have n13 : L.rmsb≠L.one := by tauto
  have n31 := Ne.symm n13
  have n14 : L.rmsb≠L.minus := by tauto
  have n41 := Ne.symm n14
  have n23 : L.lower≠L.one := by tauto
  have n32 := Ne.symm n23
  have n24 : L.lower≠L.minus := by tauto
  have n42 := Ne.symm n24
  have n34 : L.one≠L.minus := by tauto
  have n43 := Ne.symm n34
  cases P <;> cases H <;> cases hr : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqo : q=L.one <;>
        simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]

theorem prepareSign_biased (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hv : regValue L.r s.basis=encodeWord 256 (biasedValue R)) (hl : s.basis L.lower=false) :
    let t := run (BalancedCleanup.prepareSign L.toLayout) m s
    t.phase=s.phase ∧ regValue L.r t.basis=(|R|+(jh : Int)).toNat ∧
    t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) := by
  let c : State := ⟨s.phase,writeBit s.basis L.lower (negative R)⟩
  have la : L.lower∉L.r := fun h => BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [h])
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have dr := (List.nodup_append'.mp (L.toLayout.dataND n0)).1
  have sign := biased_sign L hw R hr s.basis hv
  have first (ms : List Bool) : run [.CX L.rmsb L.lower] ms s=c := by
    simp [run,c,writeBit,hl,sign]
  have body := signComplement_correct L.lower L.r dr la c m
  have before : regValue L.r c.basis=encodeWord 256 (biasedValue R) := by
    exact (regValue_congr _ _ _ (fun q hq => by
      simp [c,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])).trans hv
  simp only [BalancedCleanup.prepareSign,run_append,run_take,measurementCount,List.drop_zero,first]
  refine ⟨body.1,?_,?_,?_⟩
  · rw [body.2.2,before,show c.basis L.lower=negative R by simp [c,writeBit],
      (BalancedCleanup.widths L.toLayout hw).2.1,biased_magnitude R hr]
  · exact (body.2.1 L.lower la).trans (by simp [c,writeBit])
  · intro q hq hn
    exact (body.2.1 q hq).trans (by simp [c,writeBit,hn])


theorem no_measurement_phase (p : Program) (hm : measurementCount p=0) (s : State) (m : List Bool) :
    (run p m s).phase=s.phase := by
  induction p generalizing s m with
  | nil => rfl
  | cons i p ih => cases i <;> simp_all [measurementCount,run]



end ECDSAAdd.Entrant.BiasedCircuit

#print axioms ECDSAAdd.Entrant.BiasedCircuit.counts
#print axioms ECDSAAdd.Entrant.BiasedCircuit.fold_arithmetic

end

section
-- ===== BiasedPrefix =====
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.BiasedCircuit
open Arithmetic Arithmetic.BalancedField

structure PrefixPost (L : Layout) (R : Int) (P : Bool) (s t : State) : Prop where
  phase : t.phase=s.phase
  value : regValue L.r t.basis=encodeWord 255 (normalizedR R)
  lower : t.basis L.lower=negative R
  parity : t.basis L.parity=P
  guard : t.basis L.sourceGuard=s.basis L.ymsb
  frame : ∀q,q∉L.r → q≠L.lower → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q

def referencePrefix (L : Layout) : Program :=
  BalancedCircuit.coreProgram L++
    (BalancedCleanup.prepareSign L.toLayout++BalancedCleanup.normalize L.toLayout)

theorem referencePost (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    PrefixPost L (halfResult (rawSum B X Y)) (originalParity (rawSum B X Y)) s
      (run (referencePrefix L) m s) := by
  let R := halfResult (rawSum B X Y)
  let ms := m.drop (measurementCount (BalancedCircuit.coreProgram L))
  generalize ec : run (BalancedCircuit.coreProgram L) m s=c
  generalize ed : run (BalancedCleanup.prepareSign L.toLayout) ms c=d
  generalize ee : run (BalancedCleanup.normalize L.toLayout) ms d=e
  have core := BalancedCircuit.core_correct L hw hn B X Y hx hy s m hs hr hyr hc
  rw [ec] at core
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have cen : Centered R := (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have prep := BalancedCleanup.prepareSign_value L.toLayout hw n0 R cen c ms
    core.2.1 (core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean]))
  rw [ed] at prep
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.one]++L.y++L.carry) :
      q∉L.r ∧ q≠L.lower := by
    have rd : (L.r++([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.one]++L.y++L.carry)).Nodup := by
      apply List.nodup_iff_count.mpr
      intro w
      have c := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) w
      simp only [List.count_append,List.count_cons,List.count_nil] at c ⊢
      omega
    have ld : (L.lower::([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.one]++L.y++L.carry)).Nodup := by
      apply List.nodup_iff_count.mpr
      intro w
      have c := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) w
      simp only [List.count_append,List.count_cons,List.count_nil] at c ⊢
      omega
    exact ⟨fun h => List.disjoint_left.mp (List.nodup_append'.mp rd).2.2 h hq,
      fun e => (List.nodup_cons.mp ld).1 (e ▸ hq)⟩
  have one : d.basis L.one=false :=
    (prep.2.2 _ (away _ (by simp)).1 (away _ (by simp)).2).trans
      (core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean]))
  have clean : ∀q∈L.carry,d.basis q=false := by
    intro q hq
    exact (prep.2.2 _ (away _ (by simp [hq])).1 (away _ (by simp [hq])).2).trans
      (core.2.2.2.2.1 _ (by simp [BalancedCircuit.coreClean,hq]))
  have rm0 : d.basis L.rmsb=false := by
    have bit := regValue_highBit L.low L.rmsb d.basis
    rw [(BalancedCleanup.widths L.toLayout hw).1] at bit
    change d.basis L.rmsb=true ↔ 2^255≤regValue L.r d.basis at bit
    rw [prep.1] at bit
    have mag := magnitude_bounds R cen
    have hp := constants
    have cast := Int.toNat_of_nonneg mag.1
    cases h : d.basis L.rmsb <;> simp_all <;> omega
  have lo : regValue L.low d.basis=(magnitude R).toNat := by
    have v := prep.1
    rw [BalancedCleanup.Layout.r,regValue_append] at v
    simpa [regValue,rm0] using v
  have norm := BalancedCleanup.normalize_value L.toLayout hw n0 R cen d ms lo prep.2.1 one clean
  rw [ee] at norm
  have ef (q : Wire) (hq : q∉L.r) (hl : q≠L.lower) : e.basis q=c.basis q :=
    (norm.2.2 q (fun h => hq (by simp [BalancedCleanup.Layout.r,h]))).trans (prep.2.2 q hq hl)
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have val : regValue L.r e.basis=encodeWord 255 (normalizedR R) := by
    rw [BalancedCleanup.Layout.r,regValue_append,norm.2.1]
    have outside : L.rmsb∉L.low := by
      exact fun h => List.disjoint_left.mp (List.nodup_append'.mp
        (List.nodup_append'.mp (L.toLayout.dataND n0)).1).2.2 h (by simp)
    simp [regValue,norm.2.2 _ outside,rm0]
  have mc : measurementCount (BalancedCleanup.prepareSign L.toLayout)=0 := by
    simp [BalancedCleanup.prepareSign,measurementCount_append,measurementCount,
      (signComplement_counts L.lower L.r).2]
  have phaseD : d.phase=c.phase := by
    rw [←ed]
    exact no_measurement_phase _ mc _ _
  have actual : run (referencePrefix L) m s=e := by
    rw [referencePrefix,run_append,run_take,ec]
    rw [run_append,run_take,mc,List.drop_zero,ed,ee]
  rw [actual]
  refine ⟨norm.1.trans (phaseD.trans core.1),val,?_,?_,?_,?_⟩
  · exact (norm.2.2 L.lower (fun h => L.toLayout.flagAway n0 L.lower (by simp)
      (by simp [BalancedCleanup.Layout.r,h]))).trans prep.2.1
  · exact (ef _ (away _ (by simp)).1 (away _ (by simp)).2).trans core.2.2.1
  · exact (ef _ (away _ (by simp)).1 (away _ (by simp)).2).trans core.2.2.2.1
  · intro q hqr hql hqp hqg
    exact (ef q hqr hql).trans (core.2.2.2.2.2 q hqr hqp hqg)


theorem foldStates (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (v w a b z t d e : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hv : regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T)
    (hp : v.basis L.parity=originalParity T) (ho : v.basis L.one=decide (T<0))
    (h0 : v.basis L.r0=originalParity T) (hl : v.basis L.lower=false)
    (hm : v.basis L.minus=false) (hc : ∀q∈L.carry,v.basis q=false)
    (ew : run (prepareFold L) m1 v=w)
    (ea : run (rotateRight (BalancedCircuit.rawTarget L)) m2 w=a)
    (eb : run (signView L) m3 a=b) (ez : run (fold L) m4 b=z)
    (et : run (releaseSelectors L) m5 z=t)
    (ed : run (BalancedCleanup.prepareSign L.toLayout) m6 t=d)
    (ee : run (flipBias L) m7 d=e) :
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q) := by
  let P := originalParity T
  let N := decide (T<0)
  let R := halfResult T
  let H := negative R
  have rc : Centered R := (halfResult_spec T ht).1
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have away (f : Wire)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]) :
      f∉BalancedCircuit.rawTarget L := BalancedCircuit.compose_not_raw L hn f hf
  have dataflag (q : Wire) (hq : q∈L.r++L.carry) (f : Wire)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f :=
    by
      intro eq
      have hd : f∈L.r++L.carry := eq ▸ hq
      exact BalancedCircuit.flagAway L hn f hf (by simp only [List.mem_append] at hd ⊢; tauto)
  have wp := prepareFold_run L hn P N v m1 hp ho h0 hl hm
  rw [ew] at wp
  have wf (q : Wire) (ql : q≠L.lower) (qm : q≠L.minus) (q0 : q≠L.r0) :
      w.basis q=v.basis q := by rw [wp]; simp only [writeBit,
        Function.update_of_ne ql,Function.update_of_ne qm,Function.update_of_ne q0]
  have w0 : w.basis L.r0=false := by rw [wp]; simp [writeBit]
  have wl : w.basis L.lower=N := by rw [wp]; simp only [writeBit,
    Function.update_of_ne (show L.lower≠L.r0 by tauto),
    Function.update_of_ne (show L.lower≠L.minus by tauto),Function.update_self]
  have wm : w.basis L.minus=(P && N) := by rw [wp]; simp only [writeBit,
    Function.update_of_ne (show L.minus≠L.r0 by tauto),Function.update_self]
  have shape : BalancedCircuit.rawTarget L=L.r0::BalancedCircuit.foldTarget L := by
    simp [BalancedCircuit.rawTarget,BalancedCircuit.foldTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have wr : regValue (BalancedCircuit.rawTarget L) w.basis=
      2*regValue (BalancedCircuit.foldTarget L) v.basis := by
    rw [shape]
    change (if w.basis L.r0 then 1 else 0)+2*regValue (BalancedCircuit.foldTarget L) w.basis=_
    rw [w0]
    simp only [Bool.false_eq_true,if_false,zero_add]
    congr 1
    apply regValue_congr
    intro q hq
    have qr : q∈BalancedCircuit.rawTarget L := by rw [shape]; simp [hq]
    have nq : q≠L.r0 := fun e => BalancedCircuit.compose_not_fold_r0 L hn (e ▸ hq)
    exact wf q (fun e => away L.lower (by simp) (e ▸ qr))
      (fun e => away L.minus (by simp) (e ▸ qr)) nq
  have rawv : regValue (BalancedCircuit.foldTarget L) v.basis=encodeWord 257 T/2 := by
    rw [shape] at hv
    change (if v.basis L.r0 then 1 else 0)+2*regValue (BalancedCircuit.foldTarget L) v.basis=_ at hv
    rw [h0] at hv
    cases hp0 : originalParity T <;> simp [hp0] at hv <;> omega
  rw [rawv] at wr
  have rot := rotateRight_spec (BalancedCircuit.rawTarget L) (BalancedCircuit.rawTargetND L hn)
    (2*(encodeWord 257 T/2)) (by omega) w m2 wr
  rw [ea] at rot
  have av : regValue (BalancedCircuit.rawTarget L) a.basis=encodeWord 257 T/2 := by
    have val := rot.2
    change regValue (BalancedCircuit.rawTarget L) a.basis=2*(encodeWord 257 T/2)/2 at val
    omega
  have af (q : Wire) (hq : q∉BalancedCircuit.rawTarget L) : a.basis q=w.basis q := by
    simpa only [ea] using (rotate_frame (BalancedCircuit.rawTarget L) w m2).2.1 q hq
  have ao : a.basis L.one=false := by
    have bit := regValue_highBit L.r L.one a.basis
    rw [(BalancedCleanup.widths L.toLayout hw).2.1] at bit
    change a.basis L.one=true ↔ 2^256≤regValue (BalancedCircuit.rawTarget L) a.basis at bit
    rw [av] at bit
    have bound := encodeWord_bound 257 T
    norm_num at bound bit
    cases ba : a.basis L.one <;> simp_all <;> omega
  have ar : regValue L.r a.basis=encodeWord 257 T/2 := by
    rw [BalancedCircuit.rawTarget,regValue_append] at av
    simpa [regValue,ao] using av
  have ap : a.basis L.parity=P :=
    (af _ (away _ (by simp))).trans ((wf _ (by tauto) (by tauto) (by tauto)).trans hp)
  have al : a.basis L.lower=N := (af _ (away _ (by simp))).trans wl
  have bp := signView_run L hn P N a m3 ap ao al
  rw [eb] at bp
  have bf (q : Wire) (hq : q≠L.one) : b.basis q=a.basis q := by
    rw [bp]; simp only [writeBit,Function.update_of_ne hq]
  have bo : b.basis L.one=H := by
    rw [bp]
    simp only [writeBit,Function.update_self]
    have sg := halfResult_sign T ht
    change (P ^^ N)=negative (halfResult T)
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    exact Bool.xor_comm _ _
  have bl : b.basis L.lower=N := (bf _ (by tauto)).trans al
  have bpar : b.basis L.parity=P := (bf _ (by tauto)).trans ap
  have bm : b.basis L.minus=(P && N) :=
    (bf _ (by tauto)).trans ((af _ (away _ (by simp))).trans wm)
  have br : regValue L.r b.basis=encodeWord 257 T/2 :=
    (regValue_congr _ _ _ (fun q hq => bf q (dataflag q (by simp [hq]) _ (by simp)))).trans ar
  have bc : ∀q∈L.carry,b.basis q=false := by
    intro q hq
    have ql := dataflag q (by simp [hq]) L.lower (by simp)
    have qm := dataflag q (by simp [hq]) L.minus (by simp)
    have qo := dataflag q (by simp [hq]) L.one (by simp)
    have q0 : q≠L.r0 := by
      intro eq
      have raw := BalancedCircuit.compose_raw_away L hn q (by simp [hq])
      exact raw (by simp [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,eq])
    exact (bf q qo).trans ((af q (BalancedCircuit.compose_raw_away L hn q (by simp [hq]))).trans
      ((wf q ql qm q0).trans (hc q hq)))
  have fd : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have fs : ∀q∈mappedWires (biasBits L),q∉L.minus::(L.r++L.carry.take 255) := by
    intro q hq hmem
    have src := biasBits_sources L q hq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have add := mappedAdd_correct (biasBits L) L.r (L.carry.take 255) L.minus fd fs
    (by simp [biasBits,(BalancedCleanup.widths L.toLayout hw).2.1])
    (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1])
    b m4 (fun q hq => bc q (List.mem_of_mem_take hq))
  simp only [show mappedAdd (biasBits L) L.r (L.carry.take 255) L.minus=fold L from rfl,ez] at add
  have zv : regValue L.r z.basis=encodeWord 256 (biasedValue R) := by
    rw [add.2.2,biasBits_value,br,bl,bo,bm,(BalancedCleanup.widths L.toLayout hw).2.1]
    simpa only [Nat.add_comm] using fold_arithmetic T ht
  have zr : z.basis L.rmsb=H := biased_sign L hw R rc z.basis zv
  have zp : z.basis L.parity=P :=
    (add.2.1 _ (fun h => away L.parity (by simp) (by simp [BalancedCircuit.rawTarget,h]))).trans bpar
  have zl : z.basis L.lower=(H ^^ P) := by
    rw [add.2.1 _ (fun h => away L.lower (by simp) (by simp [BalancedCircuit.rawTarget,h])),bl]
    have sg := halfResult_sign T ht
    change N=(negative (halfResult T) ^^ P)
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    cases N <;> cases P <;> rfl
  have zm : z.basis L.minus=(P && !H) := by
    rw [add.2.1 _ (fun h => away L.minus (by simp) (by simp [BalancedCircuit.rawTarget,h])),bm]
    have sg := halfResult_sign T ht
    change (P && N)=(P && !negative (halfResult T))
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    cases N <;> cases P <;> rfl
  have zo : z.basis L.one=H := (add.2.1 _ (fun h =>
    BalancedCircuit.flagAway L hn L.one (by simp) (by simp [h]))).trans bo
  have rel := releaseSelectors_run L hn P H z m5 zp zr zl zm zo
  rw [et] at rel
  have tf (q : Wire) (ql : q≠L.lower) (qo : q≠L.one) (qm : q≠L.minus) : t.basis q=z.basis q := by
    rw [rel]
    simp only [writeBit,Function.update_of_ne ql,Function.update_of_ne qo,Function.update_of_ne qm]
  have tl : t.basis L.lower=false := by rw [rel]; simp only [writeBit,
    Function.update_of_ne (show L.lower≠L.minus by tauto),
    Function.update_of_ne (show L.lower≠L.one by tauto),Function.update_self]
  have cleanOne : t.basis L.one=false := by rw [rel]; simp only [writeBit,
    Function.update_of_ne (show L.one≠L.minus by tauto),Function.update_self]
  have tm : t.basis L.minus=false := by rw [rel]; simp [writeBit]
  have tv : regValue L.r t.basis=encodeWord 256 (biasedValue R) := by
    apply Eq.trans _ zv
    apply regValue_congr
    intro q hq
    exact tf q (dataflag q (by simp [hq]) _ (by simp))
      (dataflag q (by simp [hq]) _ (by simp)) (dataflag q (by simp [hq]) _ (by simp))
  have ps := prepareSign_biased L hw hn R rc t m6 tv tl
  rw [ed] at ps
  have fl := flipBias_value L hw hn R rc d m7 ps.2.1
  rw [ee] at fl
  have ef (q : Wire) (hq : q∉L.r) : e.basis q=d.basis q := by
    rw [←ee]
    have mem : L.rtail.getD 253 0∈L.r := by
      have sp := low_split L hw
      have ml : L.rtail.getD 253 0∈L.low := by rw [←sp]; simp
      exact List.mem_append_left _ ml
    simp only [flipBias,run,writeBit,Function.update_of_ne (show q≠L.rtail.getD 253 0 from fun e => hq (e ▸ mem))]
  have toR (f : Wire) (hf : f∈[L.one,L.minus,L.lower]) : f∉L.r := by
    intro h
    exact BalancedCircuit.flagAway L hn f (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto) (by simp [h])
  have phase : e.phase=v.phase := by
    have ephase : e.phase=d.phase := by rw [←ee]; rfl
    have tphase : t.phase=z.phase := by rw [rel]
    have bphase : b.phase=a.phase := by rw [bp]
    have wphase : w.phase=v.phase := by rw [wp]
    exact ephase.trans (ps.1.trans (tphase.trans
      (add.1.trans (bphase.trans (rot.1.trans wphase)))))
  refine ⟨phase,fl,?_,?_,?_,?_⟩
  · exact (ef _ (toR _ (by simp))).trans ps.2.2.1
  · exact (ef _ (toR _ (by simp))).trans ((ps.2.2.2 _ (toR _ (by simp)) (by tauto)).trans cleanOne)
  · exact (ef _ (toR _ (by simp))).trans ((ps.2.2.2 _ (toR _ (by simp)) (by tauto)).trans tm)
  · intro q hqr hql hqm
    have qo : q≠L.one := fun eq => hqr (by simp [BalancedCircuit.rawTarget,eq])
    have qr : q∉L.r := fun h => hqr (by simp [BalancedCircuit.rawTarget,h])
    have q0 : q≠L.r0 := fun eq => hqr (by simp [BalancedCircuit.rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,eq])
    exact (ef q qr).trans ((ps.2.2.2 q qr hql).trans ((tf q hql qo hqm).trans
      ((add.2.1 q qr).trans ((bf q qo).trans ((af q hqr).trans (wf q hql hqm q0))))))


def remainder (L : Layout) : Program :=
  prepareFold L++(rotateRight (BalancedCircuit.rawTarget L)++(signView L++(fold L++
    (releaseSelectors L++(BalancedCleanup.prepareSign L.toLayout++flipBias L)))))

theorem remainder_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (v : State) (m : List Bool)
    (hv : regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T)
    (hp : v.basis L.parity=originalParity T) (ho : v.basis L.one=decide (T<0))
    (h0 : v.basis L.r0=originalParity T) (hl : v.basis L.lower=false)
    (hm : v.basis L.minus=false) (hc : ∀q∈L.carry,v.basis q=false) :
    let e := run (remainder L) m v
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q) := by
  let P : State → State → Prop := fun v e =>
    regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T →
    v.basis L.parity=originalParity T → v.basis L.one=decide (T<0) →
    v.basis L.r0=originalParity T → v.basis L.lower=false → v.basis L.minus=false →
    (∀q∈L.carry,v.basis q=false) →
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q)
  have run7 := skywalkRunSeven (prepareFold L) (rotateRight (BalancedCircuit.rawTarget L))
    (signView L) (fold L) (releaseSelectors L) (BalancedCleanup.prepareSign L.toLayout) (flipBias L) P
    (by
      intro v w a b z t d e m1 m2 m3 m4 m5 m6 m7 ew ea eb ez et ed ee hv hp ho h0 hl hm hc
      exact foldStates L hw hn T ht v w a b z t d e m1 m2 m3 m4 m5 m6 m7
        hv hp ho h0 hl hm hc ew ea eb ez et ed ee) v m
  exact run7 hv hp ho h0 hl hm hc

theorem prefixPost (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    PrefixPost L (halfResult (rawSum B X Y)) (originalParity (rawSum B X Y)) s
      (run (biasedPrefix L) m s) := by
  let T := rawSum B X Y
  let ms := m.drop (measurementCount (BalancedCircuit.rawAdd L))
  generalize eu : run (BalancedCircuit.seedViews L) m s=u
  generalize ev : run (BalancedCircuit.rawAdd L) m u=v
  generalize et : run (remainder L) ms v=t
  have seed := BalancedCircuit.compose_seed_frame L hw hn s m hc
  rw [eu] at seed
  have sv := BalancedCircuit.seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (BalancedCircuit.seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (BalancedCircuit.seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉BalancedCircuit.rawTarget L) : v.basis q=u.basis q := by
    simpa only [ev] using BalancedCircuit.rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉BalancedCircuit.rawTarget L := BalancedCircuit.compose_raw_away L hn q hq
  have vp : v.basis L.parity=originalParity T := by
    exact (rf _ (away _ (by simp))).trans (by simpa only [eu] using BalancedCircuit.seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=decide (T<0) :=
    BalancedCircuit.word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=originalParity T := by
    apply BalancedCircuit.word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := BalancedCircuit.compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [BalancedCircuit.rawTarget]))
    exact (rf q cv.1).trans ((seed.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have vw := BalancedCircuit.word_encoding (BalancedCircuit.rawTarget L) 257
    (BalancedCircuit.widths L hw).2.1 v.basis T sv.2.1
  have rem := remainder_correct L hw hn T (rawSum_bounds B X Y hx hy) v ms vw vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (fun q hq => vz q (by simp [hq]))
  rw [et] at rem
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have actual : run (biasedPrefix L) m s=t := by
    change run (BalancedCircuit.seedViews L++(BalancedCircuit.rawAdd L++remainder L)) m s=t
    rw [run_append,run_take,show measurementCount (BalancedCircuit.seedViews L)=0 from rfl,
      List.drop_zero,eu,run_append,run_take,ev,et]
  rw [actual]
  refine ⟨rem.1.trans sv.1,rem.2.1,rem.2.2.1,?_,?_,?_⟩
  · exact (rem.2.2.2.2.2 _ (away _ (by simp)) (by tauto) (by tauto)).trans vp
  · exact (rem.2.2.2.2.2 _ (away _ (by simp)) (by tauto) (by tauto)).trans
      ((rf _ (away _ (by simp))).trans seed.2.1)
  · intro q hqr hql hqp hqg
    by_cases qo : q=L.one
    · subst q
      exact rem.2.2.2.1.trans (hc _ (by simp [BalancedCircuit.work])).symm
    by_cases qm : q=L.minus
    · subst q
      exact rem.2.2.2.2.1.trans (hc _ (by simp [BalancedCircuit.work])).symm
    have raw : q∉BalancedCircuit.rawTarget L := by
      simpa [BalancedCircuit.rawTarget] using And.intro hqr qo
    exact (rem.2.2.2.2.2 q raw hql qm).trans
      ((rf q raw).trans (seed.2.2 q hqg qo hqp))


end ECDSAAdd.Entrant.BiasedCircuit

end

section
-- ===== BiasedSupport =====
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.BiasedCircuit
open Arithmetic Arithmetic.BalancedField

/-- One carry bank and six scalar sites, including the input sign. -/
def activeWires (L : Layout) : List Wire := [L.sourceGuard,L.minus]++L.toLayout.wires

theorem activeSites (L : Layout) (hw : L.Widths) : (activeWires L).length=774 := by
  simp [activeWires,BalancedCleanup.Layout.wires,hw.1,hw.2.1,hw.2.2]

theorem support (L : Layout) (hw : L.Widths) : wires (program L)⊆(activeWires L).toFinset := by
  have w := BalancedCircuit.widths L hw
  have member (q : Wire) : q∈(activeWires L).toFinset ↔
      q∈[L.sourceGuard,L.minus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry := by
    simp [activeWires,BalancedCleanup.Layout.wires,or_assoc]
  have cleanup (q : Wire) (hq : q∈wires (BalancedCleanup.program L.toLayout)) :
      q∈(activeWires L).toFinset := by
    have h := BalancedCleanup.support L.toLayout hw hq
    exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp h))
  have ps : wires (BalancedCleanup.prepareSign L.toLayout)⊆(activeWires L).toFinset := by
    intro q hq
    apply cleanup q
    simp only [BalancedCleanup.program,wires_append,Finset.mem_union]
    exact Or.inl hq
  have add := addInPlace_wires (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L)
    L.carry L.sign (by omega) (by omega)
  have comp := signComplement_wires_subset L.sign (BalancedCircuit.rawSource L)
  have raw : wires (BalancedCircuit.rawAdd L)⊆(activeWires L).toFinset := by
    intro q hq
    simp only [BalancedCircuit.rawAdd,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · have h := comp hq
      simp only [member,BalancedCircuit.rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢
      tauto
    · rw [add] at hq
      simp only [member,BalancedCircuit.rawSource,BalancedCircuit.rawTarget,
        BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
        List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢
      tauto
    · have h := comp hq
      simp only [member,BalancedCircuit.rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢
      tauto
  have fs : wires (fold L)⊆(activeWires L).toFinset := by
    intro q hq
    have h := mappedAdd_wires_subset (biasBits L) L.r (L.carry.take 255) L.minus hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton] at h
    rcases h with ((h|h)|h)|h
    · rcases biasBits_sources L q h with he|he <;> exact (member q).mpr (Or.inl (by simp [he]))
    · simp only [member,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_append,
        List.mem_cons,List.not_mem_nil] at h ⊢
      tauto
    · exact (member q).mpr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_take h))))
    · exact (member q).mpr (Or.inl (by simp [h]))
  have seedSmall : wires (BalancedCircuit.seedViews L)⊆
      [L.ymsb,L.sourceGuard,L.rmsb,L.one,L.ylow.getD 0 0,L.parity,L.r0].toFinset := by
    intro q hq
    simp only [BalancedCircuit.seedViews,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil] at hq ⊢
    tauto
  have seed : wires (BalancedCircuit.seedViews L)⊆(activeWires L).toFinset := by
    intro q hq
    have low : L.ylow.getD 0 0∈L.ylow := by
      cases hy : L.ylow with
      | nil => have hh := hw.2.1; simp [hy] at hh
      | cons a as => simp [hy]
    have small := seedSmall hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil] at small
    rcases small with e|e|e|e|e|e|e|e
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inr (Or.inr (Or.inl (by simpa only [e] using low))))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact False.elim e
  have rot : wires (rotateRight (BalancedCircuit.rawTarget L))⊆(activeWires L).toFinset := by
    intro q hq
    rw [(rotate_wires _).1,if_neg (by omega)] at hq
    simp only [member,BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢
    tauto
  have flip : wires (flipBias L)⊆(activeWires L).toFinset := by
    intro q hq
    have mem : L.rtail.getD 253 0∈L.low := by rw [←low_split L hw]; simp
    have lowmem : ∀q∈L.low,q∈(activeWires L).toFinset := by
      intro q hq
      simp only [member,BalancedCleanup.Layout.low,List.mem_cons] at hq ⊢
      tauto
    have he : q=L.rtail.getD 253 0 := by simpa only [flipBias,wires,Instr.wires,
      Finset.union_empty,Finset.mem_singleton] using hq
    exact he ▸ lowmem _ mem
  have pref : wires (biasedPrefix L)⊆(activeWires L).toFinset := by
    intro q hq
    simp only [biasedPrefix,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq|hq|hq|hq|hq
    · exact seed hq
    · exact raw hq
    · simp only [prepareFold,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢
      tauto
    · exact rot hq
    · simp only [signView,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢
      tauto
    · exact fs hq
    · simp only [releaseSelectors,member,wires,Instr.wires,correctionWires,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢
      tauto
    · exact ps hq
    · exact flip hq
  have suf : wires (cleanupSuffix L)⊆(activeWires L).toFinset := by
    intro q hq
    simp only [cleanupSuffix,wires_append,wires_reverse,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq|hq
    · apply cleanup q
      simp only [BalancedCleanup.program,wires_append,Finset.mem_union,or_assoc]
      tauto
    · apply cleanup q
      simp only [BalancedCleanup.program,wires_append,Finset.mem_union,or_assoc]
      tauto
    · apply cleanup q
      simp only [BalancedCleanup.program,wires_append,wires_reverse,Finset.mem_union,or_assoc]
      tauto
    · apply cleanup q
      simp only [BalancedCleanup.program,wires_append,wires_reverse,Finset.mem_union,or_assoc]
      tauto
    · exact ps hq
    · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢
      tauto
  intro q hq
  rw [program,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · exact pref hq
  · exact suf hq

theorem qubitBound (L : Layout) (hw : L.Widths) : qubitCount (program L)≤774 := by
  have h := Finset.card_le_card (support L hw)
  have n := List.toFinset_card_le (activeWires L)
  rw [activeSites L hw] at n
  exact h.trans n


theorem omitted_sites (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.cout∉wires (program L) ∧ L.plus∉wires (program L) := by
  have nd : ([L.cout,L.plus]++activeWires L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [BalancedCircuit.Layout.wires,activeWires,List.count_append,List.count_cons,
      List.count_nil] at h ⊢
    omega
  have away : ∀q∈[L.cout,L.plus],q∉wires (program L) := by
    intro q hq hp
    exact List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 hq
      (List.mem_toFinset.mp (support L hw hp))
  exact ⟨away _ (by simp),away _ (by simp)⟩

end ECDSAAdd.Entrant.BiasedCircuit

#print axioms ECDSAAdd.Entrant.BiasedCircuit.support
#print axioms ECDSAAdd.Entrant.BiasedCircuit.qubitBound

end

section
-- ===== BiasedPhysical =====
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.BiasedCircuit
open Arithmetic RecordedQuantum

/-- The emitted circuit has distinct ordinary gate targets and controls. -/
theorem physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) := by
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have ofProper (p : Program) (hp : ProperProgram p) : GatePhysical p :=
    (physical_embed p).mp (physical_of_proper p hp)
  have seed : GatePhysical (BalancedCircuit.seedViews L) := by
    have nd := BalancedCircuit.seedND L hw hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    simp_all [BalancedCircuit.seedViews,GatePhysical,PhysicalInstr,ProperGate,ne_comm]
  have small : GatePhysical (prepareFold L++signView L++releaseSelectors L++flipBias L) := by
    have nd := BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    simp_all [prepareFold,signView,releaseSelectors,flipBias,GatePhysical,PhysicalInstr,ProperGate,ne_comm]
  have rawND := BalancedCircuit.rawLayoutND L hn
  have comp : GatePhysical (signComplement L.sign (BalancedCircuit.rawSource L)) := by
    apply ofProper
    apply BalancedCleanup.complement_proper
    exact fun h => (List.nodup_cons.mp rawND).1 (List.mem_append_left _ (List.mem_append_left _ h))
  have raw : GatePhysical (BalancedCircuit.rawAdd L) := by
    simp only [BalancedCircuit.rawAdd,gatePhysical_append]
    exact ⟨⟨comp,addInPlace_physical _ _ _ _ rawND⟩,comp⟩
  have fnd : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have mapped : GatePhysical (fold L) := by
    apply mappedAdd_physical _ _ _ _ fnd
    intro b hb q hq hmem
    have mem : q∈mappedWires (biasBits L) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    have src := biasBits_sources L q mem
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have nd := BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append,or_assoc] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have ps := ofProper _ (BalancedCleanup.prepareSign_proper L.toLayout n0)
  have pc := ofProper _ (BalancedCleanup.prepareCompare_proper L.toLayout n0)
  have psr := ofProper _ (properProgram_reverse _ (BalancedCleanup.prepareSign_proper L.toLayout n0))
  have pcr := ofProper _ (properProgram_reverse _ (BalancedCleanup.prepareCompare_proper L.toLayout n0))
  have un : GatePhysical (BalancedCleanup.unnormalize L.toLayout) := by
    simp only [BalancedCleanup.unnormalize,gatePhysical_append]
    exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],
      literalAdd_physical _ _ _ _ _ (List.nodup_cons.mp (L.toLayout.normND n0)).2⟩,
      by simp [GatePhysical,PhysicalInstr,ProperGate]⟩
  have cmp := compareLt_physical none L.y L.r L.carry L.one L.parity
    (L.toLayout.compareND n0) (by simp)
  have last : GatePhysical [.CX L.ymsb L.sourceGuard] := by
    have nd := BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    have ne : L.ymsb≠L.sourceGuard := Ne.symm (by tauto)
    simpa [GatePhysical,PhysicalInstr,ProperGate] using ne
  have rot := (rotate_physical (BalancedCircuit.rawTarget L) (BalancedCircuit.rawTargetND L hn)).1
  simp only [gatePhysical_append] at small
  simp only [program,biasedPrefix,cleanupSuffix,gatePhysical_append]
  exact ⟨⟨seed,⟨raw,⟨small.1.1.1,⟨rot,⟨small.1.1.2,⟨mapped,⟨small.1.2,⟨ps,small.2⟩⟩⟩⟩⟩⟩⟩⟩,
    ⟨pc,⟨cmp,⟨pcr,⟨un,⟨psr,last⟩⟩⟩⟩⟩⟩

end ECDSAAdd.Entrant.BiasedCircuit

#print axioms ECDSAAdd.Entrant.BiasedCircuit.physical

end

section
-- ===== BiasedCircuit =====
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.BiasedCircuit
open Arithmetic Arithmetic.BalancedField

theorem prefix_eq_reference (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (biasedPrefix L) m s=run (referencePrefix L) n s := by
  have a := prefixPost L hw hn B X Y hx hy s m hs hr hyr hc
  have b := referencePost L hw hn B X Y hx hy s n hs hr hyr hc
  apply State.extensionality
  · exact a.phase.trans b.phase.symm
  · funext q
    by_cases qr : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (a.value.trans b.value.symm) q qr
    by_cases ql : q=L.lower
    · subst q; exact a.lower.trans b.lower.symm
    by_cases qp : q=L.parity
    · subst q; exact a.parity.trans b.parity.symm
    by_cases qg : q=L.sourceGuard
    · subst q; exact a.guard.trans b.guard.symm
    exact (a.frame q qr ql qp qg).trans (b.frame q qr ql qp qg).symm

theorem reference_program (L : Layout) :
    BalancedCircuit.program L=referencePrefix L++cleanupSuffix L := by
  simp only [BalancedCircuit.program_eq_core,referencePrefix,cleanupSuffix,
    BalancedCleanup.program,List.append_assoc]

/-- Exact single-bank forward kernel for every input phase and measurement record. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈BalancedCircuit.work L,t.basis q=false) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let k := measurementCount (referencePrefix L)
  let tail := m.drop (measurementCount (biasedPrefix L))
  let n := List.replicate k false++tail
  have eq : run (program L) m s=run (BalancedCircuit.program L) n s := by
    rw [program,reference_program,run_append,run_take,run_append,run_take,
      prefix_eq_reference L hw hn B X Y hx hy s m n hs hr hyr hc]
    have dn : n.drop (measurementCount (referencePrefix L))=tail := by simp [n,k]
    rw [dn]
  rw [eq]
  exact BalancedCircuit.program_correct L hw hn B X Y hx hy s n hs hr hyr hc


/-- Interchangeability with the public balanced kernel, for independent records. -/
theorem run_eq_balanced (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (program L) m s=run (BalancedCircuit.program L) n s := by
  have a := program_correct L hw hn B X Y hx hy s m hs hr hyr hc
  have b := BalancedCircuit.program_correct L hw hn B X Y hx hy s n hs hr hyr hc
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2.2 q hq).trans (b.2.2.2 q hq).symm

end ECDSAAdd.Entrant.BiasedCircuit

#print axioms ECDSAAdd.Entrant.BiasedCircuit.program_correct

#print axioms ECDSAAdd.Entrant.BiasedCircuit.run_eq_balanced

end


section
-- ===== BiasedInverseProgram =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField

abbrev Layout := BalancedCircuit.Layout

def halfBias : Nat := 2^30 + 244

def biasBits (L : Layout) : List MappedBit :=
  (List.range 255).map (fun i =>
    {wire := some L.lower, flip := halfBias.testBit i}) ++
    [{wire := some L.one, flip := false}]

def recoverPrefix (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toLayout ++ BalancedCleanup.normalize L.toLayout ++
  BalancedCleanup.prepareCompare L.toLayout ++
  compareLt none L.y L.r L.carry L.one L.parity ++
  (BalancedCleanup.prepareCompare L.toLayout).reverse

def unbiasView (L : Layout) : Program :=
  [.X (L.r.getD 254 0)] ++ (BalancedCleanup.prepareSign L.toLayout).reverse

def selectors (L : Layout) : Program :=
  [.CX L.parity L.lower, .CX L.rmsb L.lower, .CX L.rmsb L.one,
    .CCX L.parity L.lower L.minus]

def unfoldBias (L : Layout) : Program :=
  mappedSub (biasBits L) L.r (L.carry.take 255) L.minus

def release (L : Layout) : Program :=
  [.CX L.rmsb L.lower, .CX L.parity L.one, .CX L.rmsb L.one,
    .measureX L.minus [] [.CZ L.parity L.rmsb]]

def restoreRaw (L : Layout) : Program :=
  selectors L ++ unfoldBias L ++ release L ++
  rotateLeft (rawTarget L) ++ [.CX L.parity L.r0]

def program (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard] ++ recoverPrefix L ++ unbiasView L ++
  restoreRaw L ++ BalancedInverse.rawSubtract L ++ (seedViews L).reverse

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L) = 1022 ∧ measurementCount (program L) = 1022 := by
  have w := BalancedCircuit.widths L hw
  have cw := BalancedCleanup.widths L.toLayout hw
  have ra := subInPlace_counts (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have fa := mappedSub_counts (biasBits L) L.r (L.carry.take 255) L.minus
    (by simp [biasBits, cw.2.1]) (by simp [List.length_take, hw.2.2, cw.2.1])
  have na := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.negativeLiteral (by omega)
  have co := compareLt_counts none L.y L.r L.carry L.one L.parity
    (by omega) (by omega)
  have cm := signComplement_counts L.sign (rawSource L)
  have cr := signComplement_counts L.lower L.r
  have cy := signComplement_counts L.sign L.y
  have cl := signComplement_counts L.lower L.y
  have rr := rotate_counts L.r
  have rt := rotate_counts (rawTarget L)
  simp only [program, restoreRaw, recoverPrefix, unbiasView, selectors, unfoldBias, release,
    BalancedInverse.rawSubtract, BalancedCleanup.prepareSign, BalancedCleanup.normalize,
    BalancedCleanup.prepareCompare, seedViews, toffoliCount_append, measurementCount_append,
    toffoliCount_reverse, measurementCount_reverse, ra.1, ra.2, fa.1, fa.2, na.1, na.2,
    co.1, co.2, cm.1, cm.2, cr.1, cr.2, cy.1, cy.2, cl.1, cl.2,
    rr.2.2.1, rr.2.2.2, rt.2.2.1, rt.2.2.2, w.2.1, cw.1, cw.2.1]
  norm_num [toffoliCount, measurementCount]

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseMath =====
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField

def biased (R : Int) : Int := if R < 0 then R - halfBias - 1 else R + halfBias

def biasSource (n z : Bool) : Nat :=
  (if n then 2^255 - 1 - halfBias else halfBias) + 2^255 * z.toNat

private theorem mapped_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i => ({wire := some L.lower, flip := halfBias.testBit i} : MappedBit))) s =
    is.foldr (fun i acc => (s L.lower ^^ halfBias.testBit i).toNat + 2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [mappedValue, MappedBit.value, ih, Bool.xor_comm]

private theorem biasSource_calc (n : Bool) :
    (List.range 255).foldr (fun i acc => (n ^^ halfBias.testBit i).toNat + 2*acc) 0 =
    if n then 2^255 - 1 - halfBias else halfBias := by
  cases n <;> decide

theorem biasBits_value (L : Layout) (s : BasisState) :
    mappedValue (biasBits L) s = biasSource (s L.lower) (s L.one) := by
  rw [biasBits, mappedValue_append, mapped_list, biasSource_calc]
  simp [biasSource, mappedValue, MappedBit.value]

theorem biasBits_sources (L : Layout) (a : Wire) (ha : a ∈ mappedWires (biasBits L)) :
    a = L.lower ∨ a = L.one := by
  simp only [biasBits, mappedWires, List.flatMap_append, List.flatMap_map,
    List.mem_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨i, hi, ha⟩ | ha
  · exact Or.inl (by simpa using ha)
  · exact Or.inr (by simpa using ha)

theorem biased_bounds (R : Int) (hr : Centered R) :
    -((2^255 : Nat) : Int) ≤ biased R ∧ biased R < ((2^255 : Nat) : Int) := by
  unfold Centered q at hr
  norm_num [ECDSAAdd.p] at hr
  unfold biased halfBias
  split_ifs <;> norm_num at ⊢ <;> omega

theorem biased_sign (R : Int) : (biased R < 0) ↔ R < 0 := by
  unfold biased halfBias
  split_ifs <;> norm_num at ⊢ <;> omega

theorem biased_magnitude (R : Int) :
    (if R < 0 then -biased R-1 else biased R) = |R| + halfBias := by
  by_cases hn : R < 0
  · simp [biased, hn, abs_of_neg hn]; ring
  · simp [biased, hn, abs_of_nonneg (by omega : 0 ≤ R)]

theorem normalized_bias (R : Int) :
    normalizedR R + ((2^254 : Nat) : Int) = |R| + halfBias := by
  by_cases hn : R < 0
  · simp [normalizedR, magnitude, signBit, negative, hn, abs_of_neg hn]
    norm_num [halfBias, h, q, ECDSAAdd.p]
    omega
  · simp [normalizedR, magnitude, signBit, negative, hn,
      abs_of_nonneg (by omega : 0 ≤ R)]
    norm_num [halfBias, h, q, ECDSAAdd.p]
    omega

theorem unfold_arithmetic (T : Int) (ht : -(2*q) ≤ T ∧ T ≤ 2*q) :
    (encodeWord 256 (biased (halfResult T)) + 2^256 -
      biasSource (decide (T<0)) (negative (halfResult T)) -
      (originalParity T && decide (T<0)).toNat) % 2^256 = encodeWord 256 (T/2) := by
  have hb := biased_bounds (halfResult T) (halfResult_spec T ht).1
  have z := BalancedFold.encode_shift 256 (biased (halfResult T)) (by norm_num at hb ⊢; omega)
  have wt : -((2^255 : Nat) : Int) ≤ T/2 ∧ T/2 < ((2^255 : Nat) : Int) := by
    norm_num [q, ECDSAAdd.p] at ht ⊢; omega
  have w := BalancedFold.encode_shift 256 (T/2) (by norm_num at wt ⊢; omega)
  have hr := (halfResult_spec T ht).2
  by_cases hp : T%2=0 <;> by_cases hn : T<0
  all_goals
    have pp : originalParity T = decide (¬ T%2=0) := rfl
    have sn := halfResult_sign T ht
    simp only [pp, hp, hn, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false, Bool.false_xor, Bool.true_xor,
      Bool.not_false, Bool.not_true] at sn
    simp only [evenLift, hp, if_true, if_false] at hr
    try split_ifs at hr
    all_goals
      norm_num [q, ECDSAAdd.p] at ht hr
      by_cases nr : halfResult T < 0
      all_goals
        simp only [nr, decide_true, decide_false, Bool.false_eq_true,
          Bool.true_eq_false] at sn
        all_goals simp only [biased, nr, if_true, if_false] at z ⊢
        all_goals simp only [biasSource, negative, nr, originalParity, ne_eq, hp, hn,
          not_true_eq_false, not_false_eq_true, decide_true, decide_false,
          if_true, if_false, Bool.and_self, Bool.and_false, Bool.false_and,
          Bool.toNat_true, Bool.toNat_false] at ⊢
        all_goals norm_num [halfBias] at z w ⊢
        all_goals split_ifs at z w <;> omega

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInversePrefix =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedField
open Arithmetic.BalancedCleanup

theorem prefix_states (L : BalancedCleanup.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State)
    (m1 m2 m3 m4 m5 : List Bool) (s1 s2 s3 s4 s5 : State)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hs1 : run (prepareSign L) m1 s=s1) (hs2 : run (normalize L) m2 s1=s2)
    (hs3 : run (prepareCompare L) m3 s2=s3)
    (hs4 : run (compareLt none L.y L.r L.carry L.one L.parity) m4 s3=s4)
    (hs5 : run (prepareCompare L).reverse m5 s4=s5) :
    s5.phase=s.phase ∧ regValue L.r s5.basis=encodeWord 255 (normalizedR R) ∧
    s5.basis L.lower=negative R ∧
    s5.basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) ∧
    ∀a,a∉L.r → a≠L.lower → a≠L.parity → s5.basis a=s.basis a := by
  have w := widths L hw
  have nd := L.normND hn
  have flags := L.flagsND hn
  have pa := clifford_parity_away L hw hn
  have ar : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have ay : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have al : L.parity≠L.lower := by have hh := (List.nodup_cons.mp flags).1; simp at hh; tauto
  have oa : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have ol : L.one≠L.lower := by have hh := List.nodup_iff_count.mp flags L.one; simp [List.count_cons] at hh; intro e; simp [e] at hh; omega
  have sy : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by have hh := List.nodup_iff_count.mp flags L.sign; simp [List.count_cons] at hh; intro e; simp [←e] at hh; omega
  have ca (q : Wire) (hq : q∈L.carry) : q∉L.r ∧ q≠L.lower := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact ⟨fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]),
      fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])⟩
  have v1 := prepareSign_value L hw hn R hr s m1 hR hz
  rw [hs1] at v1
  have one1 : s1.basis L.one=false := (v1.2.2 _ oa ol).trans ho
  have clean1 : ∀q∈L.carry,s1.basis q=false := fun q hq => (v1.2.2 q (ca q hq).1 (ca q hq).2).trans (hc q hq)
  have Y1 : regValue L.y s1.basis=encodeWord 256 Y := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact (regValue_congr _ _ _ (fun q hq => v1.2.2 q
      (fun r => List.disjoint_left.mp d.2.2 r (by simp [hq]))
      (fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])))).trans hY
  have rm0 : s1.basis L.rmsb=false := by
    have hi := regValue_highBit L.low L.rmsb s1.basis
    rw [w.1] at hi
    change s1.basis L.rmsb=true ↔ 2^255≤regValue L.r s1.basis at hi
    rw [v1.1] at hi
    have b := magnitude_bounds R hr; have p := constants
    have cast := Int.toNat_of_nonneg b.1
    cases e : s1.basis L.rmsb
    · rfl
    · simp [e] at hi
      omega
  have low1 : regValue L.low s1.basis=(magnitude R).toNat := by
    have h := v1.1; rw [Layout.r,regValue_append] at h; simpa [regValue,rm0] using h
  have v2 := normalize_value L hw hn R hr s1 m2 low1 v1.2.1 one1 clean1
  rw [hs2] at v2
  have rmAway : L.rmsb∉L.low := by have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).1; exact fun h => List.disjoint_left.mp d.2.2 h (by simp)
  have R2 : regValue L.r s2.basis=encodeWord 255 (normalizedR R) := by
    rw [Layout.r,regValue_append,v2.2.1]; simp [regValue,v2.2.2 _ rmAway,rm0]
  have Y2 : regValue L.y s2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => v2.2.2 q (by
      intro hl; exact List.disjoint_left.mp (List.nodup_append'.mp (L.dataND hn)).2.2
        (show q∈L.r from by simp [Layout.r,hl])
        (show q∈L.y++L.carry from by simp [hq])))).trans Y1
  have S2 : s2.basis L.sign=B := (v2.2.2 _ (fun h => sy (by simp [Layout.r,h]))).trans ((v1.2.2 _ sy sl).trans hS)
  have L2 : s2.basis L.lower=negative R := (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h]))).trans v1.2.1
  have v3 := prepareCompare_value L hw hn R Y B hr hy s2 m3 R2 Y2 S2 L2
  rw [hs3] at v3
  have frame2 (q : Wire) (hq : q∉L.r) : s2.basis q=s1.basis q := v2.2.2 q (fun h => hq (by simp [Layout.r,h]))
  have one3 : s3.basis L.one=false := (v3.2.2 _ oa (fun h => L.flagAway hn L.one (by simp) (by simp [h]))).trans ((frame2 _ oa).trans one1)
  have clean3 : ∀q∈L.carry,s3.basis q=false := by
    intro q hq; have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).2.1
    exact (v3.2.2 q (ca q hq).1 (fun hyq => List.disjoint_left.mp d.2.2 hyq hq)).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have cmp := compareLt_correct none L.y L.r L.carry L.one L.parity (L.compareND hn)
    (by simp) (by omega) (by unfold Layout.Widths at hw; omega) s3 m4 one3 clean3
  rw [hs4] at cmp
  have pred : decide (regValue L.y s3.basis<regValue L.r s3.basis)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    have interval := cleanup_interval_identity B R Y hr hy
    omega
  have A3 : s3.basis L.parity=s.basis L.parity := (v3.2.2 _ ar ay).trans ((frame2 _ ar).trans (v1.2.2 _ ar al))
  have A4 : s4.basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) := by
    rw [cmp.2.2,A3,pred]
    simp [controlValue]
  have ex5 := inverse_except (prepareCompare L) (prepareCompare_proper L hn) L.parity pa.2 s2 s4 m3 m5 (by rw [hs3]; exact ⟨cmp.1,cmp.2.1⟩)
  rw [hs5] at ex5
  have keep5 := run_preserves_outside (prepareCompare L).reverse m5 s4 L.parity
    (by rw [wires_reverse]; exact pa.2)
  rw [hs5] at keep5
  refine ⟨ex5.1.trans (v2.1.trans ?_), ?_, ?_, keep5.trans A4, ?_⟩
  · rw [←hs1]
    exact FiniteUnitary.run_phase _ (prepareSign_proper L hn) s m1
  · exact (regValue_congr _ _ _ (fun a ha => ex5.2 a
      (fun e => ar (e ▸ ha)))).trans R2
  · exact (ex5.2 _ (Ne.symm al)).trans L2
  · intro a har hal hap
    exact (ex5.2 a hap).trans ((frame2 a har).trans (v1.2.2 a har hal))

theorem recoverPrefix_correct (L : Layout) (hw : L.Widths) (hn : L.toLayout.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    let t := run (recoverPrefix L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 255 (normalizedR R) ∧
    t.basis L.lower=negative R ∧
    t.basis L.parity=(s.basis L.parity ^^ decide (q < |2*R-signedY B Y|)) ∧
    ∀a,a∉L.r → a≠L.lower → a≠L.parity → t.basis a=s.basis a := by
  unfold recoverPrefix
  simp only [List.append_assoc, run_append, run_take]
  exact prefix_states L.toLayout hw hn R Y B hr hy s
    _ _ _ _ _ _ _ _ _ _ hR hY hS hz ho hc rfl rfl rfl rfl rfl

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseViews =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedField

private theorem complement_run (q : Wire) (xs : List Wire) (hq : q∉xs)
    (hn : xs.Nodup) (s : State) (m : List Bool) :
    run (signComplement q xs) m s =
      ⟨s.phase, fun a => if a∈xs then s.basis a ^^ s.basis q else s.basis a⟩ := by
  induction xs generalizing s with
  | nil => simp [signComplement,run]
  | cons a xs ih =>
    have hqa : q≠a := fun e => hq (by simp [e])
    have hqt : q∉xs := fun h => hq (by simp [h])
    have nd := List.nodup_cons.mp hn
    simp only [signComplement,List.map_cons,run]
    change run (signComplement q xs) m
      ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩ = _
    rw [ih hqt nd.2]
    apply congrArg (State.mk s.phase)
    funext b
    by_cases ba : b=a <;> by_cases bx : b∈xs <;>
      simp_all [writeBit]
    all_goals subst b; simp [Function.update_self]

theorem complement_reverse (q : Wire) (xs : List Wire) (hn : xs.Nodup)
    (hq : q∉xs) (s : State) (m : List Bool) :
    run (signComplement q xs).reverse m s = run (signComplement q xs) m s := by
  have shape : (signComplement q xs).reverse=signComplement q xs.reverse := by
    simp [signComplement]
  rw [shape,complement_run _ _ (by simpa using hq) (List.nodup_reverse.mpr hn),
    complement_run _ _ hq hn]
  simp

theorem low_split (L : Layout) (hw : L.Widths) :
    L.low = L.r.take 254 ++ [L.r.getD 254 0] := by
  have w := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by omega
  have split : L.r.take 254 ++ [L.r.getD 254 0] = L.r.take 255 := by
    conv_rhs => rw [show 255=254+1 from rfl, List.take_add_one]
    rw [List.getD_eq_getElem _ _ idx,List.getElem?_eq_getElem idx]
    rfl
  rw [split, BalancedCleanup.Layout.r, ←w.1]
  simp

theorem biased_from_magnitude (R : Int) (hr : Centered R) :
    (if negative R then 2^256-1-(|R|+(halfBias : Int)).toNat
      else (|R|+(halfBias : Int)).toNat) = encodeWord 256 (biased R) := by
  have hb := biased_bounds R hr
  have enc := BalancedFold.encode_shift 256 (biased R) (by norm_num at hb ⊢; omega)
  have mag := Int.toNat_of_nonneg (show 0≤|R|+(halfBias : Int) by
    have := abs_nonneg R; norm_num [halfBias]; omega)
  by_cases hn : R<0
  · rw [if_pos ((biased_sign R).mpr hn)] at enc
    simp [negative,hn,biased,abs_of_neg hn] at enc mag ⊢
    norm_num [halfBias] at enc mag ⊢
    omega
  · rw [if_neg (fun h => hn ((biased_sign R).mp h))] at enc
    simp [negative,hn,biased,abs_of_nonneg (by omega : 0≤R)] at enc mag ⊢
    omega

theorem biased_msb (L : Layout) (hw : L.Widths) (R : Int) (hr : Centered R)
    (s : BasisState) (hR : regValue L.r s=encodeWord 256 (biased R)) :
    s L.rmsb=negative R := by
  have w := BalancedCleanup.widths L.toLayout hw
  have decoded : signedRegValue L.r s=biased R := by
    unfold signedRegValue
    rw [w.2.1,hR]
    exact decode_encodeWord 256 (by norm_num) _ (by
      simpa using biased_bounds R hr)
  have sign := signedRegValue_neg_iff L.low L.rmsb s
  change (signedRegValue L.r s<0 ↔ s L.rmsb=true) at sign
  rw [decoded,biased_sign] at sign
  cases e : s L.rmsb <;> simp_all [negative]

theorem unbiasView_correct (L : Layout) (hw : L.Widths) (hn : L.toLayout.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 255 (normalizedR R))
    (hl : s.basis L.lower=negative R) :
    let t := run (unbiasView L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (biased R) ∧
    t.basis L.lower=false ∧
    ∀a,a∉L.r → a≠L.lower → t.basis a=s.basis a := by
  have w := BalancedCleanup.widths L.toLayout hw
  have nd := (List.nodup_append'.mp (L.toLayout.dataND hn)).1
  have lowND := (List.nodup_append'.mp nd).1
  have la : L.lower∉L.r := fun h => L.toLayout.flagAway hn L.lower (by simp) (by simp [h])
  have rmAway : L.rmsb∉L.low := fun h =>
    List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  let bit := L.r.getD 254 0
  have shape : L.low=L.r.take 254++[bit] := low_split L hw
  have bitLow : bit∈L.low := by rw [shape]; simp
  have bitR : bit∈L.r := by simp [BalancedCleanup.Layout.r,bitLow]
  have bitNe : L.rmsb≠bit := fun e => rmAway (e.symm ▸ bitLow)
  have lowlen : (L.r.take 254).length=254 := by simp [w.2.1]
  have top := regValue_highBit L.low L.rmsb s.basis
  rw [w.1] at top
  change s.basis L.rmsb=true ↔ 2^255≤regValue L.r s.basis at top
  have bound := encodeWord_bound 255 (normalizedR R)
  have rms : s.basis L.rmsb=false := by
    rw [hR] at top
    cases e : s.basis L.rmsb <;> simp_all
    omega
  have lowR : regValue L.low s.basis=encodeWord 255 (normalizedR R) := by
    rw [BalancedCleanup.Layout.r,regValue_append] at hR
    simpa [regValue,rms] using hR
  let u := run [.X bit] m s
  have uf (a : Wire) (ha : a≠bit) : u.basis a=s.basis a := by simp [u,run,writeBit,ha]
  have vb := BalancedCleanup.bias_value (L.r.take 254) bit
    (by rw [←shape]; exact lowND) s m
  rw [←shape,lowlen,lowR,normalizedR_lowword_decode R hr,normalized_bias] at vb
  have uR : regValue L.r u.basis=(|R|+(halfBias : Int)).toNat := by
    have lowU : regValue L.low u.basis=(|R|+(halfBias : Int)).toNat := by
      simpa only [Int.toNat_natCast] using congrArg Int.toNat vb
    rw [BalancedCleanup.Layout.r,regValue_append,lowU]
    simp [regValue,uf _ bitNe,rms]
  have uL : u.basis L.lower=negative R :=
    (uf L.lower (fun e => la (by rw [e]; exact bitR))).trans hl
  let v := run (signComplement L.lower L.r) m u
  have cv := signComplement_correct L.lower L.r nd la u m
  have vR : regValue L.r v.basis=encodeWord 256 (biased R) := by
    rw [cv.2.2,uR,uL,w.2.1,biased_from_magnitude R hr]
  have vL : v.basis L.lower=negative R := (cv.2.1 _ la).trans uL
  have vm : v.basis L.rmsb=negative R := biased_msb L hw R hr v.basis vR
  have actual : run (unbiasView L) m s=run [.CX L.rmsb L.lower] m v := by
    simp only [unbiasView,BalancedCleanup.prepareSign,List.reverse_append,
      List.reverse_singleton,List.append_assoc,run_append,run_take,measurementCount,
      List.drop_zero,measurementCount_reverse,(signComplement_counts L.lower L.r).2]
    rw [complement_reverse _ _ nd la]
    have cm (t : State) : run (signComplement L.lower L.r) (m.take 0) t =
        run (signComplement L.lower L.r) m t := by
      simpa only [(signComplement_counts L.lower L.r).2] using
        run_take (signComplement L.lower L.r) m t
    rw [cm]
    rfl
  rw [actual]
  refine ⟨cv.1,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun a ha => by
      simp [run,writeBit,show a≠L.lower from fun e => la (e ▸ ha)])).trans vR
  · simp [run,writeBit,vL,vm]
  · intro a har hal
    simp only [run,writeBit,Function.update_of_ne hal]
    exact (cv.2.1 a har).trans (uf a (fun e => har (e.symm ▸ bitR)))

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseFlags =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField

theorem selectors_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (hh : s.basis L.rmsb=(N ^^ P)) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (ho : s.basis L.one=false) :
    run (selectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower N) L.one (N ^^ P)) L.minus (P && N)⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.one,L.minus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro a; have h := List.nodup_iff_count.mp (scalarND L hn) a
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4⟩,⟨h1_2,h1_3,h1_4⟩,⟨h2_3,h2_4⟩,h3_4⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h3_4r := Ne.symm h3_4
  cases P <;> cases N
  all_goals
    simp only [selectors,run]
    apply congrArg (State.mk s.phase)
    funext a
    by_cases hm : a=L.minus <;> by_cases ho : a=L.one <;> by_cases hl : a=L.lower <;>
      simp_all [writeBit,Function.update]

theorem release_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (hh : s.basis L.rmsb=N) (hl : s.basis L.lower=N)
    (hm : s.basis L.minus=(P && N)) (ho : s.basis L.one=(N ^^ P)) :
    run (release L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower false) L.one false) L.minus false⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.one,L.minus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro a; have h := List.nodup_iff_count.mp (scalarND L hn) a
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4⟩,⟨h1_2,h1_3,h1_4⟩,⟨h2_3,h2_4⟩,h3_4⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h3_4r := Ne.symm h3_4
  cases P <;> cases N <;> cases hx : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [release,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext a
      by_cases hm : a=L.minus <;> by_cases ho : a=L.one <;> by_cases hl : a=L.lower <;>
        simp_all [release,run,measureAndCorrect,correct,writeBit,Function.update]

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseUnfold =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField

theorem unfoldBias_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hl : s.basis L.lower=decide (T<0)) (ho : s.basis L.one=negative (halfResult T))
    (hm : s.basis L.minus=(originalParity T && decide (T<0)))
    (hR : regValue L.r s.basis=encodeWord 256 (biased (halfResult T)))
    (hc : ∀a∈L.carry,s.basis a=false) :
    let t := run (unfoldBias L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (T/2) ∧
    ∀a,a∉L.r → t.basis a=s.basis a := by
  have nd : (L.lower::L.one::L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp (allND L hn) a
    have t := (List.take_sublist 255 L.carry).count_le a
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have source : ∀a∈mappedWires (biasBits L),a∉L.minus::(L.r++L.carry.take 255) := by
    intro a ha
    rcases biasBits_sources L a ha with rfl|rfl
    · exact fun h => n1.1 (by simp [h])
    · exact n2.1
  have w := BalancedCleanup.widths L.toLayout hw
  have sub := BalancedInverse.mappedSub_any_correct (biasBits L) L.r (L.carry.take 255) L.minus
    n2.2 source (by simp [biasBits,w.2.1])
    (by simp [List.length_take,hw.2.2,w.2.1]) s m
    (fun a ha => hc a (List.mem_of_mem_take ha))
  refine ⟨sub.1,?_,sub.2.1⟩
  rw [unfoldBias,sub.2.2,hR,biasBits_value,hl,ho,hm,w.2.1]
  exact unfold_arithmetic T ht

theorem half_msb (L : Layout) (hw : L.Widths) (T : Int)
    (ht : -(2*q)≤T ∧ T≤2*q) (s : BasisState)
    (hR : regValue L.r s=encodeWord 256 (T/2)) : s L.rmsb=decide (T<0) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have decoded : signedRegValue L.r s=T/2 := by
    unfold signedRegValue
    rw [w.2.1,hR]
    apply decode_encodeWord 256 (by norm_num)
    norm_num [q,ECDSAAdd.p] at ht ⊢
    omega
  have sign := word_sign L.low L.rmsb s (T/2) decoded
  have eq : (T/2<0) ↔ T<0 := by omega
  simpa only [eq] using sign

theorem half_encoding (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) :
    2*encodeWord 256 (T/2)+(originalParity T).toNat=encodeWord 257 T := by
  norm_num [q,ECDSAAdd.p] at ht
  have e := BalancedFold.encode_shift 257 T (by norm_num; omega)
  have f := BalancedFold.encode_shift 256 (T/2) (by norm_num; omega)
  have pa := originalParity_value T
  cases hp : originalParity T <;> simp [hp] at pa ⊢ <;> norm_num at e f ⊢ <;>
    split_ifs at e f <;> omega

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseRestore =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField

theorem restoreRaw_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hR : regValue L.r s.basis=encodeWord 256 (biased (halfResult T)))
    (hl : s.basis L.lower=false) (ho : s.basis L.one=false) (hm : s.basis L.minus=false)
    (hc : ∀a∈L.carry,s.basis a=false) :
    let t := run (restoreRaw L) m s
    t.phase=s.phase ∧ regValue (rawTarget L) t.basis=encodeWord 257 T ∧
    t.basis L.lower=false ∧ t.basis L.minus=false ∧
    ∀a,a∉rawTarget L → a≠L.lower → a≠L.minus → t.basis a=s.basis a := by
  let P := originalParity T
  let N := decide (T<0)
  let u : State := ⟨s.phase,writeBit (writeBit (writeBit s.basis L.lower N)
    L.one (N ^^ P)) L.minus (P && N)⟩
  let v := run (unfoldBias L) m u
  let m1 := m.drop (measurementCount (unfoldBias L))
  let z := run (release L) m1 v
  let m2 := m1.drop 1
  let rot := run (rotateLeft (rawTarget L)) m2 z
  let out := run [.CX L.parity L.r0] m2 rot
  have sd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at sd
  have lm : L.lower≠L.minus := by tauto
  have om : L.one≠L.minus := by tauto
  have ol : L.one≠L.lower := by tauto
  have pl : L.parity≠L.lower := by tauto
  have po : L.parity≠L.one := by tauto
  have pm : L.parity≠L.minus := by tauto
  have r0p : L.r0≠L.parity := by tauto
  have r0o : L.r0≠L.one := by tauto
  have flags (a : Wire) (ha : a∈L.r++L.y++L.carry)
      (f : Wire) (hf : f∈[L.lower,L.one,L.minus]) : a≠f := by
    intro e
    exact flagAway L hn f (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto)
      (e ▸ ha)
  have uf (a : Wire) (al : a≠L.lower) (ao : a≠L.one) (am : a≠L.minus) : u.basis a=s.basis a := by
    simp [u,writeBit,al,ao,am]
  have uL : u.basis L.lower=N := by simp [u,writeBit,lm,Ne.symm ol]
  have uO : u.basis L.one=(N ^^ P) := by simp [u,writeBit,om]
  have uM : u.basis L.minus=(P && N) := by simp [u,writeBit]
  have uP : u.basis L.parity=P := (uf _ pl po pm).trans hp
  have sign := biased_msb L hw _ (halfResult_spec T ht).1 s.basis hR
  rw [negative,halfResult_sign T ht] at sign
  have sel : run (selectors L) m s=u := selectors_run L hn P N s m hp sign hl hm ho
  have uR : regValue L.r u.basis=encodeWord 256 (biased (halfResult T)) := by
    apply Eq.trans _ hR
    apply regValue_congr
    intro a ha
    exact uf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))
  have uC : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (uf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))).trans (hc a ha)
  have sub := unfoldBias_correct L hw hn T ht u m uL
    (by rw [negative,halfResult_sign T ht]; exact uO) uM uR uC
  have vR : regValue L.r v.basis=encodeWord 256 (T/2) := sub.2.1
  have fa (f : Wire) (hf : f∈[L.lower,L.one,L.minus,L.parity]) : f∉L.r := by
    intro h
    exact flagAway L hn f (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto)
      (by simp [h])
  have rel : z=⟨v.phase,writeBit (writeBit (writeBit v.basis L.lower false)
      L.one false) L.minus false⟩ :=
    release_run L hn P N v m1 ((sub.2.2 _ (fa _ (by simp))).trans uP)
      (half_msb L hw T ht v.basis vR)
      ((sub.2.2 _ (fa _ (by simp))).trans uL)
      ((sub.2.2 _ (fa _ (by simp))).trans uM)
      ((sub.2.2 _ (fa _ (by simp))).trans uO)
  have zf (a : Wire) (al : a≠L.lower) (ao : a≠L.one) (am : a≠L.minus) : z.basis a=v.basis a := by
    rw [rel]; simp [writeBit,al,ao,am]
  have zL : z.basis L.lower=false := by rw [rel]; simp [writeBit,lm,Ne.symm ol]
  have zM : z.basis L.minus=false := by rw [rel]; simp [writeBit]
  have zO : z.basis L.one=false := by rw [rel]; simp [writeBit,om]
  have zR : regValue L.r z.basis=encodeWord 256 (T/2) := by
    apply Eq.trans _ vR
    apply regValue_congr
    intro a ha
    exact zf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))
  have zP : z.basis L.parity=P := (zf _ pl po pm).trans ((sub.2.2 _ (fa _ (by simp))).trans uP)
  have rp := BalancedInverse.rotate_unfold L hw hn (T/2) z m2 zO zR
  have away (a : Wire) (ha : a∉L.r) (ao : a≠L.one) : a∉rawTarget L := by
    simp [rawTarget,ha,ao]
  have pr : rot.basis L.parity=P := (rp.2.2.2 _ (away _ (fa _ (by simp)) po)).trans zP
  have outV : regValue (rawTarget L) out.basis=encodeWord 257 T := by
    have shape : rawTarget L=L.r0::foldTarget L := by
      simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
    have r0Away : L.r0∉foldTarget L := by
      have nd := rawTargetND L hn
      rw [shape] at nd
      exact (List.nodup_cons.mp nd).1
    have tail : regValue (foldTarget L) out.basis=encodeWord 256 (T/2) := by
      apply Eq.trans _ rp.2.2.1
      apply regValue_congr
      intro a ha
      change out.basis a=rot.basis a
      simp [out,run,writeBit,show a≠L.r0 from fun e => r0Away (e ▸ ha)]
    rw [shape]
    change (if out.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) out.basis=_
    have r0rot : rot.basis L.r0=false := rp.2.1
    have low : out.basis L.r0=P := by simp [out,run,writeBit,r0rot,pr]
    rw [low,tail]
    have he := half_encoding T ht
    cases hp' : P <;> simpa [P,hp',Nat.add_comm] using he
  have actual : run (restoreRaw L) m s=out := by
    simp only [restoreRaw,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount (selectors L)=0 from rfl,List.drop_zero]
    rw [sel,run_append,run_take]
    change run (release L ++ (rotateLeft (rawTarget L) ++ [.CX L.parity L.r0])) m1 v=out
    rw [run_append,run_take]
    simp only [show measurementCount (release L)=1 from rfl]
    change run (rotateLeft (rawTarget L) ++ [.CX L.parity L.r0]) m2 z=out
    rw [run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero]
  rw [actual]
  have of (a : Wire) (ar : a∉rawTarget L) : out.basis a=z.basis a := by
    have ar0 : a≠L.r0 := fun e => ar (by simp [rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,e])
    simp only [out,run,writeBit,Function.update_of_ne ar0]
    exact rp.2.2.2 a ar
  refine ⟨?_,outV,?_,?_,?_⟩
  · change rot.phase=s.phase
    exact rp.1.trans ((congrArg State.phase rel).trans sub.1)
  · exact (of _ (away _ (fa _ (by simp)) (Ne.symm ol))).trans zL
  · exact (of _ (away _ (fa _ (by simp)) (Ne.symm om))).trans zM
  · intro a ar al am
    have ar' : a∉L.r := fun h => ar (by simp [rawTarget,h])
    have ao : a≠L.one := fun e => ar (by simp [rawTarget,e])
    exact (of a ar).trans ((zf a al ao am).trans ((sub.2.2 a ar').trans (uf a al ao am)))

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverse =====
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit Arithmetic.BalancedField
attribute [local irreducible] run measurementCount

/-- Exact multiply-direction inverse with one shared carry bank. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀a∈work L,s.basis a=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (BalancedInverse.result B R Y) ∧
    (∀a∈work L,t.basis a=false) ∧ (∀a,a∉L.r → t.basis a=s.basis a) := by
  let X := BalancedInverse.result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let u0 := run [.CX L.ymsb L.sourceGuard] m s
  let u1 := run (recoverPrefix L) m u0
  let m1 := m.drop (measurementCount (recoverPrefix L))
  let u2 := run (unbiasView L) m1 u1
  let m2 := m1.drop (measurementCount (unbiasView L))
  let u3 := run (restoreRaw L) m2 u2
  let m3 := m2.drop (measurementCount (restoreRaw L))
  let u4 := run (BalancedInverse.rawSubtract L) m3 u3
  let m4 := m3.drop (measurementCount (BalancedInverse.rawSubtract L))
  let out := run (seedViews L).reverse m4 u4
  have hx : Centered X := BalancedInverse.result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := BalancedInverse.result_half B R Y hr hy
  have par : decide (q < |2*R-signedY B Y|)=P := BalancedInverse.result_parity B R Y hr hy
  have w := BalancedCleanup.widths L.toLayout hw
  have rwid := BalancedCircuit.widths L hw
  have cnd : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h0_7r := Ne.symm h0_7
  have h0_8r := Ne.symm h0_8
  have h0_9r := Ne.symm h0_9
  have h0_10r := Ne.symm h0_10
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h1_7r := Ne.symm h1_7
  have h1_8r := Ne.symm h1_8
  have h1_9r := Ne.symm h1_9
  have h1_10r := Ne.symm h1_10
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h2_7r := Ne.symm h2_7
  have h2_8r := Ne.symm h2_8
  have h2_9r := Ne.symm h2_9
  have h2_10r := Ne.symm h2_10
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h3_7r := Ne.symm h3_7
  have h3_8r := Ne.symm h3_8
  have h3_9r := Ne.symm h3_9
  have h3_10r := Ne.symm h3_10
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h4_7r := Ne.symm h4_7
  have h4_8r := Ne.symm h4_8
  have h4_9r := Ne.symm h4_9
  have h4_10r := Ne.symm h4_10
  have h5_6r := Ne.symm h5_6
  have h5_7r := Ne.symm h5_7
  have h5_8r := Ne.symm h5_8
  have h5_9r := Ne.symm h5_9
  have h5_10r := Ne.symm h5_10
  have h6_7r := Ne.symm h6_7
  have h6_8r := Ne.symm h6_8
  have h6_9r := Ne.symm h6_9
  have h6_10r := Ne.symm h6_10
  have h7_8r := Ne.symm h7_8
  have h7_9r := Ne.symm h7_9
  have h7_10r := Ne.symm h7_10
  have h8_9r := Ne.symm h8_9
  have h8_10r := Ne.symm h8_10
  have h9_10r := Ne.symm h9_10
  have flagR (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      f∉L.r := fun h => flagAway L hn f hf (by simp [h])
  have away (a : Wire)
      (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      a∉rawTarget L := compose_raw_away L hn a ha
  have neq (a : Wire) (ha : a∈L.y++L.carry)
      (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
    by
      intro e
      apply flagAway L hn f hf
      subst a
      simp only [List.mem_append] at ha ⊢
      tauto
  have nr (a : Wire) (ha : a∈L.y++L.carry) : a∉L.r := by
    have d := (List.nodup_append'.mp (allND L hn)).2.1
    have dn : (L.r++(L.y++L.carry)).Nodup := by
      simpa only [List.append_assoc] using d
    exact fun h => List.disjoint_left.mp (List.nodup_append'.mp dn).2.2 h ha
  have f0 (a : Wire) (ha : a≠L.sourceGuard) : u0.basis a=s.basis a := by
    simp [u0,run,writeBit,ha]
  have g0 : u0.basis L.sourceGuard=s.basis L.ymsb := by
    simp [u0,run,writeBit,hc L.sourceGuard (by simp [work])]
  have r0 : regValue L.r u0.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 w.2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => f0 a
      (fun e => flagR L.sourceGuard (by simp) (e ▸ ha)))
  have y0 : regValue L.y u0.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 w.2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => f0 a (neq a (by simp [ha]) _ (by simp)))
  have z0 (a : Wire) (ha : a∈work L) (hg : a≠L.sourceGuard) : u0.basis a=false :=
    (f0 a hg).trans (hc a ha)
  have pre := recoverPrefix_correct L hw cnd R Y B hr hy u0 m r0 y0
    ((f0 _ (by assumption)).trans hs) (z0 _ (by simp [work]) (by assumption))
    (z0 _ (by simp [work]) (by assumption))
    (fun a ha => z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp)))
  have p1 : u1.basis L.parity=P := by
    rw [pre.2.2.2.1,z0 _ (by simp [work]) (by assumption),par]
    exact Bool.false_xor P
  have view := unbiasView_correct L hw cnd R hr u1 m1 pre.2.1 pre.2.2.1
  have f2 (a : Wire) (ar : a∉L.r) (al : a≠L.lower) (ap : a≠L.parity) : u2.basis a=u0.basis a :=
    (view.2.2.2 a ar al).trans (pre.2.2.2.2 a ar al ap)
  have p2 : u2.basis L.parity=P :=
    (view.2.2.2 _ (flagR _ (by simp)) (by assumption)).trans p1
  have r2 : regValue L.r u2.basis=encodeWord 256 (biased (halfResult T)) := by
    rw [half]; exact view.2.1
  have restore := restoreRaw_correct L hw hn T ht u2 m2 p2 r2 view.2.2.1
    ((f2 _ (flagR _ (by simp)) (by assumption) (by assumption)).trans (z0 _ (by simp [work]) (by assumption)))
    ((f2 _ (flagR _ (by simp)) (by assumption) (by assumption)).trans (z0 _ (by simp [work]) (by assumption)))
    (fun a ha => (f2 a (nr a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp))).trans
      (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp))))
  have f3 (a : Wire) (ar : a∉rawTarget L) (al : a≠L.lower) (am : a≠L.minus)
      (ap : a≠L.parity) : u3.basis a=u0.basis a :=
    (restore.2.2.2.2 a ar al am).trans
      (f2 a (fun h => ar (by simp [rawTarget,h])) al ap)
  have p3 : u3.basis L.parity=P :=
    (restore.2.2.2.2 _ (away _ (by simp)) (by assumption) (by assumption)).trans p2
  have y3 : signedRegValue L.y u3.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    exact (f3 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
      (f0 a (neq a (by simp [ha]) _ (by simp)))
  have g3 : u3.basis L.sourceGuard=u3.basis L.ymsb := by
    have g := (f3 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g0
    have y := (f3 L.ymsb (away _ (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f0 _ (by assumption))
    exact g.trans y.symm
  have src3 : signedRegValue (rawSource L) u3.basis=Y :=
    (signed_extension L.ylow L.ymsb L.sourceGuard u3.basis g3).trans y3
  have raw3 : signedRegValue (rawTarget L) u3.basis=T := by
    unfold signedRegValue
    rw [rwid.2.1,restore.2.1]
    apply decode_encodeWord 257 (by norm_num)
    have c := constants
    norm_num at ⊢
    omega
  have carry3 : regValue L.carry u3.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (f3 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
      (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp)))
  have sign3 : u3.basis L.sign=B :=
    (f3 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans ((f0 _ (by assumption)).trans hs)
  have sub := BalancedInverse.rawSubtract_signed L hw hn B X Y hx u3 m3 sign3 src3 raw3 carry3
  have y4 : signedRegValue L.y u4.basis=Y := by
    apply Eq.trans _ y3
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => sub.2.2 a (away a (by simp [ha])))
  have g4 : u4.basis L.sourceGuard=u4.basis L.ymsb :=
    (sub.2.2 _ (away _ (by simp))).trans (g3.trans
      (sub.2.2 _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p4 : u4.basis L.parity=P := (sub.2.2 _ (away _ (by simp))).trans p3
  have seed := BalancedInverse.unseed_packet L hw hn B X Y hx u4 m4 sub.2.1 y4 g4 p4
  have f4 (a : Wire) (ar : a∉rawTarget L) (al : a≠L.lower) (am : a≠L.minus)
      (ap : a≠L.parity) : u4.basis a=u0.basis a := (sub.2.2 a ar).trans (f3 a ar al am ap)
  have clean : ∀a∈work L,out.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact seed.2.1
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((f4 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          (z0 _ (by simp [work]) (by assumption)))
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((sub.2.2 _ (away _ (by simp))).trans restore.2.2.2.1)
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((f4 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          (z0 _ (by simp [work]) (by assumption)))
    · exact seed.2.2.2.1
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((sub.2.2 _ (away _ (by simp))).trans restore.2.2.1)
    · exact seed.2.2.1
    · exact (seed.2.2.2.2 a (neq a (by simp [ha]) _ (by simp))
        (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
        ((f4 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
          (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
          (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp))))
  have frame : ∀a,a∉L.r → out.basis a=s.basis a := by
    intro a ar
    by_cases aw : a∈work L
    · exact (clean a aw).trans (hc a aw).symm
    · have ne (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus]) : a≠f := by
        intro e
        apply aw
        subst a
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        tauto
      have rawA : a∉rawTarget L := by simp [rawTarget,ar,ne L.one (by simp)]
      exact (seed.2.2.2.2 a (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))).trans
        ((f4 a rawA (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))).trans
          (f0 a (ne _ (by simp))))
  have value : regValue L.r out.basis=encodeWord 256 X := by
    have corr := BalancedInverse.unseed_correlations L hw B X Y hx u4 sub.2.1 y4 g4 p4
    have narrow : signedRegValue L.r u4.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u4.basis corr.1).symm.trans sub.2.1
    apply Eq.trans _ (word_encoding L.r 256 w.2.1 u4.basis X narrow)
    apply regValue_congr
    intro a ha
    have ne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagR f hf (e ▸ ha)
    exact seed.2.2.2.2 a (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))
  have actual : run (program L) m s=out := by
    simp only [program,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from by simp only [measurementCount],List.drop_zero]
    change run (recoverPrefix L ++ (unbiasView L ++ (restoreRaw L ++
      (BalancedInverse.rawSubtract L ++ (seedViews L).reverse)))) m u0=out
    rw [run_append,run_take]
    change run (unbiasView L ++ (restoreRaw L ++
      (BalancedInverse.rawSubtract L ++ (seedViews L).reverse))) m1 u1=out
    rw [run_append,run_take]
    change run (restoreRaw L ++ (BalancedInverse.rawSubtract L ++ (seedViews L).reverse)) m2 u2=out
    rw [run_append,run_take]
    change run (BalancedInverse.rawSubtract L ++ (seedViews L).reverse) m3 u3=out
    rw [run_append,run_take]
  rw [actual]
  have ph0 : u0.phase=s.phase := by simp [u0,run]
  exact ⟨seed.1.trans (sub.1.trans (restore.1.trans (view.1.trans (pre.1.trans ph0)))),value,clean,frame⟩

/-- Whole-state interchangeability permits independent measurement tapes. -/
theorem kernel_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀a∈work L,s.basis a=false) :
    run (program L) m s=run (BalancedInverse.program L) n s := by
  have fresh := program_correct L hw hn B R Y hr hy s m hs hR hY hc
  have old := BalancedInverse.program_correct L hw hn B R Y hr hy s n hs hR hY hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext a
    by_cases ha : a∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) a ha
    · exact (fresh.2.2.2 a ha).trans (old.2.2.2 a ha).symm

end ECDSAAdd.Entrant.BiasedInverse

end

section
-- ===== BiasedInverseSupport =====
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic Arithmetic.BalancedCircuit

theorem support (L : Layout) (hw : L.Widths) : wires (program L) ⊆ L.wires.toFinset := by
  have old := BalancedInverse.support L hw
  simp only [BalancedInverse.program,wires_append,Finset.union_subset_iff] at old
  have cl := BalancedCleanup.support L.toLayout hw
  have embed : L.toLayout.wires.toFinset ⊆ L.wires.toFinset := by
    intro a ha
    simp only [Layout.wires,List.toFinset_append,Finset.mem_union]
    exact Or.inr ha
  have cls := Finset.Subset.trans cl embed
  simp only [BalancedCleanup.program,wires_append,Finset.union_subset_iff] at cls
  have pre : wires (recoverPrefix L) ⊆ L.wires.toFinset := by
    simp only [recoverPrefix,wires_append,Finset.union_subset_iff]
    tauto
  have member (a : Wire) : a∈L.wires.toFinset ↔
      a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      a∈L.rtail ∨ a∈L.ylow ∨ a∈L.carry := by
    simp [Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have small (a : Wire) (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0]) :
      a∈L.wires.toFinset := (member a).mpr (Or.inl ha)
  have rmem (a : Wire) (ha : a∈L.r) : a∈L.wires.toFinset := by
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    simp only [member,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have flip : wires [.X (L.r.getD 254 0)] ⊆ L.wires.toFinset := by
    have w := BalancedCleanup.widths L.toLayout hw
    have idx : 254<L.r.length := by omega
    have bit : L.r.getD 254 0∈L.r := by
      rw [List.getD_eq_getElem _ _ idx]
      exact List.getElem_mem _
    simpa [wires,Instr.wires] using rmem _ bit
  have view : wires (unbiasView L) ⊆ L.wires.toFinset := by
    simp only [unbiasView,wires_append,Finset.union_subset_iff]
    exact ⟨flip,cls.2.2.2.2.2.2⟩
  have mapped := mappedSub_wires_subset (biasBits L) L.r (L.carry.take 255) L.minus
  have unfoldS : wires (unfoldBias L) ⊆ L.wires.toFinset := by
    intro a ha
    have h := mapped ha
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with h|h|h|h
    · rcases biasBits_sources L a h with rfl|rfl <;> exact small _ (by simp)
    · exact rmem a h
    · exact (member a).mpr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_take h))))
    · exact small a (by simp [h])
  have sel : wires (selectors L) ⊆ L.wires.toFinset := by
    intro a ha
    simp only [selectors,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty] at ha
    apply small
    simp only [List.mem_cons,List.not_mem_nil]
    tauto
  have rel : wires (release L) ⊆ L.wires.toFinset := by
    intro a ha
    simp only [release,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty] at ha
    apply small
    simp only [List.mem_cons,List.not_mem_nil]
    tauto
  have ins : wires [.CX L.parity L.r0] ⊆ L.wires.toFinset := by
    intro a ha
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at ha
    apply small
    simp only [List.mem_cons,List.not_mem_nil]
    tauto
  simp only [program,restoreRaw,wires_append,Finset.union_subset_iff]
  tauto

end ECDSAAdd.Entrant.BiasedInverse

end


section
namespace ECDSAAdd.Entrant.ShortKernelDependencies
open Arithmetic Arithmetic.BalancedField Secp256k1 Challenge Baselines Arithmetic.FieldRename
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] literalConstAdd compareLt rotateLeft rotateRight signComplement addInPlace subInPlace mappedAdd mappedSub swapRegisters transcriptSelectWindow
theorem biasedCircuit_support (L : BalancedCircuit.Layout) (hw : L.Widths) :
    wires (BiasedCircuit.program L)⊆L.wires.toFinset := by
  intro q hq
  have h := BiasedCircuit.support L hw hq
  simp only [BiasedCircuit.activeWires,BalancedCircuit.Layout.wires,List.mem_toFinset,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  tauto

theorem bf_r_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (mapCircuit f L).r=L.r.map f := r_map f L.toLayout
theorem bf_y_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (mapCircuit f L).y=L.y.map f := y_map f L.toLayout
theorem bf_low_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (mapCircuit f L).low=L.low.map f := low_map f L.toLayout

theorem bf_biasBits_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (BiasedCircuit.biasBits L).map (mapBit f)=BiasedCircuit.biasBits (mapCircuit f L) := by
  simp only [BiasedCircuit.biasBits,List.map_append,List.map_map,List.map_cons,List.map_nil]
  rfl

theorem bf_flip_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    renameProgram f (BiasedCircuit.flipBias L)=BiasedCircuit.flipBias (mapCircuit f L) := by
  have h : 253<L.rtail.length := by rw [hw.1]; omega
  simp [BiasedCircuit.flipBias,renameProgram,renameInstr,mapCircuit,mapCleanup,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]

theorem bf_prefix_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hy : L.ylow≠[]) :
    renameProgram f (BiasedCircuit.biasedPrefix L)=BiasedCircuit.biasedPrefix (mapCircuit f L) := by
  have pf : renameProgram f (BiasedCircuit.prepareFold L)=
      BiasedCircuit.prepareFold (mapCircuit f L) := by
    simp only [BiasedCircuit.prepareFold,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr]
  have sv : renameProgram f (BiasedCircuit.signView L)=BiasedCircuit.signView (mapCircuit f L) := by
    simp only [BiasedCircuit.signView,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr]
  have rs : renameProgram f (BiasedCircuit.releaseSelectors L)=
      BiasedCircuit.releaseSelectors (mapCircuit f L) := by
    simp only [BiasedCircuit.releaseSelectors,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr,renameCorrection]
  have fd : renameProgram f (BiasedCircuit.fold L)=BiasedCircuit.fold (mapCircuit f L) := by
    simp only [BiasedCircuit.fold,mappedAdd_natural,bf_biasBits_map,List.map_take,bf_r_map]
    rfl
  simp only [BiasedCircuit.biasedPrefix,rename_append,seedViews_natural f L hy,rawAdd_natural,
    pf,rotateRight_natural,rawTarget_map,sv,fd,rs,prepareSign_natural,bf_flip_natural f L hw]
  rfl

theorem bf_suffix_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BiasedCircuit.cleanupSuffix L)=BiasedCircuit.cleanupSuffix (mapCircuit f L) := by
  simp only [BiasedCircuit.cleanupSuffix,BalancedCleanup.unnormalize,BalancedCleanup.prepareCompare,
    rename_append,rename_reverse,prepareSign_natural,literalConstAdd_natural,rotateLeft_natural,
    signComplement_natural,compareLt_natural,bf_low_map,bf_r_map,bf_y_map,List.map_take]
  rfl

theorem biasedCircuit_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    renameProgram f (BiasedCircuit.program L)=BiasedCircuit.program (mapCircuit f L) := by
  have hy : L.ylow≠[] := by
    intro e
    have h := hw.2.1
    rw [e] at h
    simp at h
  simp only [BiasedCircuit.program,rename_append,bf_prefix_natural f L hw hy,bf_suffix_natural]

theorem bi_biasBits_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (BiasedInverse.biasBits L).map (mapBit f)=BiasedInverse.biasBits (mapCircuit f L) := by
  simp only [BiasedInverse.biasBits,List.map_append,List.map_map,List.map_cons,List.map_nil]
  rfl

theorem bi_recoverPrefix_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BiasedInverse.recoverPrefix L)=BiasedInverse.recoverPrefix (mapCircuit f L) := by
  simp only [BiasedInverse.recoverPrefix,BalancedCleanup.normalize,BalancedCleanup.prepareCompare,
    rename_append,rename_reverse,prepareSign_natural,literalConstAdd_natural,
    rotateLeft_natural,signComplement_natural,compareLt_natural,mapCircuit,low_map,r_map,y_map,List.map_take]
  rfl

theorem bi_r_getD_map (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    (mapCircuit f L).r.getD 254 0=f (L.r.getD 254 0) := by
  have w := (BalancedCleanup.widths L.toLayout hw).2.1
  have h : 254<L.r.length := by omega
  change (mapCleanup f L.toLayout).r.getD 254 0=f (L.r.getD 254 0)
  rw [r_map,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using h),
    List.getD_eq_getElem _ _ h,List.getElem_map]

theorem bi_unbiasView_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    renameProgram f (BiasedInverse.unbiasView L)=BiasedInverse.unbiasView (mapCircuit f L) := by
  simp only [BiasedInverse.unbiasView,rename_append,rename_reverse,prepareSign_natural,
    bi_r_getD_map f L hw]
  rfl

theorem bi_selectors_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BiasedInverse.selectors L)=BiasedInverse.selectors (mapCircuit f L) := rfl

theorem bi_release_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BiasedInverse.release L)=BiasedInverse.release (mapCircuit f L) := rfl

theorem bi_restoreRaw_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (BiasedInverse.restoreRaw L)=BiasedInverse.restoreRaw (mapCircuit f L) := by
  have rm : (mapCircuit f L).r=L.r.map f := r_map f L.toLayout
  simp only [BiasedInverse.restoreRaw,BiasedInverse.unfoldBias,rename_append,
    bi_selectors_natural,mappedSub_natural,bi_biasBits_map,bi_release_natural,
    rotateLeft_natural,rawTarget_map,rm,List.map_take]
  rfl

/-- Relabeling uses the valid result width so the selected high bit is present. -/
theorem biasedInverse_natural (f : Wire → Wire) (L : BalancedCircuit.Layout)
    (hy : L.ylow ≠ []) (hw : L.Widths) :
    renameProgram f (BiasedInverse.program L)=BiasedInverse.program (mapCircuit f L) := by
  simp only [BiasedInverse.program,rename_append,rename_reverse,
    bi_recoverPrefix_natural,bi_unbiasView_natural f L hw,bi_restoreRaw_natural,
    rawSubtract_natural,seedViews_natural f L hy]
  rfl


end ECDSAAdd.Entrant.ShortKernelDependencies
end

-- ===== Root verified Short kernel Arithmetic =====
section
namespace ECDSAAdd.Entrant.ShortBiasedFold
open Arithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
abbrev Layout := BalancedCircuit.Layout

def lowBits (L : Layout) : List MappedBit := (BiasedCircuit.biasBits L).take 255

def shortFold (L : Layout) : Program :=
  mappedAdd (lowBits L) L.low (L.carry.take 254) L.minus ++ [.CX L.parity L.rmsb]

def shortUnfold (L : Layout) : Program :=
  mappedSub (lowBits L) L.low (L.carry.take 254) L.minus ++ [.CX L.parity L.rmsb]

theorem lowBits_length (L : Layout) : (lowBits L).length=255 := by
  simp [lowBits,BiasedCircuit.biasBits]

theorem short_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (shortFold L)=254 ∧ measurementCount (shortFold L)=254 ∧
    toffoliCount (shortUnfold L)=254 ∧ measurementCount (shortUnfold L)=254 := by
  have widths := BalancedCleanup.widths L.toLayout hw
  have len : (lowBits L).length=L.low.length := by rw [lowBits_length,widths.1]
  have carry : (L.carry.take 254).length+1=L.low.length := by
    simp [List.length_take,hw.2.2,widths.1]
  have a := mappedAdd_counts (lowBits L) L.low (L.carry.take 254) L.minus len carry
  have b := mappedSub_counts (lowBits L) L.low (L.carry.take 254) L.minus len carry
  simp only [shortFold,shortUnfold,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,widths.1]
  norm_num [toffoliCount,measurementCount]

theorem low_sum_mod (n x y xh yh c : Nat) :
    (((x+2^n*xh)+(y+2^n*yh)+c)%2^(n+1))%2^n=(x+y+c)%2^n := by
  rw [Nat.mod_mod_of_dvd _ (show 2^n∣2^(n+1) from ⟨2,by simp [Nat.pow_succ]⟩)]
  simp [Nat.add_mod,Nat.mul_mod]

theorem reg_low_mod (ys : List Wire) (top : Wire) (s : BasisState) :
    regValue (ys++[top]) s %2^ys.length=regValue ys s := by
  rw [regValue_append]
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt (regValue_lt ys s)]

/-- The full adder's low word is independent of the source and target top bits. -/
theorem full_add_low (bits : List MappedBit) (b : MappedBit) (ys carry : List Wire)
    (top cin : Wire) (hl : bits.length=ys.length) (hc : carry.length=ys.length)
    (hn : (cin::((ys++[top])++carry)).Nodup)
    (hs : ∀q∈mappedWires (bits++[b]),q∉cin::((ys++[top])++carry))
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false) :
    regValue ys (run (mappedAdd (bits++[b]) (ys++[top]) carry cin) m s).basis=
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  have add := mappedAdd_correct (bits++[b]) (ys++[top]) carry cin hn hs
    (by simp [hl]) (by simp [hc]) s m clean
  have h := congrArg (fun v : Nat => v%2^ys.length) add.2.2
  dsimp only at h
  rw [reg_low_mod] at h
  rw [mappedValue_append,regValue_append,hl,List.length_append,List.length_singleton] at h
  simpa only [mappedValue,regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,
    low_sum_mod] using h

/-- A known high output bit lets the full ripple be replaced by a low ripple and CX. -/
theorem full_add_eq_short (bits : List MappedBit) (b : MappedBit)
    (ys carry small : List Wire) (top cin control : Wire)
    (hl : bits.length=ys.length) (hc : carry.length=ys.length)
    (hsmall : small.length+1=ys.length)
    (hn : (cin::((ys++[top])++carry)).Nodup)
    (hs : ∀q∈mappedWires (bits++[b]),q∉cin::((ys++[top])++carry))
    (hn' : (cin::(ys++small)).Nodup)
    (hs' : ∀q∈mappedWires bits,q∉cin::(ys++small))
    (htop : top∉ys) (hcontrol : control∉ys)
    (s : State) (m n : List Bool)
    (clean : ∀q∈carry,s.basis q=false) (clean' : ∀q∈small,s.basis q=false)
    (high : (run (mappedAdd (bits++[b]) (ys++[top]) carry cin) m s).basis top =
      (s.basis top ^^ s.basis control)) :
    run (mappedAdd (bits++[b]) (ys++[top]) carry cin) m s =
    run (mappedAdd bits ys small cin ++ [.CX control top]) n s := by
  have full := mappedAdd_correct (bits++[b]) (ys++[top]) carry cin hn hs
    (by simp [hl]) (by simp [hc]) s m clean
  have low := full_add_low bits b ys carry top cin hl hc hn hs s m clean
  have narrow := mappedAdd_correct bits ys small cin hn' hs' hl hsmall s n clean'
  rw [run_append]
  simp only [run_take,run]
  generalize he : run (mappedAdd (bits++[b]) (ys++[top]) carry cin) m s = v at full low high ⊢
  generalize hf : run (mappedAdd bits ys small cin) n s = u at narrow ⊢
  refine State.extensionality v ⟨u.phase,writeBit u.basis top (u.basis top ^^ u.basis control)⟩
    (full.1.trans narrow.1.symm) ?_
  funext q
  by_cases qt : q=top
  · subst q
    change v.basis top = (writeBit u.basis top (u.basis top ^^ u.basis control)) top
    rw [writeBit,Function.update_self,narrow.2.1 top htop,narrow.2.1 control hcontrol]
    exact high
  · simp only [writeBit,Function.update_of_ne qt]
    by_cases qy : q∈ys
    · exact (regValue_eq_iff ys v.basis u.basis).mp (low.trans narrow.2.2.symm) q qy
    · exact (full.2.1 q (by simp [qy,qt])).trans (narrow.2.1 q qy).symm
theorem biasBits_split (L : Layout) :
    BiasedCircuit.biasBits L = lowBits L ++ [{wire:=some L.one,flip:=false}] := by
  simp [lowBits,BiasedCircuit.biasBits,List.take_append]

theorem biased_fold_eq (L : Layout) (hw : L.Widths)
    (hn : (L.minus::(L.r++L.carry.take 255)).Nodup)
    (hs : ∀q∈mappedWires (BiasedCircuit.biasBits L),q∉L.minus::(L.r++L.carry.take 255))
    (hn' : (L.minus::(L.low++L.carry.take 254)).Nodup)
    (hs' : ∀q∈mappedWires (lowBits L),q∉L.minus::(L.low++L.carry.take 254))
    (htop : L.rmsb∉L.low) (hpar : L.parity∉L.low)
    (T : Int) (ht : -(2*Arithmetic.BalancedField.q)≤T ∧ T≤2*Arithmetic.BalancedField.q)
    (s : State) (m n : List Bool)
    (hv : regValue L.r s.basis=Arithmetic.BalancedField.encodeWord 257 T/2)
    (hl : s.basis L.lower=decide (T<0))
    (ho : s.basis L.one=Arithmetic.BalancedField.negative (Arithmetic.BalancedField.halfResult T))
    (hp : s.basis L.parity=Arithmetic.BalancedField.originalParity T)
    (hm : s.basis L.minus=(Arithmetic.BalancedField.originalParity T && decide (T<0)))
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (BiasedCircuit.fold L) m s=run (shortFold L) n s := by
  have widths := BalancedCleanup.widths L.toLayout hw
  have add := mappedAdd_correct (BiasedCircuit.biasBits L) L.r (L.carry.take 255) L.minus hn hs
    (by simp [BiasedCircuit.biasBits,widths.2.1])
    (by simp [List.length_take,hw.2.2,widths.2.1]) s m
    (fun q hq => clean q (List.mem_of_mem_take hq))
  have val : regValue L.r (run (BiasedCircuit.fold L) m s).basis =
      Arithmetic.BalancedField.encodeWord 256 (BiasedCircuit.biasedValue (Arithmetic.BalancedField.halfResult T)) := by
    rw [BiasedCircuit.fold,add.2.2,BiasedCircuit.biasBits_value,hv,hl,ho,hm,widths.2.1]
    simpa only [Nat.add_comm] using BiasedCircuit.fold_arithmetic T ht
  have out := BiasedCircuit.biased_sign L hw _ (Arithmetic.BalancedField.halfResult_spec T ht).1 _ val
  have enc := BiasedInverse.half_encoding T ht
  have raw : regValue L.r s.basis=Arithmetic.BalancedField.encodeWord 256 (T/2) := by
    rw [hv]
    cases p : Arithmetic.BalancedField.originalParity T <;> simp [p] at enc <;> omega
  have inp := BiasedInverse.half_msb L hw T ht s.basis raw
  have high : (run (BiasedCircuit.fold L) m s).basis L.rmsb =
      (s.basis L.rmsb ^^ s.basis L.parity) := by
    rw [out,inp,hp]
    exact Arithmetic.BalancedField.halfResult_sign T ht
  have oldShape : BiasedCircuit.fold L = mappedAdd
      (lowBits L ++ [{wire:=some L.one,flip:=false}]) (L.low++[L.rmsb])
      (L.carry.take 255) L.minus := by
    rw [BiasedCircuit.fold,biasBits_split]; rfl
  rw [oldShape] at high ⊢
  exact full_add_eq_short (lowBits L) {wire:=some L.one,flip:=false} L.low
    (L.carry.take 255) (L.carry.take 254) L.rmsb L.minus L.parity
    (by rw [lowBits_length,widths.1])
    (by simp [List.length_take,hw.2.2,widths.1])
    (by simp [List.length_take,hw.2.2,widths.1])
    hn (by simpa only [←biasBits_split] using hs) hn' hs' htop hpar s m n
    (fun q hq => clean q (List.mem_of_mem_take hq))
    (fun q hq => clean q (List.mem_of_mem_take hq)) high
theorem biased_fold_layout_eq (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*Arithmetic.BalancedField.q)≤T ∧ T≤2*Arithmetic.BalancedField.q)
    (s : State) (m n : List Bool)
    (hv : regValue L.r s.basis=Arithmetic.BalancedField.encodeWord 257 T/2)
    (hl : s.basis L.lower=decide (T<0))
    (ho : s.basis L.one=Arithmetic.BalancedField.negative (Arithmetic.BalancedField.halfResult T))
    (hp : s.basis L.parity=Arithmetic.BalancedField.originalParity T)
    (hm : s.basis L.minus=(Arithmetic.BalancedField.originalParity T && decide (T<0)))
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (BiasedCircuit.fold L) m s=run (shortFold L) n s := by
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have fullND : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have smallND : (L.minus::(L.low++L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have fullSrc : ∀q∈mappedWires (BiasedCircuit.biasBits L),q∉L.minus::(L.r++L.carry.take 255) := by
    intro q hq hmem
    have src := BiasedCircuit.biasBits_sources L q hq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have smallSrc : ∀q∈mappedWires (lowBits L),q∉L.minus::(L.low++L.carry.take 254) := by
    intro q hq hmem
    have fullq : q∈mappedWires (BiasedCircuit.biasBits L) := by
      rw [biasBits_split]
      simp only [mappedWires,List.flatMap_append,List.mem_append]
      exact Or.inl hq
    have src := BiasedCircuit.biasBits_sources L q fullq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [BalancedCleanup.Layout.r,he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have topAway : L.rmsb∉L.low := by
    intro bad
    have data := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) L.rmsb
    have cnt := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at data
    simp at data
    omega
  have parityAway : L.parity∉L.low := by
    intro bad
    exact BalancedCircuit.flagAway L hn L.parity (by simp) (by simp [BalancedCleanup.Layout.r,bad])
  exact biased_fold_eq L hw fullND fullSrc smallND smallSrc topAway parityAway T ht s m n hv hl ho hp hm clean
end ECDSAAdd.Entrant.ShortBiasedFold
end

-- ===== Root verified Short kernel FoldStates =====
section
namespace ECDSAAdd.Entrant.ShortBiasedFold
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.BalancedField ECDSAAdd.Entrant.BiasedCircuit
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem foldStates (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (v w a b z t d e : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hv : regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T)
    (hp : v.basis L.parity=originalParity T) (ho : v.basis L.one=decide (T<0))
    (h0 : v.basis L.r0=originalParity T) (hl : v.basis L.lower=false)
    (hm : v.basis L.minus=false) (hc : ∀q∈L.carry,v.basis q=false)
    (ew : run (prepareFold L) m1 v=w)
    (ea : run (rotateRight (BalancedCircuit.rawTarget L)) m2 w=a)
    (eb : run (signView L) m3 a=b) (ez : run (shortFold L) m4 b=z)
    (et : run (releaseSelectors L) m5 z=t)
    (ed : run (BalancedCleanup.prepareSign L.toLayout) m6 t=d)
    (ee : run (flipBias L) m7 d=e) :
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q) := by
  let P := originalParity T
  let N := decide (T<0)
  let R := halfResult T
  let H := negative R
  have rc : Centered R := (halfResult_spec T ht).1
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have away (f : Wire)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]) :
      f∉BalancedCircuit.rawTarget L := BalancedCircuit.compose_not_raw L hn f hf
  have dataflag (q : Wire) (hq : q∈L.r++L.carry) (f : Wire)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f :=
    by
      intro eq
      have hd : f∈L.r++L.carry := eq ▸ hq
      exact BalancedCircuit.flagAway L hn f hf (by simp only [List.mem_append] at hd ⊢; tauto)
  have wp := prepareFold_run L hn P N v m1 hp ho h0 hl hm
  rw [ew] at wp
  have wf (q : Wire) (ql : q≠L.lower) (qm : q≠L.minus) (q0 : q≠L.r0) :
      w.basis q=v.basis q := by rw [wp]; simp only [writeBit,
        Function.update_of_ne ql,Function.update_of_ne qm,Function.update_of_ne q0]
  have w0 : w.basis L.r0=false := by rw [wp]; simp [writeBit]
  have wl : w.basis L.lower=N := by rw [wp]; simp only [writeBit,
    Function.update_of_ne (show L.lower≠L.r0 by tauto),
    Function.update_of_ne (show L.lower≠L.minus by tauto),Function.update_self]
  have wm : w.basis L.minus=(P && N) := by rw [wp]; simp only [writeBit,
    Function.update_of_ne (show L.minus≠L.r0 by tauto),Function.update_self]
  have shape : BalancedCircuit.rawTarget L=L.r0::BalancedCircuit.foldTarget L := by
    simp [BalancedCircuit.rawTarget,BalancedCircuit.foldTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have wr : regValue (BalancedCircuit.rawTarget L) w.basis=
      2*regValue (BalancedCircuit.foldTarget L) v.basis := by
    rw [shape]
    change (if w.basis L.r0 then 1 else 0)+2*regValue (BalancedCircuit.foldTarget L) w.basis=_
    rw [w0]
    simp only [Bool.false_eq_true,if_false,zero_add]
    congr 1
    apply regValue_congr
    intro q hq
    have qr : q∈BalancedCircuit.rawTarget L := by rw [shape]; simp [hq]
    have nq : q≠L.r0 := fun e => BalancedCircuit.compose_not_fold_r0 L hn (e ▸ hq)
    exact wf q (fun e => away L.lower (by simp) (e ▸ qr))
      (fun e => away L.minus (by simp) (e ▸ qr)) nq
  have rawv : regValue (BalancedCircuit.foldTarget L) v.basis=encodeWord 257 T/2 := by
    rw [shape] at hv
    change (if v.basis L.r0 then 1 else 0)+2*regValue (BalancedCircuit.foldTarget L) v.basis=_ at hv
    rw [h0] at hv
    cases hp0 : originalParity T <;> simp [hp0] at hv <;> omega
  rw [rawv] at wr
  have rot := rotateRight_spec (BalancedCircuit.rawTarget L) (BalancedCircuit.rawTargetND L hn)
    (2*(encodeWord 257 T/2)) (by omega) w m2 wr
  rw [ea] at rot
  have av : regValue (BalancedCircuit.rawTarget L) a.basis=encodeWord 257 T/2 := by
    have val := rot.2
    change regValue (BalancedCircuit.rawTarget L) a.basis=2*(encodeWord 257 T/2)/2 at val
    omega
  have af (q : Wire) (hq : q∉BalancedCircuit.rawTarget L) : a.basis q=w.basis q := by
    simpa only [ea] using (rotate_frame (BalancedCircuit.rawTarget L) w m2).2.1 q hq
  have ao : a.basis L.one=false := by
    have bit := regValue_highBit L.r L.one a.basis
    rw [(BalancedCleanup.widths L.toLayout hw).2.1] at bit
    change a.basis L.one=true ↔ 2^256≤regValue (BalancedCircuit.rawTarget L) a.basis at bit
    rw [av] at bit
    have bound := encodeWord_bound 257 T
    norm_num at bound bit
    cases ba : a.basis L.one <;> simp_all <;> omega
  have ar : regValue L.r a.basis=encodeWord 257 T/2 := by
    rw [BalancedCircuit.rawTarget,regValue_append] at av
    simpa [regValue,ao] using av
  have ap : a.basis L.parity=P :=
    (af _ (away _ (by simp))).trans ((wf _ (by tauto) (by tauto) (by tauto)).trans hp)
  have al : a.basis L.lower=N := (af _ (away _ (by simp))).trans wl
  have bp := signView_run L hn P N a m3 ap ao al
  rw [eb] at bp
  have bf (q : Wire) (hq : q≠L.one) : b.basis q=a.basis q := by
    rw [bp]; simp only [writeBit,Function.update_of_ne hq]
  have bo : b.basis L.one=H := by
    rw [bp]
    simp only [writeBit,Function.update_self]
    have sg := halfResult_sign T ht
    change (P ^^ N)=negative (halfResult T)
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    exact Bool.xor_comm _ _
  have bl : b.basis L.lower=N := (bf _ (by tauto)).trans al
  have bpar : b.basis L.parity=P := (bf _ (by tauto)).trans ap
  have bm : b.basis L.minus=(P && N) :=
    (bf _ (by tauto)).trans ((af _ (away _ (by simp))).trans wm)
  have br : regValue L.r b.basis=encodeWord 257 T/2 :=
    (regValue_congr _ _ _ (fun q hq => bf q (dataflag q (by simp [hq]) _ (by simp)))).trans ar
  have bc : ∀q∈L.carry,b.basis q=false := by
    intro q hq
    have ql := dataflag q (by simp [hq]) L.lower (by simp)
    have qm := dataflag q (by simp [hq]) L.minus (by simp)
    have qo := dataflag q (by simp [hq]) L.one (by simp)
    have q0 : q≠L.r0 := by
      intro eq
      have raw := BalancedCircuit.compose_raw_away L hn q (by simp [hq])
      exact raw (by simp [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,eq])
    exact (bf q qo).trans ((af q (BalancedCircuit.compose_raw_away L hn q (by simp [hq]))).trans
      ((wf q ql qm q0).trans (hc q hq)))
  have fd : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have fs : ∀q∈mappedWires (biasBits L),q∉L.minus::(L.r++L.carry.take 255) := by
    intro q hq hmem
    have src := biasBits_sources L q hq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have foldEq := biased_fold_layout_eq L hw hn T ht b m4 m4 br bl bo bpar bm bc
  rw [←foldEq] at ez
  have add := mappedAdd_correct (biasBits L) L.r (L.carry.take 255) L.minus fd fs
    (by simp [biasBits,(BalancedCleanup.widths L.toLayout hw).2.1])
    (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1])
    b m4 (fun q hq => bc q (List.mem_of_mem_take hq))
  simp only [show mappedAdd (biasBits L) L.r (L.carry.take 255) L.minus=fold L from rfl,ez] at add
  have zv : regValue L.r z.basis=encodeWord 256 (biasedValue R) := by
    rw [add.2.2,biasBits_value,br,bl,bo,bm,(BalancedCleanup.widths L.toLayout hw).2.1]
    simpa only [Nat.add_comm] using fold_arithmetic T ht
  have zr : z.basis L.rmsb=H := biased_sign L hw R rc z.basis zv
  have zp : z.basis L.parity=P :=
    (add.2.1 _ (fun h => away L.parity (by simp) (by simp [BalancedCircuit.rawTarget,h]))).trans bpar
  have zl : z.basis L.lower=(H ^^ P) := by
    rw [add.2.1 _ (fun h => away L.lower (by simp) (by simp [BalancedCircuit.rawTarget,h])),bl]
    have sg := halfResult_sign T ht
    change N=(negative (halfResult T) ^^ P)
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    cases N <;> cases P <;> rfl
  have zm : z.basis L.minus=(P && !H) := by
    rw [add.2.1 _ (fun h => away L.minus (by simp) (by simp [BalancedCircuit.rawTarget,h])),bm]
    have sg := halfResult_sign T ht
    change (P && N)=(P && !negative (halfResult T))
    rw [show negative (halfResult T)= (N ^^ P) from sg]
    cases N <;> cases P <;> rfl
  have zo : z.basis L.one=H := (add.2.1 _ (fun h =>
    BalancedCircuit.flagAway L hn L.one (by simp) (by simp [h]))).trans bo
  have rel := releaseSelectors_run L hn P H z m5 zp zr zl zm zo
  rw [et] at rel
  have tf (q : Wire) (ql : q≠L.lower) (qo : q≠L.one) (qm : q≠L.minus) : t.basis q=z.basis q := by
    rw [rel]
    simp only [writeBit,Function.update_of_ne ql,Function.update_of_ne qo,Function.update_of_ne qm]
  have tl : t.basis L.lower=false := by rw [rel]; simp only [writeBit,
    Function.update_of_ne (show L.lower≠L.minus by tauto),
    Function.update_of_ne (show L.lower≠L.one by tauto),Function.update_self]
  have cleanOne : t.basis L.one=false := by rw [rel]; simp only [writeBit,
    Function.update_of_ne (show L.one≠L.minus by tauto),Function.update_self]
  have tm : t.basis L.minus=false := by rw [rel]; simp [writeBit]
  have tv : regValue L.r t.basis=encodeWord 256 (biasedValue R) := by
    apply Eq.trans _ zv
    apply regValue_congr
    intro q hq
    exact tf q (dataflag q (by simp [hq]) _ (by simp))
      (dataflag q (by simp [hq]) _ (by simp)) (dataflag q (by simp [hq]) _ (by simp))
  have ps := prepareSign_biased L hw hn R rc t m6 tv tl
  rw [ed] at ps
  have fl := flipBias_value L hw hn R rc d m7 ps.2.1
  rw [ee] at fl
  have ef (q : Wire) (hq : q∉L.r) : e.basis q=d.basis q := by
    rw [←ee]
    have mem : L.rtail.getD 253 0∈L.r := by
      have sp := low_split L hw
      have ml : L.rtail.getD 253 0∈L.low := by rw [←sp]; simp
      exact List.mem_append_left _ ml
    simp only [flipBias,run,writeBit,Function.update_of_ne (show q≠L.rtail.getD 253 0 from fun e => hq (e ▸ mem))]
  have toR (f : Wire) (hf : f∈[L.one,L.minus,L.lower]) : f∉L.r := by
    intro h
    exact BalancedCircuit.flagAway L hn f (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto) (by simp [h])
  have phase : e.phase=v.phase := by
    have ephase : e.phase=d.phase := by rw [←ee]; rfl
    have tphase : t.phase=z.phase := by rw [rel]
    have bphase : b.phase=a.phase := by rw [bp]
    have wphase : w.phase=v.phase := by rw [wp]
    exact ephase.trans (ps.1.trans (tphase.trans
      (add.1.trans (bphase.trans (rot.1.trans wphase)))))
  refine ⟨phase,fl,?_,?_,?_,?_⟩
  · exact (ef _ (toR _ (by simp))).trans ps.2.2.1
  · exact (ef _ (toR _ (by simp))).trans ((ps.2.2.2 _ (toR _ (by simp)) (by tauto)).trans cleanOne)
  · exact (ef _ (toR _ (by simp))).trans ((ps.2.2.2 _ (toR _ (by simp)) (by tauto)).trans tm)
  · intro q hqr hql hqm
    have qo : q≠L.one := fun eq => hqr (by simp [BalancedCircuit.rawTarget,eq])
    have qr : q∉L.r := fun h => hqr (by simp [BalancedCircuit.rawTarget,h])
    have q0 : q≠L.r0 := fun eq => hqr (by simp [BalancedCircuit.rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,eq])
    exact (ef q qr).trans ((ps.2.2.2 q qr hql).trans ((tf q hql qo hqm).trans
      ((add.2.1 q qr).trans ((bf q qo).trans ((af q hqr).trans (wf q hql hqm q0))))))


end ECDSAAdd.Entrant.ShortBiasedFold
end

-- ===== Root verified Short kernel Prefix =====
section
namespace ECDSAAdd.Entrant.ShortBiasedFold
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.BalancedField ECDSAAdd.Entrant.BiasedCircuit
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def remainder (L : Layout) : Program :=
  prepareFold L++(rotateRight (BalancedCircuit.rawTarget L)++(signView L++(shortFold L++
    (releaseSelectors L++(BalancedCleanup.prepareSign L.toLayout++flipBias L)))))

theorem remainder_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (v : State) (m : List Bool)
    (hv : regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T)
    (hp : v.basis L.parity=originalParity T) (ho : v.basis L.one=decide (T<0))
    (h0 : v.basis L.r0=originalParity T) (hl : v.basis L.lower=false)
    (hm : v.basis L.minus=false) (hc : ∀q∈L.carry,v.basis q=false) :
    let e := run (remainder L) m v
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q) := by
  let P : State → State → Prop := fun v e =>
    regValue (BalancedCircuit.rawTarget L) v.basis=encodeWord 257 T →
    v.basis L.parity=originalParity T → v.basis L.one=decide (T<0) →
    v.basis L.r0=originalParity T → v.basis L.lower=false → v.basis L.minus=false →
    (∀q∈L.carry,v.basis q=false) →
    e.phase=v.phase ∧ regValue L.r e.basis=encodeWord 255 (normalizedR (halfResult T)) ∧
    e.basis L.lower=negative (halfResult T) ∧ e.basis L.one=false ∧ e.basis L.minus=false ∧
    (∀q,q∉BalancedCircuit.rawTarget L → q≠L.lower → q≠L.minus → e.basis q=v.basis q)
  have run7 := skywalkRunSeven (prepareFold L) (rotateRight (BalancedCircuit.rawTarget L))
    (signView L) (shortFold L) (releaseSelectors L) (BalancedCleanup.prepareSign L.toLayout) (flipBias L) P
    (by
      intro v w a b z t d e m1 m2 m3 m4 m5 m6 m7 ew ea eb ez et ed ee hv hp ho h0 hl hm hc
      exact foldStates L hw hn T ht v w a b z t d e m1 m2 m3 m4 m5 m6 m7
        hv hp ho h0 hl hm hc ew ea eb ez et ed ee) v m
  exact run7 hv hp ho h0 hl hm hc


def biasedPrefix (L : Layout) : Program :=
  BalancedCircuit.seedViews L++(BalancedCircuit.rawAdd L++remainder L)

theorem prefixPost (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    PrefixPost L (halfResult (rawSum B X Y)) (originalParity (rawSum B X Y)) s
      (run (biasedPrefix L) m s) := by
  let T := rawSum B X Y
  let ms := m.drop (measurementCount (BalancedCircuit.rawAdd L))
  generalize eu : run (BalancedCircuit.seedViews L) m s=u
  generalize ev : run (BalancedCircuit.rawAdd L) m u=v
  generalize et : run (remainder L) ms v=t
  have seed := BalancedCircuit.compose_seed_frame L hw hn s m hc
  rw [eu] at seed
  have sv := BalancedCircuit.seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (BalancedCircuit.seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (BalancedCircuit.seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉BalancedCircuit.rawTarget L) : v.basis q=u.basis q := by
    simpa only [ev] using BalancedCircuit.rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉BalancedCircuit.rawTarget L := BalancedCircuit.compose_raw_away L hn q hq
  have vp : v.basis L.parity=originalParity T := by
    exact (rf _ (away _ (by simp))).trans (by simpa only [eu] using BalancedCircuit.seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=decide (T<0) :=
    BalancedCircuit.word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=originalParity T := by
    apply BalancedCircuit.word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := BalancedCircuit.compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [BalancedCircuit.rawTarget]))
    exact (rf q cv.1).trans ((seed.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have vw := BalancedCircuit.word_encoding (BalancedCircuit.rawTarget L) 257
    (BalancedCircuit.widths L hw).2.1 v.basis T sv.2.1
  have rem := remainder_correct L hw hn T (rawSum_bounds B X Y hx hy) v ms vw vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (fun q hq => vz q (by simp [hq]))
  rw [et] at rem
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have actual : run (biasedPrefix L) m s=t := by
    change run (BalancedCircuit.seedViews L++(BalancedCircuit.rawAdd L++remainder L)) m s=t
    rw [run_append,run_take,show measurementCount (BalancedCircuit.seedViews L)=0 from rfl,
      List.drop_zero,eu,run_append,run_take,ev,et]
  rw [actual]
  refine ⟨rem.1.trans sv.1,rem.2.1,rem.2.2.1,?_,?_,?_⟩
  · exact (rem.2.2.2.2.2 _ (away _ (by simp)) (by tauto) (by tauto)).trans vp
  · exact (rem.2.2.2.2.2 _ (away _ (by simp)) (by tauto) (by tauto)).trans
      ((rf _ (away _ (by simp))).trans seed.2.1)
  · intro q hqr hql hqp hqg
    by_cases qo : q=L.one
    · subst q
      exact rem.2.2.2.1.trans (hc _ (by simp [BalancedCircuit.work])).symm
    by_cases qm : q=L.minus
    · subst q
      exact rem.2.2.2.2.1.trans (hc _ (by simp [BalancedCircuit.work])).symm
    have raw : q∉BalancedCircuit.rawTarget L := by
      simpa [BalancedCircuit.rawTarget] using And.intro hqr qo
    exact (rem.2.2.2.2.2 q raw hql qm).trans
      ((rf q raw).trans (seed.2.2 q hqg qo hqp))


def program (L : Layout) : Program := biasedPrefix L++BiasedCircuit.cleanupSuffix L

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1021 ∧ measurementCount (program L)=1021 := by
  have old := BiasedCircuit.counts L hw
  have widths := BalancedCleanup.widths L.toLayout hw
  have fa := mappedAdd_counts (BiasedCircuit.biasBits L) L.r (L.carry.take 255) L.minus
    (by simp [BiasedCircuit.biasBits,widths.2.1])
    (by simp [List.length_take,hw.2.2,widths.2.1])
  have short := short_counts L hw
  simp only [BiasedCircuit.program,BiasedCircuit.biasedPrefix,BiasedCircuit.fold,
    toffoliCount_append,measurementCount_append,fa.1,fa.2,widths.2.1] at old
  simp only [program,biasedPrefix,remainder,toffoliCount_append,measurementCount_append,short.1,short.2.1]
  omega

theorem prefix_eq_reference (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (biasedPrefix L) m s=run (referencePrefix L) n s := by
  have a := prefixPost L hw hn B X Y hx hy s m hs hr hyr hc
  have b := referencePost L hw hn B X Y hx hy s n hs hr hyr hc
  apply State.extensionality
  · exact a.phase.trans b.phase.symm
  · funext q
    by_cases qr : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (a.value.trans b.value.symm) q qr
    by_cases ql : q=L.lower
    · subst q; exact a.lower.trans b.lower.symm
    by_cases qp : q=L.parity
    · subst q; exact a.parity.trans b.parity.symm
    by_cases qg : q=L.sourceGuard
    · subst q; exact a.guard.trans b.guard.symm
    exact (a.frame q qr ql qp qg).trans (b.frame q qr ql qp qg).symm

/-- Exact single-bank forward kernel for every input phase and measurement record. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈BalancedCircuit.work L,t.basis q=false) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let k := measurementCount (referencePrefix L)
  let tail := m.drop (measurementCount (biasedPrefix L))
  let n := List.replicate k false++tail
  have eq : run (program L) m s=run (BalancedCircuit.program L) n s := by
    rw [program,reference_program,run_append,run_take,run_append,run_take,
      prefix_eq_reference L hw hn B X Y hx hy s m n hs hr hyr hc]
    have dn : n.drop (measurementCount (referencePrefix L))=tail := by simp [n,k]
    rw [dn]
  rw [eq]
  exact BalancedCircuit.program_correct L hw hn B X Y hx hy s n hs hr hyr hc

end ECDSAAdd.Entrant.ShortBiasedFold
end

-- ===== Root verified Short kernel Inverse =====
section
namespace ECDSAAdd.Entrant.ShortBiasedFold
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.ShortKernelDependencies
set_option maxHeartbeats 200000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem low_sub_mod (n x y : Nat) (xh yh c : Bool) (hx : x<2^n) :
    ((y+2^n*yh.toNat+2^(n+1)-(x+2^n*xh.toNat)-c.toNat)%2^(n+1))%2^n =
      (y+2^n-x-c.toNat)%2^n := by
  rw [Nat.mod_mod_of_dvd _ (show 2^n∣2^(n+1) from ⟨2,by simp [Nat.pow_succ]⟩)]
  have eq : y+2^n*yh.toNat+2^(n+1)-(x+2^n*xh.toNat)-c.toNat =
      (y+2^n-x-c.toNat)+2^n*((if xh then 0 else 1)+yh.toNat) := by
    rw [Nat.pow_succ]
    cases xh <;> cases yh <;> cases c <;> simp [Bool.toNat] <;> omega
  rw [eq,Nat.add_mod]
  simp
theorem full_sub_low (bits : List MappedBit) (b : MappedBit) (ys carry : List Wire)
    (top cin : Wire) (hl : bits.length=ys.length) (hc : carry.length=ys.length)
    (hn : (cin::((ys++[top])++carry)).Nodup)
    (hs : ∀q∈mappedWires (bits++[b]),q∉cin::((ys++[top])++carry))
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false) :
    regValue ys (run (mappedSub (bits++[b]) (ys++[top]) carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-mappedValue bits s.basis-(s.basis cin).toNat)%2^ys.length := by
  have add := BalancedInverse.mappedSub_any_correct (bits++[b]) (ys++[top]) carry cin hn hs
    (by simp [hl]) (by simp [hc]) s m clean
  have h := congrArg (fun v : Nat => v%2^ys.length) add.2.2
  dsimp only at h
  rw [reg_low_mod] at h
  rw [mappedValue_append,regValue_append,hl,List.length_append,List.length_singleton] at h
  have small : mappedValue bits s.basis<2^ys.length := by
    simpa only [hl] using mappedValue_lt bits s.basis
  rw [show regValue [top] s.basis=(s.basis top).toNat by
    cases e : s.basis top <;> simp [regValue,e],
    show mappedValue [b] s.basis=(b.value s.basis).toNat by simp [mappedValue]] at h
  change regValue ys (run (mappedSub (bits++[b]) (ys++[top]) carry cin) m s).basis =
    ((regValue ys s.basis+2^ys.length*(s.basis top).toNat+2^(ys.length+1)-
      (mappedValue bits s.basis+2^ys.length*(b.value s.basis).toNat)-(s.basis cin).toNat)%
      2^(ys.length+1))%2^ys.length at h
  rw [low_sub_mod ys.length (mappedValue bits s.basis) (regValue ys s.basis)
    (b.value s.basis) (s.basis top) (s.basis cin) small] at h
  exact h


theorem full_sub_eq_short (bits : List MappedBit) (b : MappedBit)
    (ys carry small : List Wire) (top cin control : Wire)
    (hl : bits.length=ys.length) (hc : carry.length=ys.length)
    (hsmall : small.length+1=ys.length)
    (hn : (cin::((ys++[top])++carry)).Nodup)
    (hs : ∀q∈mappedWires (bits++[b]),q∉cin::((ys++[top])++carry))
    (hn' : (cin::(ys++small)).Nodup)
    (hs' : ∀q∈mappedWires bits,q∉cin::(ys++small))
    (htop : top∉ys) (hcontrol : control∉ys)
    (s : State) (m n : List Bool)
    (clean : ∀q∈carry,s.basis q=false) (clean' : ∀q∈small,s.basis q=false)
    (high : (run (mappedSub (bits++[b]) (ys++[top]) carry cin) m s).basis top =
      (s.basis top ^^ s.basis control)) :
    run (mappedSub (bits++[b]) (ys++[top]) carry cin) m s =
    run (mappedSub bits ys small cin ++ [.CX control top]) n s := by
  have full := BalancedInverse.mappedSub_any_correct (bits++[b]) (ys++[top]) carry cin hn hs
    (by simp [hl]) (by simp [hc]) s m clean
  have low := full_sub_low bits b ys carry top cin hl hc hn hs s m clean
  have narrow := BalancedInverse.mappedSub_any_correct bits ys small cin hn' hs' hl hsmall s n clean'
  rw [run_append]
  simp only [run_take,run]
  generalize he : run (mappedSub (bits++[b]) (ys++[top]) carry cin) m s = v at full low high ⊢
  generalize hf : run (mappedSub bits ys small cin) n s = u at narrow ⊢
  refine State.extensionality v ⟨u.phase,writeBit u.basis top (u.basis top ^^ u.basis control)⟩
    (full.1.trans narrow.1.symm) ?_
  funext q
  by_cases qt : q=top
  · subst q
    change v.basis top = (writeBit u.basis top (u.basis top ^^ u.basis control)) top
    rw [writeBit,Function.update_self,narrow.2.1 top htop,narrow.2.1 control hcontrol]
    exact high
  · simp only [writeBit,Function.update_of_ne qt]
    by_cases qy : q∈ys
    · exact (regValue_eq_iff ys v.basis u.basis).mp (low.trans narrow.2.2.symm) q qy
    · exact (full.2.1 q (by simp [qy,qt])).trans (narrow.2.1 q qy).symm
theorem biased_unfold_layout_eq (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*Arithmetic.BalancedField.q)≤T ∧ T≤2*Arithmetic.BalancedField.q)
    (s : State) (m n : List Bool)
    (hv : regValue L.r s.basis=Arithmetic.BalancedField.encodeWord 256 (BiasedInverse.biased (Arithmetic.BalancedField.halfResult T)))
    (hl : s.basis L.lower=decide (T<0))
    (ho : s.basis L.one=Arithmetic.BalancedField.negative (Arithmetic.BalancedField.halfResult T))
    (hp : s.basis L.parity=Arithmetic.BalancedField.originalParity T)
    (hm : s.basis L.minus=(Arithmetic.BalancedField.originalParity T && decide (T<0)))
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (BiasedInverse.unfoldBias L) m s=run (shortUnfold L) n s := by
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have fullND : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have smallND : (L.minus::(L.low++L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have fullSrc : ∀q∈mappedWires (BiasedCircuit.biasBits L),q∉L.minus::(L.r++L.carry.take 255) := by
    intro q hq hmem
    have src := BiasedCircuit.biasBits_sources L q hq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have smallSrc : ∀q∈mappedWires (lowBits L),q∉L.minus::(L.low++L.carry.take 254) := by
    intro q hq hmem
    have fullq : q∈mappedWires (BiasedCircuit.biasBits L) := by
      rw [biasBits_split]
      simp only [mappedWires,List.flatMap_append,List.mem_append]
      exact Or.inl hq
    have src := BiasedCircuit.biasBits_sources L q fullq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [BalancedCleanup.Layout.r,he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have topAway : L.rmsb∉L.low := by
    intro bad
    have data := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) L.rmsb
    have cnt := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at data
    simp at data
    omega
  have parityAway : L.parity∉L.low := by
    intro bad
    exact BalancedCircuit.flagAway L hn L.parity (by simp) (by simp [BalancedCleanup.Layout.r,bad])
  have sub := BiasedInverse.unfoldBias_correct L hw hn T ht s m hl ho hm hv clean
  have out := BiasedInverse.half_msb L hw T ht _ sub.2.1
  have inp := BiasedInverse.biased_msb L hw _ (Arithmetic.BalancedField.halfResult_spec T ht).1 s.basis hv
  have high : (run (BiasedInverse.unfoldBias L) m s).basis L.rmsb =
      (s.basis L.rmsb ^^ s.basis L.parity) := by
    rw [out,inp,hp,Arithmetic.BalancedField.negative,Arithmetic.BalancedField.halfResult_sign T ht]
    cases hN : decide (T<0) <;> cases hP : Arithmetic.BalancedField.originalParity T <;> rfl
  have oldShape : BiasedInverse.unfoldBias L = mappedSub
      (lowBits L ++ [{wire:=some L.one,flip:=false}]) (L.low++[L.rmsb])
      (L.carry.take 255) L.minus := by
    change mappedSub (BiasedCircuit.biasBits L) L.r (L.carry.take 255) L.minus=_
    rw [biasBits_split]; rfl
  have widths := BalancedCleanup.widths L.toLayout hw
  rw [oldShape] at high ⊢
  exact full_sub_eq_short (lowBits L) {wire:=some L.one,flip:=false} L.low
    (L.carry.take 255) (L.carry.take 254) L.rmsb L.minus L.parity
    (by rw [lowBits_length,widths.1])
    (by simp [List.length_take,hw.2.2,widths.1])
    (by simp [List.length_take,hw.2.2,widths.1])
    fullND (by simpa only [←biasBits_split] using fullSrc) smallND smallSrc topAway parityAway s m n
    (fun q hq => clean q (List.mem_of_mem_take hq))
    (fun q hq => clean q (List.mem_of_mem_take hq)) high
end ECDSAAdd.Entrant.ShortBiasedFold
end

-- ===== Root verified Short kernel InverseProgram =====
section
namespace ECDSAAdd.Entrant.ShortBiasedInverse
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.BalancedCircuit ECDSAAdd.Arithmetic.BalancedField
open ECDSAAdd.Entrant.BiasedInverse ECDSAAdd.Entrant.ShortBiasedFold
abbrev Layout := ECDSAAdd.Arithmetic.BalancedCircuit.Layout
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def unfoldBias (L : Layout) : Program := shortUnfold L

def restoreRaw (L : Layout) : Program :=
  selectors L ++ unfoldBias L ++ release L ++ rotateLeft (rawTarget L) ++ [.CX L.parity L.r0]

def program (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard] ++ recoverPrefix L ++ unbiasView L ++
  restoreRaw L ++ BalancedInverse.rawSubtract L ++ (seedViews L).reverse

theorem unfoldBias_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hl : s.basis L.lower=decide (T<0)) (ho : s.basis L.one=negative (halfResult T))
    (hm : s.basis L.minus=(originalParity T && decide (T<0)))
    (hR : regValue L.r s.basis=encodeWord 256 (biased (halfResult T)))
    (hc : ∀a∈L.carry,s.basis a=false) :
    let t := run (unfoldBias L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (T/2) ∧
    ∀a,a∉L.r → t.basis a=s.basis a := by
  have eq := biased_unfold_layout_eq L hw hn T ht s m m hR hl ho hp hm hc
  rw [unfoldBias,←eq]
  exact BiasedInverse.unfoldBias_correct L hw hn T ht s m hl ho hm hR hc

theorem restoreRaw_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hR : regValue L.r s.basis=encodeWord 256 (biased (halfResult T)))
    (hl : s.basis L.lower=false) (ho : s.basis L.one=false) (hm : s.basis L.minus=false)
    (hc : ∀a∈L.carry,s.basis a=false) :
    let t := run (restoreRaw L) m s
    t.phase=s.phase ∧ regValue (rawTarget L) t.basis=encodeWord 257 T ∧
    t.basis L.lower=false ∧ t.basis L.minus=false ∧
    ∀a,a∉rawTarget L → a≠L.lower → a≠L.minus → t.basis a=s.basis a := by
  let P := originalParity T
  let N := decide (T<0)
  let u : State := ⟨s.phase,writeBit (writeBit (writeBit s.basis L.lower N)
    L.one (N ^^ P)) L.minus (P && N)⟩
  let v := run (unfoldBias L) m u
  let m1 := m.drop (measurementCount (unfoldBias L))
  let z := run (release L) m1 v
  let m2 := m1.drop 1
  let rot := run (rotateLeft (rawTarget L)) m2 z
  let out := run [.CX L.parity L.r0] m2 rot
  have sd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at sd
  have lm : L.lower≠L.minus := by tauto
  have om : L.one≠L.minus := by tauto
  have ol : L.one≠L.lower := by tauto
  have pl : L.parity≠L.lower := by tauto
  have po : L.parity≠L.one := by tauto
  have pm : L.parity≠L.minus := by tauto
  have r0p : L.r0≠L.parity := by tauto
  have r0o : L.r0≠L.one := by tauto
  have flags (a : Wire) (ha : a∈L.r++L.y++L.carry)
      (f : Wire) (hf : f∈[L.lower,L.one,L.minus]) : a≠f := by
    intro e
    exact flagAway L hn f (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto)
      (e ▸ ha)
  have uf (a : Wire) (al : a≠L.lower) (ao : a≠L.one) (am : a≠L.minus) : u.basis a=s.basis a := by
    simp [u,writeBit,al,ao,am]
  have uL : u.basis L.lower=N := by simp [u,writeBit,lm,Ne.symm ol]
  have uO : u.basis L.one=(N ^^ P) := by simp [u,writeBit,om]
  have uM : u.basis L.minus=(P && N) := by simp [u,writeBit]
  have uP : u.basis L.parity=P := (uf _ pl po pm).trans hp
  have sign := biased_msb L hw _ (halfResult_spec T ht).1 s.basis hR
  rw [negative,halfResult_sign T ht] at sign
  have sel : run (selectors L) m s=u := selectors_run L hn P N s m hp sign hl hm ho
  have uR : regValue L.r u.basis=encodeWord 256 (biased (halfResult T)) := by
    apply Eq.trans _ hR
    apply regValue_congr
    intro a ha
    exact uf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))
  have uC : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (uf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))).trans (hc a ha)
  have sub := unfoldBias_correct L hw hn T ht u m uP uL
    (by rw [negative,halfResult_sign T ht]; exact uO) uM uR uC
  have vR : regValue L.r v.basis=encodeWord 256 (T/2) := sub.2.1
  have fa (f : Wire) (hf : f∈[L.lower,L.one,L.minus,L.parity]) : f∉L.r := by
    intro h
    exact flagAway L hn f (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢; tauto)
      (by simp [h])
  have rel : z=⟨v.phase,writeBit (writeBit (writeBit v.basis L.lower false)
      L.one false) L.minus false⟩ :=
    release_run L hn P N v m1 ((sub.2.2 _ (fa _ (by simp))).trans uP)
      (half_msb L hw T ht v.basis vR)
      ((sub.2.2 _ (fa _ (by simp))).trans uL)
      ((sub.2.2 _ (fa _ (by simp))).trans uM)
      ((sub.2.2 _ (fa _ (by simp))).trans uO)
  have zf (a : Wire) (al : a≠L.lower) (ao : a≠L.one) (am : a≠L.minus) : z.basis a=v.basis a := by
    rw [rel]; simp [writeBit,al,ao,am]
  have zL : z.basis L.lower=false := by rw [rel]; simp [writeBit,lm,Ne.symm ol]
  have zM : z.basis L.minus=false := by rw [rel]; simp [writeBit]
  have zO : z.basis L.one=false := by rw [rel]; simp [writeBit,om]
  have zR : regValue L.r z.basis=encodeWord 256 (T/2) := by
    apply Eq.trans _ vR
    apply regValue_congr
    intro a ha
    exact zf a (flags a (by simp [ha]) _ (by simp))
      (flags a (by simp [ha]) _ (by simp)) (flags a (by simp [ha]) _ (by simp))
  have zP : z.basis L.parity=P := (zf _ pl po pm).trans ((sub.2.2 _ (fa _ (by simp))).trans uP)
  have rp := BalancedInverse.rotate_unfold L hw hn (T/2) z m2 zO zR
  have away (a : Wire) (ha : a∉L.r) (ao : a≠L.one) : a∉rawTarget L := by
    simp [rawTarget,ha,ao]
  have pr : rot.basis L.parity=P := (rp.2.2.2 _ (away _ (fa _ (by simp)) po)).trans zP
  have outV : regValue (rawTarget L) out.basis=encodeWord 257 T := by
    have shape : rawTarget L=L.r0::foldTarget L := by
      simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
    have r0Away : L.r0∉foldTarget L := by
      have nd := rawTargetND L hn
      rw [shape] at nd
      exact (List.nodup_cons.mp nd).1
    have tail : regValue (foldTarget L) out.basis=encodeWord 256 (T/2) := by
      apply Eq.trans _ rp.2.2.1
      apply regValue_congr
      intro a ha
      change out.basis a=rot.basis a
      simp [out,run,writeBit,show a≠L.r0 from fun e => r0Away (e ▸ ha)]
    rw [shape]
    change (if out.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) out.basis=_
    have r0rot : rot.basis L.r0=false := rp.2.1
    have low : out.basis L.r0=P := by simp [out,run,writeBit,r0rot,pr]
    rw [low,tail]
    have he := half_encoding T ht
    cases hp' : P <;> simpa [P,hp',Nat.add_comm] using he
  have actual : run (restoreRaw L) m s=out := by
    simp only [restoreRaw,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount (selectors L)=0 from rfl,List.drop_zero]
    rw [sel,run_append,run_take]
    change run (release L ++ (rotateLeft (rawTarget L) ++ [.CX L.parity L.r0])) m1 v=out
    rw [run_append,run_take]
    simp only [show measurementCount (release L)=1 from rfl]
    change run (rotateLeft (rawTarget L) ++ [.CX L.parity L.r0]) m2 z=out
    rw [run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero]
  rw [actual]
  have of (a : Wire) (ar : a∉rawTarget L) : out.basis a=z.basis a := by
    have ar0 : a≠L.r0 := fun e => ar (by simp [rawTarget,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,e])
    simp only [out,run,writeBit,Function.update_of_ne ar0]
    exact rp.2.2.2 a ar
  refine ⟨?_,outV,?_,?_,?_⟩
  · change rot.phase=s.phase
    exact rp.1.trans ((congrArg State.phase rel).trans sub.1)
  · exact (of _ (away _ (fa _ (by simp)) (Ne.symm ol))).trans zL
  · exact (of _ (away _ (fa _ (by simp)) (Ne.symm om))).trans zM
  · intro a ar al am
    have ar' : a∉L.r := fun h => ar (by simp [rawTarget,h])
    have ao : a≠L.one := fun e => ar (by simp [rawTarget,e])
    exact (of a ar).trans ((zf a al ao am).trans ((sub.2.2 a ar').trans (uf a al ao am)))

section KernelSemantics
attribute [local irreducible] run measurementCount
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀a∈work L,s.basis a=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (BalancedInverse.result B R Y) ∧
    (∀a∈work L,t.basis a=false) ∧ (∀a,a∉L.r → t.basis a=s.basis a) := by
  let X := BalancedInverse.result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let u0 := run [.CX L.ymsb L.sourceGuard] m s
  let u1 := run (recoverPrefix L) m u0
  let m1 := m.drop (measurementCount (recoverPrefix L))
  let u2 := run (unbiasView L) m1 u1
  let m2 := m1.drop (measurementCount (unbiasView L))
  let u3 := run (restoreRaw L) m2 u2
  let m3 := m2.drop (measurementCount (restoreRaw L))
  let u4 := run (BalancedInverse.rawSubtract L) m3 u3
  let m4 := m3.drop (measurementCount (BalancedInverse.rawSubtract L))
  let out := run (seedViews L).reverse m4 u4
  have hx : Centered X := BalancedInverse.result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := BalancedInverse.result_half B R Y hr hy
  have par : decide (q < |2*R-signedY B Y|)=P := BalancedInverse.result_parity B R Y hr hy
  have w := BalancedCleanup.widths L.toLayout hw
  have rwid := BalancedCircuit.widths L hw
  have cnd : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h0_7r := Ne.symm h0_7
  have h0_8r := Ne.symm h0_8
  have h0_9r := Ne.symm h0_9
  have h0_10r := Ne.symm h0_10
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h1_7r := Ne.symm h1_7
  have h1_8r := Ne.symm h1_8
  have h1_9r := Ne.symm h1_9
  have h1_10r := Ne.symm h1_10
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h2_7r := Ne.symm h2_7
  have h2_8r := Ne.symm h2_8
  have h2_9r := Ne.symm h2_9
  have h2_10r := Ne.symm h2_10
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h3_7r := Ne.symm h3_7
  have h3_8r := Ne.symm h3_8
  have h3_9r := Ne.symm h3_9
  have h3_10r := Ne.symm h3_10
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h4_7r := Ne.symm h4_7
  have h4_8r := Ne.symm h4_8
  have h4_9r := Ne.symm h4_9
  have h4_10r := Ne.symm h4_10
  have h5_6r := Ne.symm h5_6
  have h5_7r := Ne.symm h5_7
  have h5_8r := Ne.symm h5_8
  have h5_9r := Ne.symm h5_9
  have h5_10r := Ne.symm h5_10
  have h6_7r := Ne.symm h6_7
  have h6_8r := Ne.symm h6_8
  have h6_9r := Ne.symm h6_9
  have h6_10r := Ne.symm h6_10
  have h7_8r := Ne.symm h7_8
  have h7_9r := Ne.symm h7_9
  have h7_10r := Ne.symm h7_10
  have h8_9r := Ne.symm h8_9
  have h8_10r := Ne.symm h8_10
  have h9_10r := Ne.symm h9_10
  have flagR (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      f∉L.r := fun h => flagAway L hn f hf (by simp [h])
  have away (a : Wire)
      (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      a∉rawTarget L := compose_raw_away L hn a ha
  have neq (a : Wire) (ha : a∈L.y++L.carry)
      (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
    by
      intro e
      apply flagAway L hn f hf
      subst a
      simp only [List.mem_append] at ha ⊢
      tauto
  have nr (a : Wire) (ha : a∈L.y++L.carry) : a∉L.r := by
    have d := (List.nodup_append'.mp (allND L hn)).2.1
    have dn : (L.r++(L.y++L.carry)).Nodup := by
      simpa only [List.append_assoc] using d
    exact fun h => List.disjoint_left.mp (List.nodup_append'.mp dn).2.2 h ha
  have f0 (a : Wire) (ha : a≠L.sourceGuard) : u0.basis a=s.basis a := by
    simp [u0,run,writeBit,ha]
  have g0 : u0.basis L.sourceGuard=s.basis L.ymsb := by
    simp [u0,run,writeBit,hc L.sourceGuard (by simp [work])]
  have r0 : regValue L.r u0.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 w.2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => f0 a
      (fun e => flagR L.sourceGuard (by simp) (e ▸ ha)))
  have y0 : regValue L.y u0.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 w.2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => f0 a (neq a (by simp [ha]) _ (by simp)))
  have z0 (a : Wire) (ha : a∈work L) (hg : a≠L.sourceGuard) : u0.basis a=false :=
    (f0 a hg).trans (hc a ha)
  have pre := recoverPrefix_correct L hw cnd R Y B hr hy u0 m r0 y0
    ((f0 _ (by assumption)).trans hs) (z0 _ (by simp [work]) (by assumption))
    (z0 _ (by simp [work]) (by assumption))
    (fun a ha => z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp)))
  have p1 : u1.basis L.parity=P := by
    rw [pre.2.2.2.1,z0 _ (by simp [work]) (by assumption),par]
    exact Bool.false_xor P
  have view := unbiasView_correct L hw cnd R hr u1 m1 pre.2.1 pre.2.2.1
  have f2 (a : Wire) (ar : a∉L.r) (al : a≠L.lower) (ap : a≠L.parity) : u2.basis a=u0.basis a :=
    (view.2.2.2 a ar al).trans (pre.2.2.2.2 a ar al ap)
  have p2 : u2.basis L.parity=P :=
    (view.2.2.2 _ (flagR _ (by simp)) (by assumption)).trans p1
  have r2 : regValue L.r u2.basis=encodeWord 256 (biased (halfResult T)) := by
    rw [half]; exact view.2.1
  have restore := restoreRaw_correct L hw hn T ht u2 m2 p2 r2 view.2.2.1
    ((f2 _ (flagR _ (by simp)) (by assumption) (by assumption)).trans (z0 _ (by simp [work]) (by assumption)))
    ((f2 _ (flagR _ (by simp)) (by assumption) (by assumption)).trans (z0 _ (by simp [work]) (by assumption)))
    (fun a ha => (f2 a (nr a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp))).trans
      (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp))))
  have f3 (a : Wire) (ar : a∉rawTarget L) (al : a≠L.lower) (am : a≠L.minus)
      (ap : a≠L.parity) : u3.basis a=u0.basis a :=
    (restore.2.2.2.2 a ar al am).trans
      (f2 a (fun h => ar (by simp [rawTarget,h])) al ap)
  have p3 : u3.basis L.parity=P :=
    (restore.2.2.2.2 _ (away _ (by simp)) (by assumption) (by assumption)).trans p2
  have y3 : signedRegValue L.y u3.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    exact (f3 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
      (f0 a (neq a (by simp [ha]) _ (by simp)))
  have g3 : u3.basis L.sourceGuard=u3.basis L.ymsb := by
    have g := (f3 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g0
    have y := (f3 L.ymsb (away _ (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f0 _ (by assumption))
    exact g.trans y.symm
  have src3 : signedRegValue (rawSource L) u3.basis=Y :=
    (signed_extension L.ylow L.ymsb L.sourceGuard u3.basis g3).trans y3
  have raw3 : signedRegValue (rawTarget L) u3.basis=T := by
    unfold signedRegValue
    rw [rwid.2.1,restore.2.1]
    apply decode_encodeWord 257 (by norm_num)
    have c := constants
    norm_num at ⊢
    omega
  have carry3 : regValue L.carry u3.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    exact (f3 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
      (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
      (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp)))
  have sign3 : u3.basis L.sign=B :=
    (f3 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans ((f0 _ (by assumption)).trans hs)
  have sub := BalancedInverse.rawSubtract_signed L hw hn B X Y hx u3 m3 sign3 src3 raw3 carry3
  have y4 : signedRegValue L.y u4.basis=Y := by
    apply Eq.trans _ y3
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => sub.2.2 a (away a (by simp [ha])))
  have g4 : u4.basis L.sourceGuard=u4.basis L.ymsb :=
    (sub.2.2 _ (away _ (by simp))).trans (g3.trans
      (sub.2.2 _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p4 : u4.basis L.parity=P := (sub.2.2 _ (away _ (by simp))).trans p3
  have seed := BalancedInverse.unseed_packet L hw hn B X Y hx u4 m4 sub.2.1 y4 g4 p4
  have f4 (a : Wire) (ar : a∉rawTarget L) (al : a≠L.lower) (am : a≠L.minus)
      (ap : a≠L.parity) : u4.basis a=u0.basis a := (sub.2.2 a ar).trans (f3 a ar al am ap)
  have clean : ∀a∈work L,out.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact seed.2.1
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((f4 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          (z0 _ (by simp [work]) (by assumption)))
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((sub.2.2 _ (away _ (by simp))).trans restore.2.2.2.1)
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((f4 _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          (z0 _ (by simp [work]) (by assumption)))
    · exact seed.2.2.2.1
    · exact (seed.2.2.2.2 _ (by assumption) (by assumption) (by assumption)).trans
        ((sub.2.2 _ (away _ (by simp))).trans restore.2.2.1)
    · exact seed.2.2.1
    · exact (seed.2.2.2.2 a (neq a (by simp [ha]) _ (by simp))
        (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
        ((f4 a (away a (by simp [ha])) (neq a (by simp [ha]) _ (by simp))
          (neq a (by simp [ha]) _ (by simp)) (neq a (by simp [ha]) _ (by simp))).trans
          (z0 a (by simp [work,ha]) (neq a (by simp [ha]) _ (by simp))))
  have frame : ∀a,a∉L.r → out.basis a=s.basis a := by
    intro a ar
    by_cases aw : a∈work L
    · exact (clean a aw).trans (hc a aw).symm
    · have ne (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus]) : a≠f := by
        intro e
        apply aw
        subst a
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        tauto
      have rawA : a∉rawTarget L := by simp [rawTarget,ar,ne L.one (by simp)]
      exact (seed.2.2.2.2 a (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))).trans
        ((f4 a rawA (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))).trans
          (f0 a (ne _ (by simp))))
  have value : regValue L.r out.basis=encodeWord 256 X := by
    have corr := BalancedInverse.unseed_correlations L hw B X Y hx u4 sub.2.1 y4 g4 p4
    have narrow : signedRegValue L.r u4.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u4.basis corr.1).symm.trans sub.2.1
    apply Eq.trans _ (word_encoding L.r 256 w.2.1 u4.basis X narrow)
    apply regValue_congr
    intro a ha
    have ne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagR f hf (e ▸ ha)
    exact seed.2.2.2.2 a (ne _ (by simp)) (ne _ (by simp)) (ne _ (by simp))
  have actual : run (program L) m s=out := by
    simp only [program,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from by simp only [measurementCount],List.drop_zero]
    change run (recoverPrefix L ++ (unbiasView L ++ (restoreRaw L ++
      (BalancedInverse.rawSubtract L ++ (seedViews L).reverse)))) m u0=out
    rw [run_append,run_take]
    change run (unbiasView L ++ (restoreRaw L ++
      (BalancedInverse.rawSubtract L ++ (seedViews L).reverse))) m1 u1=out
    rw [run_append,run_take]
    change run (restoreRaw L ++ (BalancedInverse.rawSubtract L ++ (seedViews L).reverse)) m2 u2=out
    rw [run_append,run_take]
    change run (BalancedInverse.rawSubtract L ++ (seedViews L).reverse) m3 u3=out
    rw [run_append,run_take]
  rw [actual]
  have ph0 : u0.phase=s.phase := by simp [u0,run]
  exact ⟨seed.1.trans (sub.1.trans (restore.1.trans (view.1.trans (pre.1.trans ph0)))),value,clean,frame⟩

/-- Whole-state interchangeability permits independent measurement tapes. -/
theorem kernel_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀a∈work L,s.basis a=false) :
    run (program L) m s=run (BalancedInverse.program L) n s := by
  have fresh := program_correct L hw hn B R Y hr hy s m hs hR hY hc
  have old := BalancedInverse.program_correct L hw hn B R Y hr hy s n hs hR hY hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext a
    by_cases ha : a∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) a ha
    · exact (fresh.2.2.2 a ha).trans (old.2.2.2 a ha).symm

end KernelSemantics

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=1021 ∧ measurementCount (program L)=1021 := by
  have old := BiasedInverse.counts L hw
  have widths := BalancedCleanup.widths L.toLayout hw
  have fa := mappedSub_counts (BiasedInverse.biasBits L) L.r (L.carry.take 255) L.minus
    (by simp [BiasedInverse.biasBits,widths.2.1])
    (by simp [List.length_take,hw.2.2,widths.2.1])
  have short := short_counts L hw
  simp only [BiasedInverse.program,BiasedInverse.restoreRaw,BiasedInverse.unfoldBias,
    toffoliCount_append,measurementCount_append,fa.1,fa.2,widths.2.1] at old
  simp only [program,restoreRaw,unfoldBias,toffoliCount_append,measurementCount_append,short.2.2.1,short.2.2.2]
  omega

end ECDSAAdd.Entrant.ShortBiasedInverse
end

-- ===== Root verified Short kernel Properties =====
section
namespace ECDSAAdd.Entrant.ShortBiasedProperties
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.ShortKernelDependencies
abbrev Layout := BalancedCircuit.Layout
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private theorem mapped_support (L : Layout) (P : Program)
    (bound : wires P ⊆ (mappedWires (ShortBiasedFold.lowBits L)++L.low++L.carry.take 254++[L.minus]).toFinset) :
    wires P ⊆ L.wires.toFinset := by
  have member (a : Wire) : a∈L.wires.toFinset ↔
      a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      a∈L.rtail ∨ a∈L.ylow ∨ a∈L.carry := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  intro a ha
  have h := bound ha
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
  rcases h with src|lo|cy|last
  · have full : a∈mappedWires (BiasedCircuit.biasBits L) := by
      rw [ShortBiasedFold.biasBits_split]
      simp only [mappedWires,List.flatMap_append,List.mem_append]
      exact Or.inl src
    rcases BiasedCircuit.biasBits_sources L a full with rfl|rfl <;> simp [member]
  · simp only [BalancedCleanup.Layout.low,List.mem_cons] at lo
    simp only [member,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · exact (member a).mpr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_take cy))))
  · simp [member,last]

private theorem cx_support (L : Layout) : wires [.CX L.parity L.rmsb]⊆L.wires.toFinset := by
  intro q hq
  have eq : q=L.parity ∨ q=L.rmsb := by simpa [wires,Instr.wires] using hq
  rcases eq with rfl|rfl <;> simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]

theorem short_support (L : Layout) :
    wires (ShortBiasedFold.shortFold L) ⊆ L.wires.toFinset ∧
    wires (ShortBiasedFold.shortUnfold L) ⊆ L.wires.toFinset := by
  constructor
  · simp only [ShortBiasedFold.shortFold,wires_append,Finset.union_subset_iff]
    exact ⟨mapped_support L _ (mappedAdd_wires_subset _ _ _ _),cx_support L⟩
  · simp only [ShortBiasedFold.shortUnfold,wires_append,Finset.union_subset_iff]
    exact ⟨mapped_support L _ (mappedSub_wires_subset _ _ _ _),cx_support L⟩

theorem forward_support (L : Layout) (hw : L.Widths) :
    wires (ShortBiasedFold.program L) ⊆ L.wires.toFinset := by
  have old := biasedCircuit_support L hw
  have narrow := (short_support L).1
  simp only [BiasedCircuit.program,BiasedCircuit.biasedPrefix,wires_append,Finset.union_subset_iff] at old
  simp only [ShortBiasedFold.program,ShortBiasedFold.biasedPrefix,ShortBiasedFold.remainder,
    wires_append,Finset.union_subset_iff]
  tauto

theorem inverse_support (L : Layout) (hw : L.Widths) :
    wires (ShortBiasedInverse.program L) ⊆ L.wires.toFinset := by
  have old := BiasedInverse.support L hw
  have narrow := (short_support L).2
  simp only [BiasedInverse.program,BiasedInverse.restoreRaw,wires_append,Finset.union_subset_iff] at old
  simp only [ShortBiasedInverse.program,ShortBiasedInverse.restoreRaw,ShortBiasedInverse.unfoldBias,
    wires_append,Finset.union_subset_iff]
  tauto

/-- Support transport for either swap order around an arbitrary supported kernel. -/
theorem body_support (divide : Bool) (L : Layout) (eff : Wire) (hw : L.Widths)
    (P : Program) (hP : wires P ⊆ L.wires.toFinset) :
    wires (if divide then ([.X L.sign]++P++[.X L.sign])++swapRegisters eff L.r L.y
      else swapRegisters eff L.r L.y++([.X L.sign]++P++[.X L.sign])) ⊆ (eff::L.wires).toFinset := by
  have hk : wires P ⊆ (eff::L.wires).toFinset :=
    hP.trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)
  have hx : wires [.X L.sign] ⊆ (eff::L.wires).toFinset := by
    intro q hq
    have eq : q=L.sign := by simpa [wires,Instr.wires] using hq
    subst q
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have width := BalancedCleanup.widths L.toLayout hw
  have sw : wires (swapRegisters eff L.r L.y) ⊆ (eff::L.wires).toFinset := by
    apply (swapRegisters_wires eff L.r L.y (width.2.1.trans width.2.2.1.symm)).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.not_mem_nil] at hq ⊢
    tauto
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff] <;> tauto

end ECDSAAdd.Entrant.ShortBiasedProperties
end

-- ===== Root verified Short kernel Resources =====
section
namespace ECDSAAdd.Entrant.ShortBiasedResources
open ECDSAAdd.Arithmetic ECDSAAdd.Challenge ECDSAAdd.Baselines
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem biasedCircuit_gateSlots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (ShortBiasedFold.program L) ≤ 24000 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have kw := BalancedCircuit.widths L hw
  have hb : (ShortBiasedFold.lowBits L).length=255 := by exact ShortBiasedFold.lowBits_length L
  have a := addInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L)
    L.carry L.sign
  have r := (rotate_gateSlots_le (BalancedCircuit.rawTarget L)).1
  have l := (rotate_gateSlots_le L.r).2
  have m := mappedAdd_gateSlots_le (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.minus
  have u := literalAdd_gateSlots_le L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.positiveLiteral
  have c := compareLt_gateSlots_le none L.y L.r L.carry L.one L.parity
  rw [kw.1] at a
  rw [kw.2.1] at r
  rw [w.2.1] at l
  rw [hb] at m
  rw [w.1] at u
  rw [w.2.1,w.2.2.1] at c
  simp only [ShortBiasedFold.program,ShortBiasedFold.biasedPrefix,ShortBiasedFold.remainder,BiasedCircuit.cleanupSuffix,
    BiasedCircuit.prepareFold,BiasedCircuit.signView,ShortBiasedFold.shortFold,
    BiasedCircuit.releaseSelectors,BiasedCircuit.flipBias,BalancedCircuit.seedViews,
    BalancedCircuit.rawAdd,BalancedCleanup.prepareSign,BalancedCleanup.prepareCompare,
    BalancedCleanup.unnormalize,gateSlots_append,reverse_gateSlots,signComplement_gateSlots,
    gateSlots_cons,gateSlots_nil,instructionSlots,kw.1,w.2.1,w.2.2.1,List.length_cons,List.length_nil]
  omega

theorem biasedInverse_gateSlots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    Challenge.gateSlots (ShortBiasedInverse.program L) ≤ 25000 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have rw := BalancedCircuit.widths L hw
  have a := literalAdd_gateSlots_le L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.negativeLiteral
  have c := compareLt_gateSlots_le none L.y L.r L.carry L.one L.parity
  have b := mappedSub_gateSlots_le (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.minus
  have s := subInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have r := (rotate_gateSlots_le L.r).2
  have rt := (rotate_gateSlots_le (BalancedCircuit.rawTarget L)).2
  rw [w.1] at a
  rw [w.2.2.1,w.2.1] at c
  have bl : (ShortBiasedFold.lowBits L).length=255 := ShortBiasedFold.lowBits_length L
  rw [bl,w.1] at b
  rw [rw.1,rw.2.1] at s
  rw [w.2.1] at r
  rw [rw.2.1] at rt
  simp only [ShortBiasedInverse.program,BiasedInverse.recoverPrefix,BiasedInverse.unbiasView,
    ShortBiasedInverse.restoreRaw,BiasedInverse.selectors,ShortBiasedInverse.unfoldBias,ShortBiasedFold.shortUnfold,BiasedInverse.release,
    BalancedInverse.rawSubtract,BalancedCleanup.prepareSign,BalancedCleanup.normalize,
    BalancedCleanup.prepareCompare,BalancedCircuit.seedViews,gateSlots_append,reverse_gateSlots,
    signComplement_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,
    w.2.1,w.2.2.1,rw.1,List.length_cons,List.length_nil]
  omega
end ECDSAAdd.Entrant.ShortBiasedResources
end

-- ===== Root verified Short kernel Natural =====
section
namespace ECDSAAdd.Entrant.ShortBiasedNatural
open ECDSAAdd.Arithmetic ECDSAAdd.Entrant.ShortKernelDependencies ECDSAAdd.Arithmetic.FieldRename
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] mappedAdd mappedSub rotateLeft rotateRight signComplement literalConstAdd compareLt addInPlace subInPlace

theorem lowBits_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (ShortBiasedFold.lowBits L).map (mapBit f)=ShortBiasedFold.lowBits (mapCircuit f L) := by
  simp only [ShortBiasedFold.lowBits,List.map_take,bf_biasBits_map]

theorem shortFold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (ShortBiasedFold.shortFold L)=ShortBiasedFold.shortFold (mapCircuit f L) := by
  simp only [ShortBiasedFold.shortFold,rename_append,mappedAdd_natural,lowBits_map,List.map_take,bf_low_map]
  rfl

theorem shortUnfold_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (ShortBiasedFold.shortUnfold L)=ShortBiasedFold.shortUnfold (mapCircuit f L) := by
  simp only [ShortBiasedFold.shortUnfold,rename_append,mappedSub_natural,lowBits_map,List.map_take,bf_low_map]
  rfl

theorem forward_prefix_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hy : L.ylow≠[]) :
    renameProgram f (ShortBiasedFold.biasedPrefix L)=ShortBiasedFold.biasedPrefix (mapCircuit f L) := by
  have pf : renameProgram f (BiasedCircuit.prepareFold L)=
      BiasedCircuit.prepareFold (mapCircuit f L) := by
    simp only [BiasedCircuit.prepareFold,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr]
  have sv : renameProgram f (BiasedCircuit.signView L)=BiasedCircuit.signView (mapCircuit f L) := by
    simp only [BiasedCircuit.signView,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr]
  have rs : renameProgram f (BiasedCircuit.releaseSelectors L)=
      BiasedCircuit.releaseSelectors (mapCircuit f L) := by
    simp only [BiasedCircuit.releaseSelectors,mapCircuit,mapCleanup,renameProgram,
      List.map_cons,List.map_nil,renameInstr,renameCorrection]
  have fd := shortFold_natural f L
  simp only [ShortBiasedFold.biasedPrefix,ShortBiasedFold.remainder,rename_append,seedViews_natural f L hy,rawAdd_natural,
    pf,rotateRight_natural,rawTarget_map,sv,fd,rs,prepareSign_natural,bf_flip_natural f L hw]
  rfl

theorem forward_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    renameProgram f (ShortBiasedFold.program L)=ShortBiasedFold.program (mapCircuit f L) := by
  have hy : L.ylow≠[] := by
    intro e
    have h:=hw.2.1
    rw [e] at h
    simp at h
  simp only [ShortBiasedFold.program,rename_append,forward_prefix_natural f L hw hy,bf_suffix_natural]

theorem restoreRaw_natural (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    renameProgram f (ShortBiasedInverse.restoreRaw L)=ShortBiasedInverse.restoreRaw (mapCircuit f L) := by
  simp only [ShortBiasedInverse.restoreRaw,ShortBiasedInverse.unfoldBias,rename_append,
    bi_selectors_natural,shortUnfold_natural,bi_release_natural,rotateLeft_natural,rawTarget_map]
  rfl

theorem inverse_natural (f : Wire → Wire) (L : BalancedCircuit.Layout)
    (hy : L.ylow≠[]) (hw : L.Widths) :
    renameProgram f (ShortBiasedInverse.program L)=ShortBiasedInverse.program (mapCircuit f L) := by
  simp only [ShortBiasedInverse.program,rename_append,rename_reverse,
    bi_recoverPrefix_natural,bi_unbiasView_natural f L hw,restoreRaw_natural,
    rawSubtract_natural,seedViews_natural f L hy]
  rfl
end ECDSAAdd.Entrant.ShortBiasedNatural
end

-- ===== ECDSAAdd.Submission.Entrant.OneBankPhysical5 =====
section

/-! Structural physicality of the protected one-bank field programs. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneBankPhysical5
open Arithmetic RecordedQuantum BalancedCircuit
attribute [local irreducible] GatePhysical addInPlace subInPlace mappedAdd mappedSub
  literalConstAdd compareLt signComplement rotateLeft rotateRight

private theorem reverse_physical (P : Program) (h : GatePhysical P) : GatePhysical P.reverse := by
  unfold GatePhysical at h ⊢
  intro i hi
  exact h i (List.mem_reverse.mp hi)

private theorem cleanup_scalar (L : BalancedCleanup.Layout) (hn : L.wires.Nodup) :
    [L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [BalancedCleanup.Layout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem cleanup_physical (L : BalancedCleanup.Layout) (_hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (BalancedCleanup.program L) := by
  have nd := cleanup_scalar L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have low := (L.normND hn).tail
  have data := L.dataND hn
  have rND : L.r.Nodup := (List.nodup_append'.mp data).1
  have cmpND : (L.parity :: L.one :: L.y++L.r++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.allND hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have rot := (rotate_physical L.r rND).2
  have sc := signComplement_physical L.lower L.r (fun h => L.flagAway hn L.lower (by simp) (by simp [h]))
  have sy := signComplement_physical L.sign L.y (fun h => L.flagAway hn L.sign (by simp) (by simp [h]))
  have ly := signComplement_physical L.lower L.y (fun h => L.flagAway hn L.lower (by simp) (by simp [h]))
  have seed : GatePhysical [.CX L.rmsb L.lower] := by
    simp [GatePhysical,PhysicalInstr,ProperGate]
    tauto
  have packet : GatePhysical [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0] := by
    simp [GatePhysical,PhysicalInstr,ProperGate]
    tauto
  have xs : GatePhysical [.X L.rmsb,.X L.ymsb] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have x : GatePhysical [.X L.lower] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have a := literalAdd_physical L.low (L.carry.take 254) L.lower L.one BalancedCleanup.negativeLiteral low
  have b := literalAdd_physical L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral low
  have cmp := compareLt_physical none L.y L.r L.carry L.one L.parity cmpND (by simp)
  have ps : GatePhysical (BalancedCleanup.prepareSign L) := by
    simpa only [BalancedCleanup.prepareSign,gatePhysical_append] using And.intro seed sc
  have pc : GatePhysical (BalancedCleanup.prepareCompare L) := by
    simpa only [BalancedCleanup.prepareCompare,gatePhysical_append] using
      And.intro (And.intro (And.intro (And.intro rot packet) sy) ly) xs
  have un : GatePhysical (BalancedCleanup.unnormalize L) := by
    simpa only [BalancedCleanup.unnormalize,gatePhysical_append] using And.intro (And.intro x b) x
  simp only [BalancedCleanup.program,BalancedCleanup.normalize,gatePhysical_append]
  exact ⟨ps,a,pc,cmp,reverse_physical _ pc,un,reverse_physical _ ps⟩

private theorem seed_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (seedViews L) := by
  have nd := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp [seedViews,GatePhysical,PhysicalInstr,ProperGate]
  tauto

private theorem small_physical (L : Layout) (hn : L.wires.Nodup) :
    GatePhysical (prepareFold L) ∧ GatePhysical (releaseSelectors L) ∧
      GatePhysical (BalancedInverse.recoverSelectors L) ∧ GatePhysical (BalancedInverse.undoPreparation L) ∧
      GatePhysical [.CX L.ymsb L.sourceGuard] ∧ GatePhysical [.CX L.minus L.cout] := by
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp [prepareFold,releaseSelectors,BalancedInverse.recoverSelectors,
    BalancedInverse.undoPreparation,GatePhysical,PhysicalInstr,ProperGate]
  tauto

private theorem fold_adder_physical (L : Layout) (hn : L.wires.Nodup) :
    GatePhysical (mappedAdd (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity) := by
  have nd : ([L.plus,L.minus]++(L.parity::(foldTarget L++[L.cout])++L.carry)).Nodup := by
    simpa only [List.cons_append,List.nil_append,List.append_assoc] using foldND L hn
  have parts := List.nodup_append'.mp nd
  apply mappedAdd_physical _ _ _ _ parts.2.1
  intro b hb q hq hbad
  simp only [foldBits,List.mem_append,List.mem_map,List.mem_singleton] at hb
  rcases hb with ⟨i,_,rfl⟩ | rfl
  · have eq : q=(if sparseF.testBit (i+1) then L.plus else L.minus) := by
      exact (Option.mem_some_iff.mp hq).symm
    subst q
    exact List.disjoint_left.mp parts.2.2 (by split_ifs <;> simp) hbad
  · simp at hq

private theorem fold_sub_physical (L : Layout) (hn : L.wires.Nodup) :
    GatePhysical (mappedSub (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity) := by
  simpa only [mappedSub,gatePhysical_append] using
    And.intro (And.intro (notRegister_physical _) (fold_adder_physical L hn)) (notRegister_physical _)

theorem circuit_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (BalancedCircuit.program L) := by
  have raw := (signedWords_physical L.sign (rawSource L) (rawTarget L) L.carry (rawLayoutND L hn)).1
  have small := small_physical L hn
  have fold : GatePhysical (BalancedCircuit.fold L) := by
    simpa only [BalancedCircuit.fold,gatePhysical_append] using And.intro (fold_adder_physical L hn) small.2.2.2.2.2
  have rot := (rotate_physical (rawTarget L) (rawTargetND L hn)).1
  have cl := cleanup_physical L.toLayout hw (List.nodup_append'.mp hn).2.1
  simp only [BalancedCircuit.program,gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨⟨seed_physical L hw hn,?_⟩,small.1⟩,fold⟩,rot⟩,small.2.1⟩,cl⟩,small.2.2.2.2.1⟩
  simpa only [rawAdd,signedAdd] using raw

theorem inverse_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (BalancedInverse.program L) := by
  have nd := rawLayoutND L hn
  have sc := signComplement_physical L.sign (rawSource L)
    (fun h => (List.nodup_cons.mp nd).1 (by simp [h]))
  have sub := subInPlace_physical (rawSource L) (rawTarget L) L.carry L.sign nd
  have raw : GatePhysical (BalancedInverse.rawSubtract L) := by
    simpa only [BalancedInverse.rawSubtract,gatePhysical_append] using And.intro (And.intro sc sub) sc
  have small := small_physical L hn
  have fold : GatePhysical (BalancedInverse.undoFold L) := by
    simpa only [BalancedInverse.undoFold,gatePhysical_append] using And.intro small.2.2.2.2.2 (fold_sub_physical L hn)
  have rot := (rotate_physical (rawTarget L) (rawTargetND L hn)).2
  have cl := cleanup_physical L.toLayout hw (List.nodup_append'.mp hn).2.1
  simp only [BalancedInverse.program,BalancedInverse.recoverParity,gatePhysical_append]
  refine ⟨⟨⟨⟨⟨⟨⟨small.2.2.2.2.1,cl⟩,small.2.2.1⟩,rot⟩,fold⟩,small.2.2.2.1⟩,?_⟩,
    reverse_physical _ (seed_physical L hw hn)⟩
  exact raw

end ECDSAAdd.Entrant.OneBankPhysical5

end



-- ===== Generic BiasPhysical =====
section
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BiasedInverse
open Arithmetic RecordedQuantum
attribute [local irreducible] mappedSub BalancedCircuit.seedViews BalancedInverse.rawSubtract

theorem physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) := by
  have oldF:=OneBankPhysical5.circuit_physical L hw hn
  have oldI:=OneBankPhysical5.inverse_physical L hw hn
  simp only [BalancedCircuit.program_eq_core,BalancedCleanup.program,gatePhysical_append] at oldF
  simp only [BalancedInverse.program,BalancedInverse.recoverParity,gatePhysical_append] at oldI
  have pre : GatePhysical (recoverPrefix L) := by
    simp only [recoverPrefix,gatePhysical_append]
    tauto
  have view : GatePhysical (unbiasView L) := by
    simp only [unbiasView,gatePhysical_append]
    exact ⟨by simp [GatePhysical,PhysicalInstr,ProperGate],by tauto⟩
  have small : GatePhysical (selectors L++release L++[.CX L.parity L.r0]) := by
    have nd:=BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    simp_all [selectors,release,GatePhysical,PhysicalInstr,ProperGate,ne_comm]
  have fnd : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take:=(List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have ma : GatePhysical (mappedAdd (biasBits L) L.r (L.carry.take 255) L.minus) := by
    apply mappedAdd_physical _ _ _ _ fnd
    intro b hb q hq hmem
    have mem : q∈mappedWires (biasBits L) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    have src:=biasBits_sources L q mem
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have nd:=BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append,or_assoc] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have mapped : GatePhysical (unfoldBias L) := by
    have nt := notRegister_physical L.r
    simpa only [unfoldBias,mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  simp only [gatePhysical_append] at small
  simp only [program,restoreRaw,gatePhysical_append]
  tauto
end ECDSAAdd.Entrant.BiasedInverse
end

-- ===== Generic ShortPhysical =====
section
namespace ECDSAAdd.Entrant.ShortBiasedPhysical
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum ECDSAAdd.Entrant.ShortBiasedFold
abbrev Layout := ECDSAAdd.Arithmetic.BalancedCircuit.Layout
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem narrow_physical (L : Layout) (hn : L.wires.Nodup) :
    GatePhysical (shortFold L) ∧ GatePhysical (shortUnfold L) := by
  have nd := BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have fullND : (L.minus::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 255 L.carry).count_le q
    simp only [List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have smallND : (L.minus::(L.low++L.carry.take 254)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have count := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take := (List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at count ⊢
    omega
  have fullSrc : ∀q∈mappedWires (BiasedCircuit.biasBits L),q∉L.minus::(L.r++L.carry.take 255) := by
    intro q hq hmem
    have src := BiasedCircuit.biasBits_sources L q hq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have smallSrc : ∀q∈mappedWires (lowBits L),q∉L.minus::(L.low++L.carry.take 254) := by
    intro q hq hmem
    have fullq : q∈mappedWires (BiasedCircuit.biasBits L) := by
      rw [biasBits_split]
      simp only [mappedWires,List.flatMap_append,List.mem_append]
      exact Or.inl hq
    have src := BiasedCircuit.biasBits_sources L q fullq
    have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      rcases src with he|he <;> simp [he]
    have ne : q≠L.minus := by rcases src with rfl|rfl <;> tauto
    simp only [List.mem_cons,List.mem_append] at hmem
    rcases hmem with he|he|he
    · exact ne he
    · exact BalancedCircuit.flagAway L hn q flag (by simp [BalancedCleanup.Layout.r,he])
    · exact BalancedCircuit.flagAway L hn q flag (by simp [List.mem_of_mem_take he])
  have topAway : L.rmsb∉L.low := by
    intro bad
    have data := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) L.rmsb
    have cnt := List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.r,List.count_append,List.count_cons,List.count_nil] at data
    simp at data
    omega
  have parityAway : L.parity∉L.low := by
    intro bad
    exact BalancedCircuit.flagAway L hn L.parity (by simp) (by simp [BalancedCleanup.Layout.r,bad])
  have ma : GatePhysical (mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.minus) := by
    apply mappedAdd_physical _ _ _ _ smallND
    intro bit hb q hq
    apply smallSrc q
    exact List.mem_flatMap.mpr ⟨bit,hb,by simpa using hq⟩
  have ms : GatePhysical (mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.minus) := by
    have nt := notRegister_physical L.low
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  have cx : GatePhysical [.CX L.parity L.rmsb] := by
    simp_all [GatePhysical,PhysicalInstr,ProperGate,ne_comm]
  simp only [ShortBiasedFold.shortFold,ShortBiasedFold.shortUnfold,gatePhysical_append]
  exact ⟨⟨ma,cx⟩,⟨ms,cx⟩⟩

theorem forward_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (ShortBiasedFold.program L) := by
  have old := BiasedCircuit.physical L hw hn
  have narrow := (narrow_physical L hn).1
  simp only [BiasedCircuit.program,BiasedCircuit.biasedPrefix,gatePhysical_append] at old
  simp only [ShortBiasedFold.program,ShortBiasedFold.biasedPrefix,ShortBiasedFold.remainder,gatePhysical_append]
  tauto

theorem inverse_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (ShortBiasedInverse.program L) := by
  have old := BiasedInverse.physical L hw hn
  have narrow := (narrow_physical L hn).2
  simp only [BiasedInverse.program,BiasedInverse.restoreRaw,gatePhysical_append] at old
  simp only [ShortBiasedInverse.program,ShortBiasedInverse.restoreRaw,ShortBiasedInverse.unfoldBias,gatePhysical_append]
  tauto
end ECDSAAdd.Entrant.ShortBiasedPhysical
end
end



-- ===== ECDSAAdd.Submission.Entrant.HalfConvert =====
section

/-! Halving boundary conversion for the balanced field replay.

For a canonical field word `v = x.val` the balanced representative of `x/2`
is fixed by the low bit `k = v mod 2` alone: `2·(x/2) = v + k·p`, so
`centered (x/2) = ⌊v/2⌋ - k·(p-1)/2`.  The conversion therefore needs no
comparison: move the low bit into the flag, rotate the word right by one,
add `k·(2^256-(p-1)/2)`, and clear the flag from the sign bit.  The inverse
subtracts the same masked constant, rotates left and moves the flag back into
the low bit, returning the canonical word of `2x`.  The rotated word is at most
`q = (p-1)/2`, and below `q` when `k = 1`, while `q+2^31+489 = 2^255`: no carry
reaches bit 255.  So only the low 255 bits go through a mapped adder and the
offset's top bit is one CNOT from the flag; the inverse likewise never borrows
from bit 255.  Each direction costs one 255-bit adder (254 Toffolis), against
765 for the compare-add-uncompare converter of `BalancedConvert`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfConvert
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.BalancedField ECDSAAdd.Arithmetic.BalancedConvert
open Secp256k1 RecordedQuantum

/-- `2^256 - (p-1)/2`, the two's-complement offset of `-(p-1)/2`. -/
def halfC : Nat := 2^255+2^31+489

def correction (L : Layout) : List MappedBit :=
  (List.range 256).map fun i =>
    {wire:=if halfC.testBit i then some L.flag else none,flip:=false}

/-- The low 255 bits of the masked offset, `k·(2^31+489)`. -/
def lowCorrection (L : Layout) : List MappedBit :=
  (List.range 255).map fun i =>
    {wire:=if halfC.testBit i then some L.flag else none,flip:=false}

def lowBit (L : Layout) : Wire := L.low.headD L.msb

/-- Canonical `x` to the balanced word of `x/2`: the low 255 bits take the low
part of the masked offset, then the flag moves into the sign bit (bit 255 of
`halfC`), which also clears it. -/
def center (L : Layout) : Program :=
  [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]++rotateRight L.word++
    mappedAdd (lowCorrection L) L.low (L.carry.take 254) L.cin++[.CX L.flag L.msb,.CX L.msb L.flag]

/-- Balanced word of `x` to the canonical word of `2x`: the sign bit moves into
the flag (clearing bit 255), then the low 255 bits drop the offset's low part. -/
def canonical (L : Layout) : Program :=
  [.CX L.msb L.flag,.CX L.flag L.msb]++mappedSub (lowCorrection L) L.low (L.carry.take 254) L.cin++
    rotateLeft L.word++[.CX L.flag (lowBit L),.CX (lowBit L) L.flag]

/-! Arithmetic of the halving identity. -/

private instance : NeZero p := ⟨p_prime.ne_zero⟩

private theorem p_eq : p=115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [p]

private theorem q_eq : q=57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
  norm_num [q,p]

private theorem pow256 : (2:Nat)^256=115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num

private theorem halfC_eq : halfC=57896044618658097711785492504343953926634992332820282019728792003958712304105 := by
  norm_num [halfC]

private theorem pow255 : (2:Nat)^255=57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  norm_num

private theorem sparseF_eq : BalancedCircuit.sparseF=4294968273 := by norm_num [BalancedCircuit.sparseF]

theorem half_val (x : Fp) :
    (x/2 : Fp).val=if x.val%2=0 then x.val/2 else (x.val+p)/2 := by
  have hv : x.val<p := ZMod.val_lt x
  have hpo : p%2=1 := by norm_num [p]
  have two : (2:Fp)≠0 := by decide
  have key : ∀ w : Nat,w<p → ((w:Nat):Fp)*2=x → (x/2 : Fp).val=w := by
    intro w hw h
    have e : x/2=((w:Nat):Fp) := by rw [div_eq_iff two]; exact h.symm
    rw [e,ZMod.val_natCast_of_lt hw]
  by_cases he : x.val%2=0
  · rw [if_pos he]
    apply key _ (by omega)
    have e : x.val/2*2=x.val := by omega
    calc ((x.val/2 : Nat):Fp)*2=((x.val/2*2 : Nat):Fp) := by rw [Nat.cast_mul]; norm_num
      _=x := by rw [e,ZMod.natCast_zmod_val]
  · rw [if_neg he]
    apply key _ (by omega)
    have e : (x.val+p)/2*2=x.val+p := by omega
    calc (((x.val+p)/2 : Nat):Fp)*2=(((x.val+p)/2*2 : Nat):Fp) := by rw [Nat.cast_mul]; norm_num
      _=x := by rw [e,Nat.cast_add,ZMod.natCast_self,add_zero,ZMod.natCast_zmod_val]

theorem threshold_half (x : Fp) : threshold (x/2)=decide (x.val%2=1) := by
  have hv : x.val<p := ZMod.val_lt x
  have hp := p_eq
  unfold threshold
  rw [half_val,q_eq]
  by_cases he : x.val%2=0
  · rw [if_pos he]
    simp only [decide_eq_decide]
    omega
  · rw [if_neg he]
    simp only [decide_eq_decide]
    omega

theorem centerWord_half (x : Fp) :
    centerWord (x/2)=((if x.val%2=1 then halfC else 0)+x.val/2)%2^256 := by
  have hv : x.val<p := ZMod.val_lt x
  have hp := p_eq
  rw [centerWord_value,threshold_half,half_val,pow256,halfC_eq,sparseF_eq]
  by_cases he : x.val%2=0
  · have h1 : ¬x.val%2=1 := by omega
    rw [if_pos he]
    simp only [h1,decide_false,Bool.false_eq_true,if_false]
    omega
  · have h1 : x.val%2=1 := by omega
    rw [if_neg he]
    simp only [h1,decide_true,if_true]
    omega

/-! The masked constant. -/

private def virtual (b : Bool) : Nat :=
  (List.range 256).foldr (fun i n => (if halfC.testBit i then b else false).toNat+2*n) 0

private theorem virtual_value (b : Bool) : virtual b=if b then halfC else 0 := by
  cases b <;> decide

private theorem correction_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i => ({wire:=(if halfC.testBit i then some L.flag else none),flip:=false} : MappedBit))) s=
    is.foldr (fun i n => (if halfC.testBit i then s L.flag else false).toNat+2*n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons,ih]
    cases hi : halfC.testBit i <;> simp [MappedBit.value,hi]

theorem correction_value (L : Layout) (s : BasisState) :
    mappedValue (correction L) s=if s L.flag then halfC else 0 := by
  rw [correction,correction_list]
  exact virtual_value _

theorem correction_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (correction L)) : w=L.flag := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  cases hf : halfC.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw

theorem correction_length (L : Layout) : (correction L).length=256 := by simp [correction]

private def lowVirtual (b : Bool) : Nat :=
  (List.range 255).foldr (fun i n => (if halfC.testBit i then b else false).toNat+2*n) 0

private theorem lowVirtual_value (b : Bool) : lowVirtual b=if b then 2147484137 else 0 := by
  cases b <;> decide

theorem lowCorrection_value (L : Layout) (s : BasisState) :
    mappedValue (lowCorrection L) s=if s L.flag then 2147484137 else 0 := by
  rw [lowCorrection,correction_list]
  exact lowVirtual_value _

theorem lowCorrection_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (lowCorrection L)) :
    w=L.flag := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  cases hf : halfC.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw

theorem lowCorrection_length (L : Layout) : (lowCorrection L).length=255 := by simp [lowCorrection]

/-! The low adder: the low 255 bits and the first 254 carries. -/

private theorem low_sub (L : Layout) :
    (L.cin::(L.low++L.carry.take 254)).Sublist (L.cin::(L.word++L.carry)) := by
  apply List.Sublist.cons₂
  rw [Layout.word,List.append_assoc]
  exact List.Sublist.append (List.Sublist.refl _)
    ((List.take_sublist _ _).trans (List.sublist_append_right _ _))

private theorem low_nodup (L : Layout) (hn : L.wires.Nodup) :
    (L.cin::(L.low++L.carry.take 254)).Nodup :=
  (low_sub L).nodup (layout_add L hn)

private theorem low_away (L : Layout) (hn : L.wires.Nodup) :
    L.flag∉L.cin::(L.low++L.carry.take 254) :=
  fun h => flag_away L hn ((low_sub L).subset h)

private theorem low_widths (L : Layout) (hw : L.Widths) :
    (lowCorrection L).length=L.low.length ∧ (L.carry.take 254).length+1=L.low.length := by
  rw [lowCorrection_length,hw.1,List.length_take,hw.2]
  decide

private theorem msb_low (L : Layout) (hn : L.wires.Nodup) : L.msb∉L.low := fun h =>
  List.disjoint_left.mp (List.nodup_append'.mp
    (List.nodup_append'.mp (List.nodup_cons.mp (layout_add L hn)).2).1).2.2 h
    (List.mem_singleton_self _)

/-- The word is its low 255 bits plus the sign bit. -/
private theorem word_split (L : Layout) (hw : L.Widths) (s : BasisState) :
    regValue L.word s=regValue L.low s+2^255*(if s L.msb then 1 else 0) := by
  rw [Layout.word,regValue_append,hw.1]
  rfl

/-! Gate-level helpers. -/

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,
      run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩

private theorem swap_in (a f : Wire) (ha : a≠f) (s : State) (m : List Bool)
    (hf : s.basis f=false) :
    (run [.CX a f,.CX f a] m s).phase=s.phase ∧
    (run [.CX a f,.CX f a] m s).basis f=s.basis a ∧
    (run [.CX a f,.CX f a] m s).basis a=false ∧
    ∀ q,q≠a → q≠f → (run [.CX a f,.CX f a] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_,?_⟩
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
  · intro q hqa hqf
    simp [run,writeBit,Function.update_apply,hqa,hqf]

private theorem swap_out (a f : Wire) (ha : a≠f) (s : State) (m : List Bool)
    (hz : s.basis a=false) :
    (run [.CX f a,.CX a f] m s).phase=s.phase ∧
    (run [.CX f a,.CX a f] m s).basis a=s.basis f ∧
    (run [.CX f a,.CX a f] m s).basis f=false ∧
    ∀ q,q≠a → q≠f → (run [.CX f a,.CX a f] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_,?_⟩
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hz]
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hz]
  · intro q hqa hqf
    simp [run,writeBit,Function.update_apply,hqa,hqf]

private theorem cx_one (c t : Wire) (s : State) (m : List Bool) :
    (run [.CX c t] m s).phase=s.phase ∧
    (run [.CX c t] m s).basis t=(s.basis t ^^ s.basis c) ∧
    ∀ q,q≠t → (run [.CX c t] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_⟩
  · simp [run,writeBit]
  · intro q hq
    simp [run,writeBit,Function.update_apply,hq]

/-- Shape of a width-checked layout: the low bit heads the word. -/
private theorem word_shape (L : Layout) (hw : L.Widths) :
    ∃ a rest,lowBit L=a ∧ L.word=a::rest := by
  cases h : L.low with
  | nil => have e := hw.1; rw [h] at e; simp at e
  | cons a tl => exact ⟨a,tl++[L.msb],by simp [lowBit,h],by simp [Layout.word,h]⟩

private theorem word_nodup (L : Layout) (hn : L.wires.Nodup) : L.word.Nodup :=
  (List.nodup_append'.mp (List.nodup_cons.mp (layout_add L hn)).2).1

private theorem reg_cons (a : Wire) (rest : List Wire) (s : BasisState) :
    regValue (a::rest) s=(if s a then 1 else 0)+2*regValue rest s := rfl

/-- Canonical-to-balanced halving conversion, with all work restored, every
measurement record and arbitrary incoming phase. -/
theorem center_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (center L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=centerWord (x/2) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  have nd := word_nodup L hn
  rw [hword] at nd
  have aRest : a∉rest := (List.nodup_cons.mp nd).1
  have aw : a∈L.word := by rw [hword]; simp
  have fa : a≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ aw)
  have hflag : s.basis L.flag=false := hc _ (by simp [work])
  have restFlag : L.flag∉rest := fun h => layout_away L hn L.flag (by simp) (by rw [hword]; simp [h])
  have flagWord : L.flag∉L.word := layout_away L hn L.flag (by simp)
  have msbWord : L.msb∈L.word := by simp [Layout.word]
  have fm : L.flag≠L.msb := fun e => flagWord (e ▸ msbWord)
  have lowWord (q : Wire) (hq : q∈L.low) : q∈L.word := by simp [Layout.word,hq]
  have msbLow := msb_low L hn
  have lw := low_widths L hw
  have xv : x.val<p := ZMod.val_lt x
  have hp := p_eq
  dsimp only
  obtain ⟨m1,m2,m3,m4,e⟩ := run_four [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]
    (rotateRight L.word) (mappedAdd (lowCorrection L) L.low (L.carry.take 254) L.cin)
    [.CX L.flag L.msb,.CX L.msb L.flag] m s
  rw [show center L=[.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]++rotateRight L.word++
    mappedAdd (lowCorrection L) L.low (L.carry.take 254) L.cin++[.CX L.flag L.msb,.CX L.msb L.flag]
    from rfl,e,hlow]
  generalize e1 : run [.CX a L.flag,.CX L.flag a] m1 s=s1
  generalize e2 : run (rotateRight L.word) m2 s1=s2
  generalize e3 : run (mappedAdd (lowCorrection L) L.low (L.carry.take 254) L.cin) m3 s2=s3
  generalize e4 : run [.CX L.flag L.msb,.CX L.msb L.flag] m4 s3=s4
  -- stage one: the low bit moves into the flag
  have h1 := swap_in a L.flag fa s m1 hflag
  rw [e1] at h1
  let R := regValue rest s.basis
  have hxv : x.val=(if s.basis a then 1 else 0)+2*R := by rw [←hx,hword]; rfl
  have restSame : regValue rest s1.basis=R := by
    apply regValue_congr
    intro q hq
    exact h1.2.2.2 q (fun e => aRest (e ▸ hq)) (fun e => restFlag (e ▸ hq))
  have v1 : regValue L.word s1.basis=2*R := by
    rw [hword,reg_cons,h1.2.2.1,restSame]; simp
  -- stage two: halve by rotation
  have r2 := rotateRight_spec L.word (word_nodup L hn) (2*R) (by omega) s1 m2 v1
  have f2 := (rotate_frame L.word s1 m2).2.1
  rw [e2] at r2 f2
  have v2 : regValue L.word s2.basis=R := by
    have h := r2.2
    change regValue L.word s2.basis=2*R/2 at h
    omega
  have clean2 (q : Wire) (hq : q∈scratch L) : s2.basis q=false := by
    have away := scratch_away L hn q hq
    have qa : q≠a := fun e => away.1 (e ▸ aw)
    rw [f2 q away.1,h1.2.2.2 q qa away.2]
    exact hc q (by simp [work,hq])
  have flag2 : s2.basis L.flag=s.basis a := by
    rw [f2 _ flagWord,h1.2.1]
  -- the halved word is at most q < 2^255, so its sign bit is clear
  have split2 := word_split L hw s2.basis
  rw [v2,pow255] at split2
  have msb2 : s2.basis L.msb=false := by
    cases h : s2.basis L.msb
    · rfl
    · rw [h] at split2
      simp only [if_true,Nat.mul_one] at split2
      omega
  have low2 : regValue L.low s2.basis=R := by
    rw [msb2] at split2
    simp only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at split2
    omega
  -- stage three: add the offset's low 255 bits; no carry reaches bit 255
  have p3 := mappedAdd_correct (lowCorrection L) L.low (L.carry.take 254) L.cin (low_nodup L hn)
    (fun q hq => (lowCorrection_sources L q hq).symm ▸ low_away L hn) lw.1 lw.2 s2 m3
    (fun q hq => clean2 q (by simp [scratch,List.mem_of_mem_take hq]))
  rw [e3] at p3
  have v3 : regValue L.low s3.basis=(if s.basis a then 2147484137 else 0)+R := by
    rw [p3.2.2,lowCorrection_value,flag2,low2,clean2 _ (by simp [scratch]),hw.1,pow255]
    cases hk : s.basis a <;> simp only [hk,Bool.false_eq_true,if_false,if_true,Bool.toNat_false,
      Nat.add_zero,Nat.zero_add] at hxv ⊢ <;> omega
  have flag3 : s3.basis L.flag=s.basis a :=
    (p3.2.1 _ (fun h => flagWord (lowWord _ h))).trans flag2
  have msb3 : s3.basis L.msb=false := (p3.2.1 _ msbLow).trans msb2
  -- stage four: the flag becomes the sign bit and is cleared
  have h4 := swap_in L.flag L.msb fm s3 m4 msb3
  rw [e4] at h4
  have low4 : regValue L.low s4.basis=regValue L.low s3.basis := by
    apply regValue_congr
    intro q hq
    exact h4.2.2.2 q (fun e => flagWord (e ▸ lowWord q hq)) (fun e => msbLow (e ▸ hq))
  have frame : ∀q,q∉L.word → s4.basis q=s.basis q := by
    intro q hq
    by_cases hf : q=L.flag
    · subst q
      rw [h4.2.2.1,hflag]
    · have qa : q≠a := fun e => hq (e ▸ aw)
      have qm : q≠L.msb := fun e => hq (e ▸ msbWord)
      rw [h4.2.2.2 q hf qm,p3.2.1 q (fun h => hq (lowWord q h)),f2 q hq,h1.2.2.2 q qa hf]
  refine ⟨h4.1.trans (p3.1.trans (r2.1.trans h1.1)),?_,work_of_frame L hn s s4 hc frame,frame⟩
  rw [word_split L hw,low4,v3,h4.2.1,flag3,centerWord_half,halfC_eq,pow255,pow256]
  cases hk : s.basis a
  · have h : ¬(x.val%2=1) := by simp only [hk,Bool.false_eq_true,if_false] at hxv; omega
    rw [if_neg h]
    simp only [hk,Bool.false_eq_true,if_false] at hxv ⊢
    omega
  · have h : x.val%2=1 := by simp only [hk,if_true] at hxv; omega
    rw [if_pos h]
    simp only [hk,if_true] at hxv ⊢
    omega

/-- Balanced-to-canonical doubling conversion. -/
theorem canonical_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=centerWord x)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (canonical L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=(2*x).val ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  have len := word_length L hw
  have nd := word_nodup L hn
  rw [hword] at nd
  have aRest : a∉rest := (List.nodup_cons.mp nd).1
  have aw : a∈L.word := by rw [hword]; simp
  have fa : a≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ aw)
  have hflag : s.basis L.flag=false := hc _ (by simp [work])
  have restFlag : L.flag∉rest := fun h => layout_away L hn L.flag (by simp) (by rw [hword]; simp [h])
  have flagWord : L.flag∉L.word := layout_away L hn L.flag (by simp)
  have msbWord : L.msb∈L.word := by simp [Layout.word]
  have mf : L.msb≠L.flag := fun e => flagWord (e ▸ msbWord)
  have lowWord (q : Wire) (hq : q∈L.low) : q∈L.word := by simp [Layout.word,hq]
  have msbLow := msb_low L hn
  have lw := low_widths L hw
  let y : Fp := 2*x
  have hy : y/2=x := by
    have two : (2:Fp)≠0 := by decide
    change (2*x)/2=x
    rw [mul_comm,mul_div_cancel_right₀ x two]
  let k : Bool := decide (y.val%2=1)
  let R := y.val/2
  have hpow : (2:Nat)^256=2*2^255 := by norm_num
  have yv : y.val<p := ZMod.val_lt y
  have hp := p_eq
  have cw : centerWord x=(if k then halfC else 0)+R := by
    rw [←hy,centerWord_half,halfC_eq,pow256]
    simp only [k,R]
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true]; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false]; omega
  dsimp only
  obtain ⟨m1,m2,m3,m4,e⟩ := run_four [.CX L.msb L.flag,.CX L.flag L.msb]
    (mappedSub (lowCorrection L) L.low (L.carry.take 254) L.cin) (rotateLeft L.word)
    [.CX L.flag (lowBit L),.CX (lowBit L) L.flag] m s
  rw [show canonical L=[.CX L.msb L.flag,.CX L.flag L.msb]++
    mappedSub (lowCorrection L) L.low (L.carry.take 254) L.cin++
    rotateLeft L.word++[.CX L.flag (lowBit L),.CX (lowBit L) L.flag] from rfl,e,hlow]
  generalize e1 : run [.CX L.msb L.flag,.CX L.flag L.msb] m1 s=s1
  generalize e2 : run (mappedSub (lowCorrection L) L.low (L.carry.take 254) L.cin) m2 s1=s2
  generalize e3 : run (rotateLeft L.word) m3 s2=s3
  generalize e4 : run [.CX L.flag a,.CX a L.flag] m4 s3=s4
  -- stage one: the sign bit moves into the flag, clearing bit 255
  have sm : s.basis L.msb=threshold x := word_msb L hw s.basis _ (threshold x) hx (center_threshold x)
  have hk : threshold x=k := by rw [←hy,threshold_half]
  have p1 := swap_in L.msb L.flag mf s m1 hflag
  rw [e1] at p1
  have flag1 : s1.basis L.flag=k := by rw [p1.2.1,sm,hk]
  have clean1 (q : Wire) (hq : q∈scratch L) : s1.basis q=false := by
    have away := scratch_away L hn q hq
    rw [p1.2.2.2 q (fun e => away.1 (e ▸ msbWord)) away.2]
    exact hc q (by simp [work,hq])
  have low0 : regValue L.low s.basis=(if k then 2147484137 else 0)+R := by
    have split := word_split L hw s.basis
    rw [hx,cw,sm,hk,halfC_eq,pow255] at split
    simp only [k,R] at split ⊢
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true] at split ⊢; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false] at split ⊢; omega
  have low1 : regValue L.low s1.basis=regValue L.low s.basis := by
    apply regValue_congr
    intro q hq
    exact p1.2.2.2 q (fun e => msbLow (e ▸ hq)) (fun e => flagWord (e ▸ lowWord q hq))
  -- stage two: remove the offset's low 255 bits; no borrow reaches bit 255
  have p2 := mappedSub_correct (lowCorrection L) L.low (L.carry.take 254) L.cin (low_nodup L hn)
    (fun q hq => (lowCorrection_sources L q hq).symm ▸ low_away L hn) lw.1 lw.2 s1 m2
    (fun q hq => clean1 q (by simp [scratch,List.mem_of_mem_take hq]))
    (clean1 _ (by simp [scratch]))
  rw [e2] at p2
  have low2 : regValue L.low s2.basis=R := by
    rw [p2.2.2,lowCorrection_value,flag1,low1,low0,hw.1,pow255]
    simp only [k,R]
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true]; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false]; omega
  have msb2 : s2.basis L.msb=false := (p2.2.1 _ msbLow).trans p1.2.2.1
  have v2 : regValue L.word s2.basis=R := by
    rw [word_split L hw,low2,msb2]
    simp only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero]
  have flag2 : s2.basis L.flag=k := (p2.2.1 _ (fun h => flagWord (lowWord _ h))).trans flag1
  -- stage three: double by rotation
  have r3 := rotateLeft_spec L.word (word_nodup L hn) R (by rw [len]; omega) s2 m3 v2
  have f3 := (rotate_frame L.word s2 m3).2.2.2
  rw [e3] at r3 f3
  have v3 : regValue L.word s3.basis=2*R := r3.2
  have flag3 : s3.basis L.flag=k := (f3 _ flagWord).trans flag2
  have parts : (if s3.basis a then 1 else 0)+2*regValue rest s3.basis=2*R := by
    rw [←reg_cons,←hword]; exact v3
  have a3 : s3.basis a=false := by
    cases h : s3.basis a
    · rfl
    · rw [h] at parts; simp at parts; omega
  have rest3 : regValue rest s3.basis=R := by rw [a3] at parts; simp at parts; omega
  -- stage four: the flag returns to the low bit
  have p4 := swap_out a L.flag fa s3 m4 a3
  rw [e4] at p4
  have rest4 : regValue rest s4.basis=R := by
    rw [←rest3]
    apply regValue_congr
    intro q hq
    exact p4.2.2.2 q (fun e => aRest (e ▸ hq)) (fun e => restFlag (e ▸ hq))
  have v4 : regValue L.word s4.basis=y.val := by
    rw [hword,reg_cons,p4.2.1,flag3,rest4]
    simp only [k,R]
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true]; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false]; omega
  have frame : ∀q,q∉L.word → s4.basis q=s.basis q := by
    intro q hq
    by_cases hf : q=L.flag
    · subst q
      rw [p4.2.2.1,hflag]
    · have qa : q≠a := fun e => hq (e ▸ aw)
      have qm : q≠L.msb := fun e => hq (e ▸ msbWord)
      rw [p4.2.2.2 q qa hf,f3 q hq,p2.2.1 q (fun h => hq (lowWord q h)),p1.2.2.2 q qm hf]
  exact ⟨p4.1.trans (r3.1.trans (p2.1.trans p1.1)),v4,work_of_frame L hn s s4 hc frame,frame⟩

/-! Resources, support and physical form. -/

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (center L)=254 ∧ measurementCount (center L)=254 ∧
    toffoliCount (canonical L)=254 ∧ measurementCount (canonical L)=254 := by
  have lw := low_widths L hw
  have a := mappedAdd_counts (lowCorrection L) L.low (L.carry.take 254) L.cin lw.1 lw.2
  have b := mappedSub_counts (lowCorrection L) L.low (L.carry.take 254) L.cin lw.1 lw.2
  have r := rotate_counts L.word
  simp [center,canonical,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    r.1,r.2.1,r.2.2.1,r.2.2.2,hw.1,toffoliCount,measurementCount]

private theorem lowBit_mem (L : Layout) (hw : L.Widths) : lowBit L∈L.word := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  rw [hlow,hword]; simp

private theorem word_sub (L : Layout) (q : Wire) (hq : q∈L.word) : q∈L.wires.toFinset := by
  simp only [Layout.word,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Layout.wires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem support (L : Layout) (hw : L.Widths) :
    wires (center L)⊆L.wires.toFinset ∧ wires (canonical L)⊆L.wires.toFinset := by
  have c := mappedAdd_wires_subset (lowCorrection L) L.low (L.carry.take 254) L.cin
  have d := mappedSub_wires_subset (lowCorrection L) L.low (L.carry.take 254) L.cin
  have r := rotate_wires L.word
  have lb := word_sub L _ (lowBit_mem L hw)
  have fl : L.flag∈L.wires.toFinset := by simp [Layout.wires]
  have ms : L.msb∈L.wires.toFinset := by simp [Layout.wires]
  have mapped (q : Wire)
      (hq : q∈(mappedWires (lowCorrection L)++L.low++L.carry.take 254++[L.cin]).toFinset) :
      q∈L.wires.toFinset := by
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with hq|hq|hq|hq
    · have e := lowCorrection_sources L q hq
      simp [Layout.wires,e]
    · simp [Layout.wires,hq]
    · simp [Layout.wires,List.mem_of_mem_take hq]
    · simp [Layout.wires,hq]
  have rot (q : Wire) (hq : q∈(if L.word.length<2 then ∅ else L.word.toFinset)) :
      q∈L.wires.toFinset := by
    split at hq
    · simp at hq
    · exact word_sub L q (List.mem_toFinset.mp hq)
  have cxs (a b : Wire) (ha : a∈L.wires.toFinset) (hb : b∈L.wires.toFinset) :
      wires [.CX a b,.CX b a]⊆L.wires.toFinset := by
    intro q hq
    have h : q=a ∨ q=b := by simp [wires,Instr.wires] at hq; tauto
    rcases h with rfl|rfl <;> assumption
  constructor
  · intro q hq
    simp only [center,wires_append,Finset.mem_union] at hq
    rcases hq with ((hq|hq)|hq)|hq
    · exact cxs _ _ lb fl hq
    · exact rot q (r.1 ▸ hq)
    · exact mapped q (c hq)
    · exact cxs _ _ fl ms hq
  · intro q hq
    simp only [canonical,wires_append,Finset.mem_union] at hq
    rcases hq with ((hq|hq)|hq)|hq
    · exact cxs _ _ ms fl hq
    · exact mapped q (d hq)
    · exact rot q (r.2 ▸ hq)
    · exact cxs _ _ fl lb hq

theorem physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (center L) ∧ GatePhysical (canonical L) := by
  have nd : (L.cin::L.low++L.carry.take 254).Nodup := low_nodup L hn
  have src : ∀ b∈lowCorrection L,∀q∈b.wire,q∉L.cin::L.low++L.carry.take 254 := by
    intro b hb q hq
    have e : q=L.flag := lowCorrection_sources L q (List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩)
    subst q
    exact low_away L hn
  have mf : L.msb≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ (by simp [Layout.word]))
  have lf : lowBit L≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ lowBit_mem L hw)
  have top : GatePhysical [.CX L.flag L.msb,.CX L.msb L.flag] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,mf,Ne.symm mf]
  have top' : GatePhysical [.CX L.msb L.flag,.CX L.flag L.msb] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,mf,Ne.symm mf]
  have sin : GatePhysical [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lf,Ne.symm lf]
  have sout : GatePhysical [.CX L.flag (lowBit L),.CX (lowBit L) L.flag] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lf,Ne.symm lf]
  have ma := mappedAdd_physical _ _ _ _ nd src
  have nt := notRegister_physical L.low
  have ms : GatePhysical (mappedSub (lowCorrection L) L.low (L.carry.take 254) L.cin) := by
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  have rot := rotate_physical L.word (word_nodup L hn)
  simp only [center,canonical,gatePhysical_append]
  exact ⟨⟨⟨⟨sin,rot.1⟩,ma⟩,top⟩,⟨⟨⟨top',ms⟩,rot.2⟩,sout⟩⟩

end ECDSAAdd.Entrant.HalfConvert

end


-- ===== ECDSAAdd.Submission.Entrant.HalfField =====
section

/-! Source: submission94960368-af01-4326-b69e-f43f55712c0a;
original half-field method: submission8e13f110-79c6-44fd-a3a3-0730950fc6e8. -/

/-! Field segment with halving endpoints.

The protected segment converts both 256-bit field ports to balanced form on
entry and both back on exit (four compare-based converters, 3,060 Toffolis).
Here only the target port is converted, by the halving converter of
`HalfConvert`, which stores the balanced word of `Y/2`; the source port is
filled from (multiplication) or cleared against (division) the target while
both are balanced, so it never needs a converter.  The unchanged entry-trimmed
511-cell replay is linear in its payload, so it runs on `Y/2` and the exit
converter doubles its result back.  Cost: 254 + 254 Toffolis per segment. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfField
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed Secp256k1 BalancedField
open CompressedFieldSupport CompressedAllocation OffsetBorrowedCanonical RecordedQuantum
attribute [local irreducible] run wires allGroupEncode compressedHistoryEncode

abbrev tgt : BalancedConvert.Layout := balancedSharedTargetConvert base
abbrev ports : BalancedCircuit.Layout := balancedSharedPorts base (base 2409)

def centerT : Program := HalfConvert.center tgt
def canonT : Program := HalfConvert.canonical tgt
def copyN : Program := copyRegister none ports.r ports.y

/-- Division: halve-center the dividend, replay, clear the duplicated
source, double back.  Multiplication: halve-center, duplicate, replay, double. -/
def segment (divide : Bool) : Program :=
  if divide then centerT++(PenultimateMapped.replay true++(copyN++canonT))
  else centerT++(copyN++(PenultimateMapped.replay false++canonT))

/-! Site bookkeeping. -/

def ids : List Nat := [1797,1027,1796,2311,1025]++List.range' 2056 256++
  List.range' 770 256++List.range' 1540 255

private theorem ids_mem (i : Nat) (h : i=1797 ∨ i=1027 ∨ i=1796 ∨ i=2311 ∨ i=1025 ∨
    (2056 ≤ i ∧ i<2312) ∨ (770 ≤ i ∧ i<1026) ∨ (1540 ≤ i ∧ i<1795)) :
    base i∈(ids.map base).toFinset := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false]
  omega

private theorem tgt_ids : ∀q∈tgt.wires,q∈(ids.map base).toFinset := by
  intro q hq
  simp only [BalancedConvert.Layout.wires,balancedSharedTargetConvert,wireBlock,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_range'_1] at hq
  rcases hq with ((rfl|rfl|rfl|rfl)|⟨i,hi,rfl⟩)|⟨i,hi,rfl⟩
  all_goals apply ids_mem; omega

private theorem ports_r : ports.r=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
private theorem ports_y : ports.y=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)

theorem centerT_sites : wires centerT⊆(ids.map base).toFinset := by
  intro q hq
  exact tgt_ids q (List.mem_toFinset.mp
    ((HalfConvert.support tgt (balancedSharedTargetConvert_widths base)).1 hq))

theorem canonT_sites : wires canonT⊆(ids.map base).toFinset := by
  intro q hq
  exact tgt_ids q (List.mem_toFinset.mp
    ((HalfConvert.support tgt (balancedSharedTargetConvert_widths base)).2 hq))

theorem copyN_sites : wires copyN⊆(ids.map base).toFinset := by
  intro q hq
  have h := copyRegister_wires_subset none ports.r ports.y hq
  rw [ports_r,ports_y] at h
  simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    wireBlock,List.mem_map,List.mem_range'_1] at h
  rcases h with ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩
  all_goals apply ids_mem; omega

theorem ids_slots : (ids.map base).toFinset⊆slots.toFinset := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  apply slot_mem
  · unfold live; omega
  · unfold omitted; omega

/-- The full history encoder never touches the endpoint sites. -/
theorem encoder_disjoint (P : Program) (h : wires P⊆(ids.map base).toFinset) :
    Disjoint (wires (allGroupEncode base 170)) (wires P) := by
  have hist := compressedPrefix_history_support base base_pool_nodup base_above 512 (by decide)
  rw [encode_prefix_512] at hist
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (h hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem encoded_transport (P : Program) (dis : Disjoint (wires (allGroupEncode base 170)) (wires P))
    (s raw : State) (m : List Bool) (encoded : s=run (allGroupEncode base 170) [] raw)
    (phase : (run P m raw).phase=raw.phase) :
    (run P m s).phase=s.phase ∧ run P m s=run (allGroupEncode base 170) [] (run P m raw) := by
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact (run_disjoint_commute _ _ dis [] m raw).symm

/-! Frame steps. -/

private theorem port_split :
    (skywalkSharedField base).z=ports.r++[base 2312] ∧
    (skywalkSharedField base).a=ports.y++[base 1026] := by
  rw [skywalkShared_field_z,ports_r,ports_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem centerWord_zero : centerWord (0:Fp)=0 := by
  have h : (0:Int)≤q := by norm_num [q,p]
  simp [centerWord,centerFp,encodeWord,h]

private theorem target_clean (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (A B : Nat) (st : BasisState)
    (frame : PairFrame ports.r ports.y origin A B st) :
    ∀q∈BalancedConvert.work tgt,st q=false := by
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  intro q hq
  exact (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)

private theorem pair_dis (hn : (skywalkSharedWires base).Nodup) : ports.r.Disjoint ports.y :=
  (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2

private theorem tgt_word : tgt.word=ports.r := balancedSharedTargetConvert_word base (base 2409)

private theorem center_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=X.val →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=centerWord (X/2) ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin (X/2) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have split := port_split
  rw [split.1,split.2,ZMod.val_zero] at frame
  have narrow := balancedPair_narrow ports.r ports.y (base 2312) (base 1026) origin raw.basis
    X.val 0 (by rw [ports_r,wireBlock_length]; exact value_bound X)
    (by rw [ports_y,wireBlock_length]; norm_num) frame hr hy
  have c := hcorrect raw m (by rw [tgt_word]; exact narrow.1)
    (target_clean hn origin hw hu _ _ _ narrow)
  have pf : PairFrame ports.r ports.y origin (centerWord (X/2)) (centerWord 0)
      (run P m raw).basis := by
    rw [centerWord_zero]
    exact PairFrame.update_temp ports.r ports.y origin raw.basis _ X.val 0 _ (pair_dis hn) narrow
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  exact ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),pf,actual.2⟩


/-- Halving entry conversion of the target port; the zero source port is
already its own balanced word. -/
theorem center_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin (X/2) 0 (run centerT m s) := by
  exact center_frame_generic centerT centerT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.center_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem canon_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=centerWord X →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=(2*X).val ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧ EncodedCanonicalFrame origin (2*X) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  rw [centerWord_zero] at frame
  have c := hcorrect raw m (by rw [tgt_word]; exact frame.1)
    (target_clean hn origin hw hu _ _ _ frame)
  have pf : PairFrame ports.r ports.y origin (2*X).val 0 (run P m raw).basis :=
    PairFrame.update_temp ports.r ports.y origin raw.basis _ _ 0 _ (pair_dis hn) frame
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen ports.r ports.y (base 2312) (base 1026) origin _ (2*X).val 0 pf
    (by rw [ports_r,ports_y]; exact outside.1) (by rw [ports_r,ports_y]; exact outside.2) hr hy
  have split := port_split
  rw [←split.1,←split.2] at wide
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  refine ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),?_,actual.2⟩
  rw [ZMod.val_zero]
  exact wide


/-- Doubling exit conversion of the target port; the zero source port is
already canonical. -/
theorem canon_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s) :
    (run canonT m s).phase=s.phase ∧ EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  exact canon_frame_generic canonT canonT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.canonical_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem copy_raw (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (A B : Nat) (raw : State) (m : List Bool)
    (frame : PairFrame ports.r ports.y origin A B raw.basis) :
    (run copyN m raw).phase=raw.phase ∧
    PairFrame ports.r ports.y origin A (B ^^^ A) (run copyN m raw).basis := by
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none ports.r ports.y len
    (balancedSharedLayout_pairND base (base 2409) hn) (by simp) raw m
  refine ⟨phase,PairFrame.update_dst _ _ origin raw.basis _ A B _ (pair_dis hn) frame keep ?_⟩
  simpa only [copyValue,frame.1,frame.2.1] using value

/-- Duplicate the balanced target into the clean source. -/
theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin X X (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [centerWord_zero,Nat.zero_xor] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-- Clear the source against the equal balanced target. -/
theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin X X s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin X 0 (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [Nat.xor_self,←centerWord_zero] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-! The unchanged forward replay as a frame step. -/

private theorem replay_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)




private theorem groups_succ (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q) := by
  simp only [groupsPayload,if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false]

private theorem first_rest_payload (origin : BasisState) (Y : Fp) :
    groupsPayload true origin 1 169
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0))=
      PenultimateSwapIdentity.penultimatePayload origin Y := by
  have start : groupsPayload true origin 0 170 (2*Y,0)=
      groupsPayload true origin 1 169
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)) :=
    groups_succ origin 0 169 (2*Y,0)
  have generic : groupsPayload true origin 0 170 (2*Y,0)=
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*0) (3*170))) (2*Y,0) :=
    PenultimateMapped.forward_groups_payload 0 170 origin (2*Y,0)
  have zero : 3*0=0 := by decide
  have length : 3*170=510 := by decide
  have lettersEq : indexedLetters (3*0) (3*170)=indexedLetters 0 510 :=
    congrArg₂ indexedLetters zero length
  have lifted : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters (3*0) (3*170))) (2*Y,0)=
        skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
          (indexedLetters 0 510)) (2*Y,0) :=
    congrArg (fun ls : List MixedTranscriptLetter =>
      skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) ls) (2*Y,0)) lettersEq
  have fold : skywalkPayloadReplay (mixedTranscriptControls origin (base 2400)
      (indexedLetters 0 510)) (2*Y,0)=PenultimateSwapIdentity.penultimatePayload origin Y := by
    unfold PenultimateSwapIdentity.penultimatePayload
    rfl
  exact start.symm.trans (generic.trans (lifted.trans fold))

private theorem trim_split : trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have last : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [last] at split
  simpa only [Nat.zero_add,Nat.reduceAdd,trimLetters] using split

private theorem last_payload (origin : BasisState) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    directionalPayload (!true) (mixedTranscriptControls origin (base 2400) [tapeLetter 510])
      ((PenultimateSwapIdentity.penultimatePayload origin Y).1,
       (PenultimateSwapIdentity.penultimatePayload origin Y).2)=
      (if origin (base 2400) then Y/(x:Fp) else Y,if origin (base 2400) then Y/(x:Fp) else Y) := by
  have whole := trimLetters_quotient origin x Y hx0 hx trace
  rw [trim_split] at whole
  simp only [mixedTranscriptControls,List.map_append,replay_append] at whole
  simp only [directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,Prod.mk.eta,
    mixedTranscriptControls]
  rw [←whole]
  rfl

theorem replay_forward
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin Y 0 s) :
    (run (PenultimateMapped.replay true) m s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin (if origin (base 2400) then Y/(x:Fp) else Y)
        (if origin (base 2400) then Y/(x:Fp) else Y) (run (PenultimateMapped.replay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  let Q := skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (packetLetters 0)) (2*Y,0)
  let P : State → State → Prop := fun initial out => EncodedFieldFrame base (base 2409) origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedFieldFrame base (base 2409) origin Z Z out
  have all := run_three_states (EntryMappedFieldSegmentTrim.firstGroup true) (mappedGroups true 1 169)
    (renameProgram allPlaced (PenultimateSwapIdentity.cell true)) P (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      have a := EntryMappedFieldSegmentTrim.firstGroup_forward_step hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf 0 (by decide))
        origin hg0 hs0 env legal Y initial m1 hin
      rw [h1] at a
      have frame1 : EncodedFieldFrame base (base 2409) origin Q.1 Q.2 s1 := a.2
      have bAll := mappedGroups_frame true 1 169 (by decide) hn hlo ho hp
        (packet_layouts (base 2400) (base 2409) (base 2410) hf)
        origin hg0 hs0 env legal Q.1 Q.2 s1 m2 frame1
      have bPhase : (run (mappedGroups true 1 169) m2 s1).phase=s1.phase := bAll.2.1
      have bFrame : EncodedFieldFrame base (base 2409) origin
          (groupsPayload true origin 1 169 (Q.1,Q.2)).1
          (groupsPayload true origin 1 169 (Q.1,Q.2)).2
          (run (mappedGroups true 1 169) m2 s1) := bAll.2.2
      rw [h2] at bPhase bFrame
      have payload : groupsPayload true origin 1 169 (Q.1,Q.2)=A := by
        change groupsPayload true origin 1 169 Q=A
        exact first_rest_payload origin Y
      rw [payload] at bFrame
      have same := PenultimateMappedCellProof.forward_cell_eq hn hlo ho hp hf origin hg0 hs0 env legal
        A.1 A.2 s2 m3 m3 bFrame (PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace)
      have old := trimCell_step true hn hlo ho hp hf origin hg0 hs0 env legal A.1 A.2 s2 m3 bFrame
      rw [←same,h3,last_payload origin x Y hx0 hx trace] at old
      exact ⟨old.2.1.trans (bPhase.trans a.1),old.2.2⟩) s m
  have shape : PenultimateMapped.replay true=EntryMappedFieldSegmentTrim.firstGroup true++
      (mappedGroups true 1 169++renameProgram allPlaced (PenultimateSwapIdentity.cell true)) := by
    simp only [PenultimateMapped.replay,if_true,List.append_assoc]
  rw [shape]
  exact all input

/-! Complete segment contract. -/

private theorem run_four_states (a b c d : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 : State) (m1 m2 m3 m4 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → run d m4 s3=s4 → P s s4)
    (s : State) (m : List Bool) : P s (run (a++(b++(c++d))) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

private theorem double_half (Y W : Fp) : 2*(Y/2*W)=Y*W := by
  have two : (2:Fp)≠0 := by decide
  field_simp

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp)≠0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem double_half_one (Y : Fp) : 2*(Y/2)=Y := by
  have two : (2:Fp)≠0 := by decide
  exact mul_div_cancel₀ Y two

/-- Same hypotheses and conclusion as the protected selected field segment. -/
theorem segment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (segment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  cases divide
  · let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out
    have all := run_four_states centerT copyN (PenultimateMapped.replay false) canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := center_frame hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at c1
      have c2 := copy_fill hn origin (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := PenultimateMapped.replay_inverse_spec hn hlo ho hp hf origin hg0 hs0 env legal
        x (Y/2) hx0 hx trace s2 m3 c2.2
      rw [h3] at c3
      have c4 := canon_frame hn origin hw hu hr hy _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y := by
        unfold fieldResult
        split
        · simp only [Bool.false_eq_true,if_false]; exact double_half Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [segment,Bool.false_eq_true,if_false] using all input
  · let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out
    have all := run_four_states centerT (PenultimateMapped.replay true) copyN canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := center_frame hn origin hw hu hr hy Y initial m1 hin
      rw [h1] at c1
      have c2 := replay_forward hn hlo ho hp hf origin hg0 hs0 env legal x hx0 hx trace
        (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := copy_clear hn origin _ s2 m3 c2.2
      rw [h3] at c3
      have c4 := canon_frame hn origin hw hu hr hy _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2/(x:Fp) else Y/2)=fieldResult true origin x Y := by
        unfold fieldResult
        split
        · simp only [if_true]; exact double_half_div Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [segment,if_true] using all input

theorem segment_pool_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run (segment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (segment divide) m s).basis q=s.basis q := by
  have result := segment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (segment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

/-! Resources, support and physical form. -/

theorem segment_counts (divide : Bool) :
    toffoliCount (segment divide)=(if divide then 654498 else 655008) ∧
    measurementCount (segment divide)=523428 := by
  have c := HalfConvert.counts tgt (balancedSharedTargetConvert_widths base)
  have r := PenultimateMapped.replay_counts divide
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  have k := copyRegister_counts none ports.r ports.y len
  simp only [Option.isSome_none,Bool.false_eq_true,if_false] at k
  cases divide <;> simp only [segment,centerT,canonT,copyN,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,c.1,c.2.1,c.2.2.1,c.2.2.2,k.1,k.2] at r ⊢
  · rw [r.1,r.2]; norm_num
  · rw [r.1,r.2]; norm_num

theorem replay_sub (divide : Bool) :
    wires (PenultimateMapped.replay divide)⊆wires (PenultimateMapped.fieldSegment divide) := by
  intro q hq
  simp only [PenultimateMapped.fieldSegment,wires_append,Finset.mem_union]
  tauto

theorem segment_support (divide : Bool) : wires (segment divide)⊆slots.toFinset := by
  have rp := (replay_sub divide).trans (PenultimateMapped.fieldSegment_support divide)
  have ce := centerT_sites.trans ids_slots
  have ca := canonT_sites.trans ids_slots
  have co := copyN_sites.trans ids_slots
  cases divide <;> simp only [segment,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  · exact ⟨ce,co,rp,ca⟩
  · exact ⟨ce,rp,co,ca⟩

theorem segment_physical (divide : Bool) : GatePhysical (segment divide) := by
  have hn : (skywalkSharedWires base).Nodup := by
    apply List.Nodup.map_on
    · intro a _ b _ eq; exact base_injective eq
    · exact List.nodup_range'
  have h := HalfConvert.physical tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn)
  have cp : GatePhysical copyN :=
    copyRegister_physical none ports.r ports.y (balancedSharedLayout_pairND base (base 2409) hn) (by simp)
  have rp := penultimateReplay_physical divide
  cases divide <;> simp only [segment,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨h.1,cp,rp,h.2⟩
  · exact ⟨h.1,rp,cp,h.2⟩

end ECDSAAdd.Entrant.HalfField

end


-- ===== ECDSAAdd.Submission.Entrant.Codec5 =====
section

/-! Five legal two-bit trits, packed into eight bits by a gate-only permutation (12 Toffolis;
`decode` is its reverse). -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Codec5
open Arithmetic Challenge RecordedQuantum Baselines

/-- Pairs 0, 1 and 2 enter a four-Toffoli three-trit pack (found by a SAT search) whose image
lies in a hyperplane, re-encoded so that wire 5 is that hole and four of its spare codes form the
coordinate plane `A₂ = A₃ = A₄ = 0` of the packed word on wires 0..4. Two Toffolis store
`sign 3 = 0, sign 4 = 1` on the illegal `11` of pair 3, and for `sign 3 = sign 4 = 1` three
conditional swaps move `A₂, A₃, A₄` into pair 3 and the orientation of pair 4, so the packed word
lands on that spare plane; three Toffolis with wire 5 as clean ancilla then clear wire 9. -/
def encode : Program := [
  .CX 3 2,.CX 2 3,.CX 2 0,.CX 0 2,.CX 0 1,.CX 1 0,.X 1,.CCX 0 1 2,.X 1,.CX 1 0,.CX 0 1,.CX 0 2,
  .CX 2 0,.CX 2 3,.CX 3 2,.CX 4 3,.CX 4 2,.CX 3 1,.CX 2 1,.CX 2 0,.CX 1 3,.CX 0 4,.CX 0 3,
  .CX 0 2,.CX 2 0,.CCX 0 1 2,.CX 2 0,.CX 0 2,.CX 0 3,.CX 0 4,.CX 1 3,.CX 2 0,.CX 2 1,.CX 3 1,
  .CX 4 2,.CX 4 3,.CX 5 4,.CX 5 3,.CX 5 2,.CX 4 5,.CX 5 4,.CX 3 5,.CX 3 1,.CX 3 0,.CX 2 5,
  .CX 2 4,.CX 2 3,.CX 2 1,.CX 3 2,.CX 1 5,.CX 1 3,.CX 0 2,.CX 2 0,.X 1,.CCX 0 1 3,.X 1,.CX 2 0,
  .CX 0 2,.CX 1 3,.CX 1 5,.CX 3 2,.CX 2 1,.CX 2 3,.CX 2 4,.CX 2 5,.CX 3 0,.CX 3 1,.CX 3 5,
  .CX 5 4,.CX 4 5,.CX 5 3,.CX 4 5,.CX 5 4,.CX 3 1,.CX 2 5,.CX 2 3,.CX 2 1,.CX 2 0,.CX 1 5,
  .CX 1 4,.CX 1 3,.CX 1 2,.CX 1 0,.CX 2 1,.CX 0 5,.CX 0 4,.CX 0 2,.CX 2 0,.X 0,.CCX 0 1 2,.X 0,
  .CX 2 0,.CX 0 2,.CX 0 4,.CX 0 5,.CX 2 1,.CX 1 0,.CX 1 2,.CX 1 3,.CX 1 4,.CX 1 5,.CX 2 0,
  .CX 2 1,.CX 2 3,.CX 2 5,.CX 3 1,.CX 5 4,.CX 4 5,.CX 5 3,.CX 5 1,.CX 4 5,.CX 4 3,.CX 4 2,
  .CX 4 0,.CX 5 4,.CX 3 5,.CX 3 4,.CX 3 2,.CX 3 1,.CX 4 3,.CX 2 5,.CX 2 4,.CX 2 1,.CX 1 4,
  .CX 1 3,.CX 1 0,.CX 3 1,.CX 0 4,.CX 4 0,.X 2,.X 3,.X 4,.CX 9 7,.CX 8 6,.CX 7 9,.CX 9 7,
  .CX 6 8,.CCX 6 7 8,.CX 6 8,.CX 9 7,.CX 7 9,.CX 8 6,.CX 9 8,.CX 9 6,.CX 8 9,.CX 9 8,.CX 7 8,
  .CX 7 6,.CX 6 8,.CX 6 7,.CCX 6 7 8,.CX 6 7,.CX 6 8,.CX 7 6,.CX 7 8,.CX 9 8,.CX 8 9,.CX 9 8,
  .CX 6 9,.CX 9 6,.CX 6 2,.CCX 9 2 6,.CX 6 2,.CX 7 3,.CCX 9 3 7,.CX 7 3,.CX 8 4,.CCX 9 4 8,
  .CX 8 4,.X 2,.X 3,.X 4,.CCX 2 3 5,.CCX 5 4 9,.CCX 2 3 5,.X 2,.X 3,.X 4]

def decode : Program := encode.reverse

def pair (a b : Wire) (s : BasisState) : Nat := (s a).toNat+2*(s b).toNat

def legal (s : BasisState) : Prop := ∀i<5,pair (2*i) (2*i+1) s<3

theorem proper_phase (p : Program) (hp : ProperProgram p) (s : State) (m : List Bool) :
    (run p m s).phase=s.phase := by
  induction p generalizing s m with
  | nil => rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have ht : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i <;> simp only [ProperGate] at hi
    all_goals first | contradiction | exact ih ht _ _

theorem proper_encode : ProperProgram encode := by
  simp [ProperProgram,encode,ProperGate]

theorem support_exact : wires encode=Finset.range 10 ∧ wires decode=Finset.range 10 := by decide

theorem support : wires encode⊆Finset.range 10 ∧ wires decode⊆Finset.range 10 := by decide

private def physicalBool : Instr→Bool
  | .X _ => true
  | .CX a b => decide (a≠b)
  | .CCX a b c => decide (a≠b ∧ a≠c ∧ b≠c)
  | .measureX _ _ _ => false

private theorem physicalBool_spec (i : Instr) (h : physicalBool i=true) : PhysicalInstr (.gate i) := by
  cases i <;> simp_all [physicalBool,PhysicalInstr,ProperGate]

private theorem physical_of_all (p : Program) (h : p.all physicalBool=true) : GatePhysical p := by
  intro i hi
  exact physicalBool_spec i ((List.all_eq_true.mp h) i hi)

theorem physical : GatePhysical encode ∧ GatePhysical decode :=
  ⟨physical_of_all encode (by decide),physical_of_all decode (by decide)⟩

theorem counts : toffoliCount encode=12 ∧ measurementCount encode=0 ∧
    toffoliCount decode=12 ∧ measurementCount decode=0 := by decide

theorem slots : gateSlots encode=178 ∧ gateSlots decode=178 := by decide

theorem encode_phase (s : State) (m : List Bool) : (run encode m s).phase=s.phase :=
  proper_phase _ proper_encode s m

/-- Bitmask view of a basis state. -/
def bitsOf (x : Nat) : BasisState := fun q => x.testBit q

def bitStep : Instr → Nat → Nat
  | .X t, x => x ^^^ 2^t
  | .CX c t, x => if x.testBit c then x ^^^ 2^t else x
  | .CCX a b t, x => if x.testBit a && x.testBit b then x ^^^ 2^t else x
  | .measureX _ _ _, x => x

def bitRun : Program → Nat → Nat
  | [], x => x
  | i :: p, x => bitRun p (bitStep i x)

def gateOnly : Program → Bool
  | [] => true
  | .measureX _ _ _ :: _ => false
  | _ :: p => gateOnly p

theorem bitsOf_flip (x t : Nat) : bitsOf (x ^^^ 2^t) = writeBit (bitsOf x) t (!x.testBit t) := by
  funext q
  by_cases h : q = t
  · subst h
    simp [bitsOf, writeBit, Nat.testBit_xor]
  · simp [bitsOf, writeBit, Function.update_of_ne h, Nat.testBit_xor, Ne.symm h]

theorem bitsOf_keep (x t : Nat) : writeBit (bitsOf x) t (x.testBit t) = bitsOf x := by
  funext q
  by_cases h : q = t
  · subst h; simp [bitsOf, writeBit]
  · simp [writeBit, Function.update_of_ne h]

/-- A gate-only program acts on bitmask states exactly as `bitRun`. -/
theorem run_bits (p : Program) (hp : gateOnly p = true) (m : List Bool) (ph : Bool) (x : Nat) :
    (run p m ⟨ph, bitsOf x⟩).basis = bitsOf (bitRun p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t =>
      have hp' : gateOnly p = true := by simpa [gateOnly] using hp
      simp only [run, bitRun, bitStep]
      rw [show (!bitsOf x t) = !x.testBit t from rfl, ← bitsOf_flip]
      exact ih hp' _
    | CX c t =>
      have hp' : gateOnly p = true := by simpa [gateOnly] using hp
      simp only [run, bitRun, bitStep]
      cases hc : x.testBit c
      · rw [show (bitsOf x t ^^ bitsOf x c) = x.testBit t by simp [bitsOf, hc], bitsOf_keep]
        simpa using ih hp' x
      · rw [show (bitsOf x t ^^ bitsOf x c) = !x.testBit t by simp [bitsOf, hc], ← bitsOf_flip]
        simpa using ih hp' _
    | CCX a b t =>
      have hp' : gateOnly p = true := by simpa [gateOnly] using hp
      simp only [run, bitRun, bitStep]
      cases hab : (x.testBit a && x.testBit b)
      · rw [show (bitsOf x t ^^ (bitsOf x a && bitsOf x b)) = x.testBit t by
          simp [bitsOf, hab], bitsOf_keep]
        simpa using ih hp' x
      · rw [show (bitsOf x t ^^ (bitsOf x a && bitsOf x b)) = !x.testBit t by
          simp [bitsOf, hab], ← bitsOf_flip]
        simpa using ih hp' _
    | measureX t c₀ c₁ => simp [gateOnly] at hp

def pack10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Nat :=
  b0.toNat+2*b1.toNat+4*b2.toNat+8*b3.toNat+16*b4.toNat+32*b5.toNat+64*b6.toNat+
    128*b7.toNat+256*b8.toNat+512*b9.toNat

def raw (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : BasisState := fun q =>
  if q=0 then b0 else if q=1 then b1 else if q=2 then b2 else if q=3 then b3 else
  if q=4 then b4 else if q=5 then b5 else if q=6 then b6 else if q=7 then b7 else
  if q=8 then b8 else if q=9 then b9 else false

theorem pack10_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ q<10,
    (pack10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9).testBit q=raw b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 q := by
  decide +kernel

theorem pack10_lt : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    pack10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9<1024 := by
  decide +kernel

def legalNat (x : Nat) : Bool :=
  !(x.testBit 0 && x.testBit 1) && !(x.testBit 2 && x.testBit 3) && !(x.testBit 4 && x.testBit 5) &&
    !(x.testBit 6 && x.testBit 7) && !(x.testBit 8 && x.testBit 9)

/-- Both holes, checked on every legal ten-bit word. -/
theorem finite_holes : ∀ x<1024, legalNat x=true →
    (bitRun encode x).testBit 5=false ∧ (bitRun encode x).testBit 9=false := by
  decide +kernel

private theorem pair_false (a b : Bool) (h : a.toNat+2*b.toNat<3) : (a && b)=false := by
  cases a <;> cases b <;> simp_all

theorem encode_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run encode m s).phase=s.phase ∧ (run encode m s).basis 5=false ∧ (run encode m s).basis 9=false := by
  obtain ⟨x,hx⟩ : ∃ x,x=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4)
      (s.basis 5) (s.basis 6) (s.basis 7) (s.basis 8) (s.basis 9) := ⟨_,rfl⟩
  have tb (q : Nat) (hq : q<10) : x.testBit q=s.basis q := by
    rw [hx,pack10_bits _ _ _ _ _ _ _ _ _ _ q hq]
    interval_cases q <;> simp [raw]
  have hb : ∀ q∈Finset.range 10,s.basis q=bitsOf x q :=
    fun q hq => (tb q (Finset.mem_range.mp hq)).symm
  have agree := pool_run_agrees encode (Finset.range 10) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
  have bits := run_bits encode (by decide) m s.phase x
  have l0 : (s.basis 0 && s.basis 1)=false := pair_false _ _ (h 0 (by decide))
  have l1 : (s.basis 2 && s.basis 3)=false := pair_false _ _ (h 1 (by decide))
  have l2 : (s.basis 4 && s.basis 5)=false := pair_false _ _ (h 2 (by decide))
  have l3 : (s.basis 6 && s.basis 7)=false := pair_false _ _ (h 3 (by decide))
  have l4 : (s.basis 8 && s.basis 9)=false := pair_false _ _ (h 4 (by decide))
  have lx : legalNat x=true := by
    simp only [legalNat,tb 0 (by decide),tb 1 (by decide),tb 2 (by decide),tb 3 (by decide),
      tb 4 (by decide),tb 5 (by decide),tb 6 (by decide),tb 7 (by decide),tb 8 (by decide),
      tb 9 (by decide),l0,l1,l2,l3,l4,Bool.not_false,Bool.and_true]
  have holes := finite_holes x (hx ▸ pack10_lt _ _ _ _ _ _ _ _ _ _) lx
  refine ⟨encode_phase s m,?_,?_⟩
  · rw [agree.2 5 (by decide),bits]; exact holes.1
  · rw [agree.2 9 (by decide),bits]; exact holes.2



/-- Only the ten declared local ports are mapped. -/
def label (f : Fin 10→Wire) (q : Wire) : Wire := if h:q<10 then f ⟨q,h⟩ else q

def encodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) encode
def decodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) decode
def legalAt (f : Fin 10→Wire) (s : BasisState) : Prop := legal (fun q => s (label f q))

private theorem label_inj (f : Fin 10→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range 10,∀b∈Finset.range 10,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

private theorem instrSupport (p : Program) (i : Instr) (hi : i∈p) : i.wires⊆wires p := by
  induction p with
  | nil => simp at hi
  | cons j p ih =>
    rcases List.mem_cons.mp hi with rfl|h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

private theorem properRename (f : Wire→Wire) (p : Program) (hp : ProperProgram p)
    (hf : ∀a∈wires p,∀b∈wires p,f a=f b → a=b) : ProperProgram (renameProgram f p) := by
  intro j hj
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
  have h := hp i hi
  have hs := instrSupport p i hi
  cases i with
  | X a => trivial
  | CX a b =>
    change f a≠f b
    exact fun e => h (hf a (hs (by simp [Instr.wires])) b (hs (by simp [Instr.wires])) e)
  | CCX a b c =>
    change f a≠f c ∧ f b≠f c
    exact ⟨fun e => h.1 (hf a (hs (by simp [Instr.wires])) c (hs (by simp [Instr.wires])) e),
      fun e => h.2 (hf b (hs (by simp [Instr.wires])) c (hs (by simp [Instr.wires])) e)⟩
  | measureX _ _ _ => contradiction

private theorem label_image (f : Fin 10→Wire) :
    (Finset.range 10).image (label f)=Finset.univ.image f := by
  ext q
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨⟨i,hi⟩,by simpa only [label,dif_pos hi] using e⟩
  · rintro ⟨i,e⟩
    exact ⟨i.val,i.isLt,by simpa only [label,dif_pos i.isLt] using e⟩

theorem supportAt_exact (f : Fin 10→Wire) :
    wires (encodeAt f)=Finset.univ.image f ∧ wires (decodeAt f)=Finset.univ.image f := by
  simp only [encodeAt,decodeAt,renameProgram_support,support_exact.1,support_exact.2,label_image]
  exact ⟨trivial,trivial⟩

theorem supportAt (f : Fin 10→Wire) :
    wires (encodeAt f)⊆Finset.univ.image f ∧ wires (decodeAt f)⊆Finset.univ.image f := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem site_mem (f : Fin 10→Wire) (i : Fin 10) : f i∈wires (encodeAt f) := by
  rw [(supportAt_exact f).1]
  exact Finset.mem_image_of_mem f (Finset.mem_univ i)

theorem countsAt (f : Fin 10→Wire) : toffoliCount (encodeAt f)=12 ∧ measurementCount (encodeAt f)=0 ∧
    toffoliCount (decodeAt f)=12 ∧ measurementCount (decodeAt f)=0 := by
  simpa only [encodeAt,decodeAt,(renameProgram_counts (label f) encode).1,
    (renameProgram_counts (label f) encode).2,(renameProgram_counts (label f) decode).1,
    (renameProgram_counts (label f) decode).2] using counts

theorem slotsAt (f : Fin 10→Wire) : gateSlots (encodeAt f)=178 ∧ gateSlots (decodeAt f)=178 := by
  simpa only [encodeAt,decodeAt,rename_gateSlots] using slots

theorem physicalAt (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAt f) ∧ GatePhysical (decodeAt f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e) physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.2 ha) b (support.2 hb) e) physical.2⟩

theorem roundtripAt (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) : run (decodeAt f) mD (run (encodeAt f) mE s)=s := by
  have h := run_reverse_proper (encodeAt f)
    (properRename _ _ proper_encode (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e)) s mE mD
  simpa only [encodeAt,decodeAt,decode,renameProgram,List.map_reverse] using h

theorem encodeAt_phase (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) : (run (encodeAt f) m s).phase=s.phase :=
  proper_phase _ (properRename _ _ proper_encode
    (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e)) s m
















theorem encodeAt_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (run (encodeAt f) m s).phase=s.phase ∧
    (run (encodeAt f) m s).basis (f 5)=false ∧ (run (encodeAt f) m s).basis (f 9)=false := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have localResult := encode_correct t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  refine ⟨placed.1.trans localResult.1,?_,?_⟩
  · have e := (placed.2 5 (by decide)).trans localResult.2.1
    simpa only [label,dif_pos (show 5<10 by decide)] using e
  · have e := (placed.2 9 (by decide)).trans localResult.2.2
    simpa only [label,dif_pos (show 9<10 by decide)] using e

theorem legalAt_iff (f : Fin 10→Wire) (s : BasisState) : legalAt f s ↔
    ∀i : Fin 5,(s (f ⟨2*i.val,by omega⟩) && s (f ⟨2*i.val+1,by omega⟩))=false := by
  have key (a b : Bool) : a.toNat+2*b.toNat<3 ↔ (a&&b)=false := by cases a <;> cases b <;> decide
  constructor
  · intro h i
    apply (key _ _).mp
    simpa only [pair,label,dif_pos (show 2*i.val<10 by omega),
      dif_pos (show 2*i.val+1<10 by omega)] using h i.val i.isLt
  · intro h
    change ∀i<5,pair (2*i) (2*i+1) (fun q => s (label f q))<3
    intro i hi
    have hb0 : 2*i<10 := Nat.mul_lt_mul_of_pos_left hi (by decide : 0<2)
    have hle : 2*i+2≤10 := by
      simpa only [Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hi)
    have hb1 : 2*i+1<10 := Nat.lt_of_lt_of_le (Nat.lt_succ_self (2*i+1)) hle
    have k := (key _ _).mpr (h ⟨i,hi⟩)
    simpa only [pair,label,dif_pos hb0,dif_pos hb1] using k

end ECDSAAdd.Entrant.Codec5

end


-- ===== Measured five-trit codec =====
section

/-! A phase-corrected measured encoder and decoder for five legal trits.
The finite safety predicate checks each measurement correction on the actual
running bitmask, then lifts that check to every phase and record tape. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.MeasuredCodec5
open Arithmetic Challenge RecordedQuantum Baselines
def encode : Program := [
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 0,
  .X 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 1,
  .CX 4 3,
  .CX 3 4,
  .CX 4 3,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 1 3,
  .CX 1 0,
  .CX 2 1,
  .CX 1 2,
  .CX 2 1,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .X 0,
  .CCX 0 1 2,
  .X 0,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 2 1,
  .CX 1 2,
  .CX 2 1,
  .CX 1 0,
  .CX 1 3,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 3,
  .CX 3 4,
  .CX 4 3,
  .CX 4 1,
  .CX 3 2,
  .CX 2 5,
  .CX 2 1,
  .CX 1 5,
  .CX 1 2,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 0,
  .X 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 1 2,
  .CX 1 5,
  .CX 2 1,
  .CX 2 5,
  .CX 3 2,
  .CX 2 3,
  .CX 4 3,
  .X 3,
  .CX 3 0,
  .CX 3 1,
  .measureX 3 [] [.CZ 4 2],
  .CX 0 2,
  .CX 1 2,
  .X 2,
  .CX 0 4,
  .CX 0 5,
  .CX 1 5,
  .X 5,
  .CX 0 2,
  .CX 2 0,
  .CX 0 2,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 6 8,
  .CCX 6 8 5,
  .CX 7 9,
  .CCX 5 9 7,
  .CX 7 9,
  .CX 5 9,
  .CX 5 6,
  .measureX 5 [] [.CZ 8 9],
  .CX 0 7,
  .CCX 6 7 0,
  .CX 0 7,
  .CX 3 8,
  .CCX 6 8 3,
  .CX 3 8,
  .CX 4 9,
  .CCX 6 9 4,
  .CX 4 9,
  .CX 6 0,
  .CX 6 3,
  .CX 6 4,
  .CCX 0 3 5,
  .measureX 6 [] [.CZ 5 4],
  .measureX 5 [] [.CZ 0 3],
  .CX 6 9,
  .CX 9 6,
  .CX 6 9]
def decode : Program := [
  .CX 6 9,
  .CX 9 6,
  .CX 6 9,
  .CCX 0 3 5,
  .CCX 5 4 6,
  .measureX 5 [] [.CZ 0 3],
  .CX 6 0,
  .CX 6 3,
  .CX 6 4,
  .CX 0 7,
  .CCX 6 7 0,
  .CX 0 7,
  .CX 3 8,
  .CCX 6 8 3,
  .CX 3 8,
  .CX 4 9,
  .CCX 6 9 4,
  .CX 4 9,
  .CCX 8 9 5,
  .CX 5 6,
  .CX 5 9,
  .CX 7 9,
  .CCX 5 9 7,
  .CX 7 9,
  .measureX 5 [] [.CZ 6 8],
  .CX 6 8,
  .CX 0 1,
  .CX 1 0,
  .CX 0 1,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 0 2,
  .CX 1 2,
  .X 2,
  .CX 0 4,
  .CX 0 5,
  .CX 1 5,
  .X 5,
  .CCX 4 2 3,
  .CX 3 0,
  .CX 3 1,
  .X 3,
  .CX 4 3,
  .CX 2 3,
  .CX 3 2,
  .CX 2 5,
  .CX 2 1,
  .CX 1 5,
  .CX 1 2,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 0,
  .X 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 1 2,
  .CX 1 5,
  .CX 2 1,
  .CX 2 5,
  .CX 3 2,
  .CX 4 1,
  .CX 4 3,
  .CX 3 4,
  .CX 4 3,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 1 3,
  .CX 1 0,
  .CX 2 1,
  .CX 1 2,
  .CX 2 1,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .X 0,
  .CCX 0 1 2,
  .X 0,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 2 1,
  .CX 1 2,
  .CX 2 1,
  .CX 1 0,
  .CX 1 3,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 3,
  .CX 3 4,
  .CX 4 3,
  .CX 4 1,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 0,
  .X 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4]
def pair (a b : Wire) (s : BasisState) : Nat := (s a).toNat+2*(s b).toNat

def legal (s : BasisState) : Prop := ∀i<5,pair (2*i) (2*i+1) s<3

theorem support_exact : wires encode=Finset.range 10 ∧ wires decode=Finset.range 10 := by decide

theorem support : wires encode⊆Finset.range 10 ∧ wires decode⊆Finset.range 10 := by decide

private def physicalBool : Instr→Bool
  | .X _ => true
  | .CX a b => decide (a≠b)
  | .CCX a b c => decide (a≠b ∧ a≠c ∧ b≠c)
  | .measureX _ _ _ => true

private theorem physicalBool_spec (i : Instr) (h : physicalBool i=true) : PhysicalInstr (.gate i) := by
  cases i <;> simp_all [physicalBool,PhysicalInstr,ProperGate]

private theorem physical_of_all (p : Program) (h : p.all physicalBool=true) : GatePhysical p := by
  intro i hi
  exact physicalBool_spec i ((List.all_eq_true.mp h) i hi)

theorem physical : GatePhysical encode ∧ GatePhysical decode :=
  ⟨physical_of_all encode (by decide),physical_of_all decode (by decide)⟩

theorem counts : toffoliCount encode=9 ∧ measurementCount encode=4 ∧
    toffoliCount decode=11 ∧ measurementCount decode=2 := by decide

theorem slots : gateSlots encode=142 ∧ gateSlots decode=140 := by decide

/-- Bitmask view of a basis state. -/
def bitsOf (x : Nat) : BasisState := fun q => x.testBit q

theorem bitsOf_flip (x t : Nat) : bitsOf (x ^^^ 2^t) = writeBit (bitsOf x) t (!x.testBit t) := by
  funext q
  by_cases h : q = t
  · subst h
    simp [bitsOf, writeBit, Nat.testBit_xor]
  · simp [bitsOf, writeBit, Function.update_of_ne h, Nat.testBit_xor, Ne.symm h]

theorem bitsOf_keep (x t : Nat) : writeBit (bitsOf x) t (x.testBit t) = bitsOf x := by
  funext q
  by_cases h : q = t
  · subst h; simp [bitsOf, writeBit]
  · simp [writeBit, Function.update_of_ne h]

def clear (x t : Nat) : Nat := if x.testBit t then x ^^^ 2^t else x

theorem bitsOf_clear (x t : Nat) : bitsOf (clear x t)=writeBit (bitsOf x) t false := by
  unfold clear
  cases h : x.testBit t
  · simpa only [h,Bool.false_eq_true,if_false] using (bitsOf_keep x t).symm
  · simpa only [h,if_true,Bool.not_true] using bitsOf_flip x t

def corrSim : List Correction → Bool → Nat → Bool
  | [], ph, _ => ph
  | .Z t::cs, ph, x => corrSim cs (ph ^^ x.testBit t) x
  | .CZ a b::cs, ph, x => corrSim cs (ph ^^ (x.testBit a && x.testBit b)) x

def sim : Program → List Bool → Bool → Nat → Bool × Nat
  | [], _, ph, x => (ph,x)
  | .X t::p, m, ph, x => sim p m ph (x ^^^ 2^t)
  | .CX c t::p, m, ph, x => sim p m ph (if x.testBit c then x ^^^ 2^t else x)
  | .CCX a b t::p, m, ph, x => sim p m ph (if x.testBit a && x.testBit b then x ^^^ 2^t else x)
  | .measureX t cs0 cs1::p, m, ph, x => sim p m.tail
      (corrSim (if m.headD false then cs1 else cs0) (ph ^^ (m.headD false && x.testBit t)) (clear x t))
      (clear x t)

theorem correct_sim (cs : List Correction) (ph : Bool) (x : Nat) :
    correct cs ⟨ph,bitsOf x⟩=⟨corrSim cs ph x,bitsOf x⟩ := by
  induction cs generalizing ph with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [correct,corrSim,bitsOf] <;> exact ih _

theorem run_sim (p : Program) (m : List Bool) (ph : Bool) (x : Nat) :
    run p m ⟨ph,bitsOf x⟩=⟨(sim p m ph x).1,bitsOf (sim p m ph x).2⟩ := by
  induction p generalizing x m ph with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t =>
      simp only [run,sim]
      rw [show (!bitsOf x t) = !x.testBit t from rfl,←bitsOf_flip]
      exact ih _ _ _
    | CX c t =>
      simp only [run,sim]
      cases hc : x.testBit c
      · rw [show (bitsOf x t ^^ bitsOf x c)=x.testBit t by simp [bitsOf,hc],bitsOf_keep]
        simpa only [hc,Bool.false_eq_true,if_false] using ih m ph x
      · rw [show (bitsOf x t ^^ bitsOf x c)=!x.testBit t by simp [bitsOf,hc],←bitsOf_flip]
        simpa only [hc,if_true] using ih m ph (x ^^^ 2^t)
    | CCX a b t =>
      simp only [run,sim]
      cases hc : (x.testBit a && x.testBit b)
      · rw [show (bitsOf x t ^^ (bitsOf x a && bitsOf x b))=x.testBit t by simp [bitsOf,hc],bitsOf_keep]
        simpa only [hc,Bool.false_eq_true,if_false] using ih m ph x
      · rw [show (bitsOf x t ^^ (bitsOf x a && bitsOf x b))= !x.testBit t by simp [bitsOf,hc],←bitsOf_flip]
        simpa only [hc,if_true] using ih m ph (x ^^^ 2^t)
    | measureX t cs0 cs1 =>
      simp only [run,sim,measureAndCorrect]
      rw [←bitsOf_clear,correct_sim]
      exact ih _ _ _

def pack10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Nat :=
  b0.toNat+2*b1.toNat+4*b2.toNat+8*b3.toNat+16*b4.toNat+32*b5.toNat+64*b6.toNat+
    128*b7.toNat+256*b8.toNat+512*b9.toNat

def raw (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : BasisState := fun q =>
  if q=0 then b0 else if q=1 then b1 else if q=2 then b2 else if q=3 then b3 else
  if q=4 then b4 else if q=5 then b5 else if q=6 then b6 else if q=7 then b7 else
  if q=8 then b8 else if q=9 then b9 else false

theorem pack10_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ q<10,
    (pack10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9).testBit q=raw b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 q := by
  decide +kernel

theorem pack10_lt : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    pack10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9<1024 := by
  decide +kernel

def legalNat (x : Nat) : Bool :=
  !(x.testBit 0 && x.testBit 1) && !(x.testBit 2 && x.testBit 3) && !(x.testBit 4 && x.testBit 5) &&
    !(x.testBit 6 && x.testBit 7) && !(x.testBit 8 && x.testBit 9)

def bitStep : Instr → Nat → Nat
  | .X t, x => x ^^^ 2^t
  | .CX c t, x => if x.testBit c then x ^^^ 2^t else x
  | .CCX a b t, x => if x.testBit a && x.testBit b then x ^^^ 2^t else x
  | .measureX t _ _, x => clear x t

def bitRun : Program → Nat → Nat
  | [], x => x
  | i::p, x => bitRun p (bitStep i x)

def safeStep : Instr → Nat → Bool
  | .measureX t c0 c1, x =>
      (corrSim c0 false (clear x t)==false) && (corrSim c1 false (clear x t)==x.testBit t)
  | _, _ => true

def safe : Program → Nat → Bool
  | [], _ => true
  | i::p, x => safeStep i x && safe p (bitStep i x)

theorem corrSim_xor (cs : List Correction) (ph : Bool) (x : Nat) :
    corrSim cs ph x=(ph ^^ corrSim cs false x) := by
  induction cs generalizing ph with
  | nil => simp [corrSim]
  | cons c cs ih =>
    cases c <;> simp only [corrSim] <;>
      rw [ih,ih (false ^^ _)] <;> simp [Bool.xor_assoc]

theorem sim_safe (p : Program) (x : Nat) (h : safe p x=true) (m : List Bool) (ph : Bool) :
    sim p m ph x=(ph,bitRun p x) := by
  induction p generalizing x m ph with
  | nil => rfl
  | cons i p ih =>
    have hh : safeStep i x=true ∧ safe p (bitStep i x)=true := by
      simpa only [safe,Bool.and_eq_true] using h
    cases i with
    | X t => exact ih _ hh.2 _ _
    | CX c t => exact ih _ hh.2 _ _
    | CCX a b t => exact ih _ hh.2 _ _
    | measureX t c0 c1 =>
      have hs : corrSim c0 false (clear x t)=false ∧ corrSim c1 false (clear x t)=x.testBit t := by
        simpa only [safeStep,Bool.and_eq_true,beq_iff_eq] using hh.1
      have neutral : corrSim (if m.headD false then c1 else c0)
          (ph ^^ (m.headD false && x.testBit t)) (clear x t)=ph := by
        cases hm : m.headD false
        · simp only [hm,Bool.false_eq_true,if_false,Bool.false_and,Bool.xor_false]
          rw [corrSim_xor,hs.1]; simp
        · simp only [hm,if_true,Bool.true_and]
          rw [corrSim_xor,hs.2]; simp [Bool.xor_assoc]
      simp only [sim,neutral]
      exact ih _ hh.2 _ _

theorem finite_encode : ∀ x<1024, legalNat x=true →
    safe encode x=true ∧ (bitRun encode x).testBit 5=false ∧ (bitRun encode x).testBit 9=false := by
  decide +kernel

theorem finite_decode : ∀ x<1024, legalNat x=true →
    safe decode (bitRun encode x)=true ∧ bitRun decode (bitRun encode x)=x := by
  decide +kernel
private theorem pair_false (a b : Bool) (h : a.toNat+2*b.toNat<3) : (a && b)=false := by
  cases a <;> cases b <;> simp_all

theorem local_word (s : State) (h : legal s.basis) :
    ∃ x, x<1024 ∧ legalNat x=true ∧ ∀q∈Finset.range 10,s.basis q=bitsOf x q := by
  let x := pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4)
      (s.basis 5) (s.basis 6) (s.basis 7) (s.basis 8) (s.basis 9)
  have tb (q : Nat) (hq : q<10) : x.testBit q=s.basis q := by
    rw [show x=pack10 (s.basis 0) (s.basis 1) (s.basis 2) (s.basis 3) (s.basis 4)
      (s.basis 5) (s.basis 6) (s.basis 7) (s.basis 8) (s.basis 9) from rfl,
      pack10_bits _ _ _ _ _ _ _ _ _ _ q hq]
    interval_cases q <;> simp [raw]
  have l0 := pair_false _ _ (h 0 (by decide))
  have l1 := pair_false _ _ (h 1 (by decide))
  have l2 := pair_false _ _ (h 2 (by decide))
  have l3 := pair_false _ _ (h 3 (by decide))
  have l4 := pair_false _ _ (h 4 (by decide))
  refine ⟨x,pack10_lt _ _ _ _ _ _ _ _ _ _,?_,fun q hq => (tb q (Finset.mem_range.mp hq)).symm⟩
  simp only [legalNat,tb 0 (by decide),tb 1 (by decide),tb 2 (by decide),tb 3 (by decide),
    tb 4 (by decide),tb 5 (by decide),tb 6 (by decide),tb 7 (by decide),tb 8 (by decide),
    tb 9 (by decide),l0,l1,l2,l3,l4,Bool.not_false,Bool.and_true]

theorem encode_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run encode m s).phase=s.phase ∧ (run encode m s).basis 5=false ∧ (run encode m s).basis 9=false := by
  obtain ⟨x,hx,lx,hb⟩ := local_word s h
  have agree := pool_run_agrees encode (Finset.range 10) support.1 m s ⟨s.phase,bitsOf x⟩ rfl hb
  have finite := finite_encode x hx lx
  have modeled := run_sim encode m s.phase x
  rw [sim_safe encode x finite.1 m s.phase] at modeled
  refine ⟨agree.1.trans ?_,(agree.2 5 (by decide)).trans ?_,(agree.2 9 (by decide)).trans ?_⟩
  · rw [modeled]
  · rw [modeled]; exact finite.2.1
  · rw [modeled]; exact finite.2.2

theorem encode_independent (s : State) (m n : List Bool) (h : legal s.basis) :
    run encode m s=run encode n s := by
  exact State.extensionality _ _ ((encode_correct s m h).1.trans (encode_correct s n h).1.symm)
    (run_basis_records _ s s m n rfl)

theorem roundtrip (s : State) (mE mD : List Bool) (h : legal s.basis) :
    run decode mD (run encode mE s)=s := by
  obtain ⟨x,hx,lx,hb⟩ := local_word s h
  let t : State := ⟨s.phase,bitsOf x⟩
  have pp := pool_run_agrees encode (Finset.range 10) support.1 mE s t rfl hb
  have dd := pool_run_agrees decode (Finset.range 10) support.2 mD
    (run encode mE s) (run encode mE t) pp.1 pp.2
  have localInv : run decode mD (run encode mE t)=t := by
    have fe := finite_encode x hx lx
    have fd := finite_decode x hx lx
    dsimp only [t]
    rw [run_sim,sim_safe encode x fe.1,run_sim,sim_safe decode _ fd.1,fd.2]
  apply State.extensionality
  · have hp := congrArg State.phase localInv
    exact dd.1.trans hp
  · funext q
    by_cases hq : q∈Finset.range 10
    · exact (dd.2 q hq).trans ((congrArg (fun st : State => st.basis q) localInv).trans (hb q hq).symm)
    · exact (run_preserves_outside decode mD (run encode mE s) q (fun h => hq (support.2 h))).trans
        (run_preserves_outside encode mE s q (fun h => hq (support.1 h)))
/-- Only the ten declared local ports are mapped. -/
def label (f : Fin 10→Wire) (q : Wire) : Wire := if h:q<10 then f ⟨q,h⟩ else q

def encodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) encode
def decodeAt (f : Fin 10→Wire) : Program := renameProgram (label f) decode
def legalAt (f : Fin 10→Wire) (s : BasisState) : Prop := legal (fun q => s (label f q))

private theorem label_inj (f : Fin 10→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range 10,∀b∈Finset.range 10,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

private theorem label_image (f : Fin 10→Wire) :
    (Finset.range 10).image (label f)=Finset.univ.image f := by
  ext q
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨⟨i,hi⟩,by simpa only [label,dif_pos hi] using e⟩
  · rintro ⟨i,e⟩
    exact ⟨i.val,i.isLt,by simpa only [label,dif_pos i.isLt] using e⟩

theorem supportAt_exact (f : Fin 10→Wire) :
    wires (encodeAt f)=Finset.univ.image f ∧ wires (decodeAt f)=Finset.univ.image f := by
  simp only [encodeAt,decodeAt,renameProgram_support,support_exact.1,support_exact.2,label_image]
  exact ⟨trivial,trivial⟩

theorem supportAt (f : Fin 10→Wire) :
    wires (encodeAt f)⊆Finset.univ.image f ∧ wires (decodeAt f)⊆Finset.univ.image f := by
  rw [(supportAt_exact f).1,(supportAt_exact f).2]
  exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩

theorem site_mem (f : Fin 10→Wire) (i : Fin 10) : f i∈wires (encodeAt f) := by
  rw [(supportAt_exact f).1]
  exact Finset.mem_image_of_mem f (Finset.mem_univ i)

theorem countsAt (f : Fin 10→Wire) : toffoliCount (encodeAt f)=9 ∧ measurementCount (encodeAt f)=4 ∧
    toffoliCount (decodeAt f)=11 ∧ measurementCount (decodeAt f)=2 := by
  simpa only [encodeAt,decodeAt,(renameProgram_counts (label f) encode).1,
    (renameProgram_counts (label f) encode).2,(renameProgram_counts (label f) decode).1,
    (renameProgram_counts (label f) decode).2] using counts

theorem slotsAt (f : Fin 10→Wire) : gateSlots (encodeAt f)=142 ∧ gateSlots (decodeAt f)=140 := by
  simpa only [encodeAt,decodeAt,rename_gateSlots] using slots

theorem physicalAt (f : Fin 10→Wire) (hf : Function.Injective f) :
    GatePhysical (encodeAt f) ∧ GatePhysical (decodeAt f) := by
  exact ⟨gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.1 ha) b (support.1 hb) e) physical.1,
    gatePhysical_rename_support _ _
    (fun a ha b hb e => label_inj f hf a (support.2 ha) b (support.2 hb) e) physical.2⟩

theorem encodeAt_correct (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) :
    (run (encodeAt f) m s).phase=s.phase ∧
    (run (encodeAt f) m s).basis (f 5)=false ∧ (run (encodeAt f) m s).basis (f 9)=false := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have localResult := encode_correct t m h
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 m t s rfl (fun _ _ => rfl)
  refine ⟨placed.1.trans localResult.1,?_,?_⟩
  · have e := (placed.2 5 (by decide)).trans localResult.2.1
    simpa only [label,dif_pos (show 5<10 by decide)] using e
  · have e := (placed.2 9 (by decide)).trans localResult.2.2
    simpa only [label,dif_pos (show 9<10 by decide)] using e

theorem legalAt_iff (f : Fin 10→Wire) (s : BasisState) : legalAt f s ↔
    ∀i : Fin 5,(s (f ⟨2*i.val,by omega⟩) && s (f ⟨2*i.val+1,by omega⟩))=false := by
  have key (a b : Bool) : a.toNat+2*b.toNat<3 ↔ (a&&b)=false := by cases a <;> cases b <;> decide
  constructor
  · intro h i
    apply (key _ _).mp
    simpa only [pair,label,dif_pos (show 2*i.val<10 by omega),
      dif_pos (show 2*i.val+1<10 by omega)] using h i.val i.isLt
  · intro h
    change ∀i<5,pair (2*i) (2*i+1) (fun q => s (label f q))<3
    intro i hi
    have hb0 : 2*i<10 := Nat.mul_lt_mul_of_pos_left hi (by decide : 0<2)
    have hle : 2*i+2≤10 := by
      simpa only [Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hi)
    have hb1 : 2*i+1<10 := Nat.lt_of_lt_of_le (Nat.lt_succ_self (2*i+1)) hle
    have k := (key _ _).mpr (h ⟨i,hi⟩)
    simpa only [pair,label,dif_pos hb0,dif_pos hb1] using k

theorem encodeAt_phase (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legalAt f s.basis) : (run (encodeAt f) m s).phase=s.phase :=
  (encodeAt_correct f hf s m h).1

theorem encodeAt_independent (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (h : legalAt f s.basis) :
    run (encodeAt f) m s=run (encodeAt f) n s := by
  apply State.extensionality
  · exact (encodeAt_phase f hf s m h).trans (encodeAt_phase f hf s n h).symm
  · exact run_basis_records _ s s m n rfl

theorem roundtripAt (f : Fin 10→Wire) (hf : Function.Injective f)
    (s : State) (mE mD : List Bool) (h : legalAt f s.basis) :
    run (decodeAt f) mD (run (encodeAt f) mE s)=s := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have pe := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 mE t s rfl (fun _ _ => rfl)
  have pd := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) decode
    support.2 mD (run encode mE t) (run (encodeAt f) mE s) pe.1.symm
    (fun q hq => (pe.2 q hq).symm)
  have inv := roundtrip t mE mD h
  apply State.extensionality
  · have hp := congrArg State.phase inv
    exact pd.1.trans hp
  · funext q
    by_cases hq : q∈Finset.univ.image f
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      have eq := (pd.2 i.val (Finset.mem_range.mpr i.isLt)).trans
        (congrArg (fun st : State => st.basis i.val) inv)
      simpa only [t,label,dif_pos i.isLt] using eq
    · exact (run_preserves_outside (decodeAt f) mD (run (encodeAt f) mE s) q
        (fun used => hq ((supportAt f).2 used))).trans
        (run_preserves_outside (encodeAt f) mE s q (fun used => hq ((supportAt f).1 used)))

def zeroNeutral : Program → Bool
  | [] => true
  | .measureX _ [] _::p => zeroNeutral p
  | .measureX _ (_::_) _::_ => false
  | _::p => zeroNeutral p

theorem zero_phase (p : Program) (h : zeroNeutral p=true) (s : State) :
    (run p [] s).phase=s.phase := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => exact ih h _
    | CX c t => exact ih h _
    | CCX a b t => exact ih h _
    | measureX t c0 c1 =>
      cases c0 with
      | nil => simpa only [run,measureAndCorrect,List.headD_nil,List.tail_nil,if_false,correct,
          Bool.false_and,Bool.xor_false] using ih h (⟨s.phase,writeBit s.basis t false⟩ : State)
      | cons c cs => simp [zeroNeutral] at h

theorem encodeAt_zero_phase (f : Fin 10→Wire) (hf : Function.Injective f) (s : State) :
    (run (encodeAt f) [] s).phase=s.phase := by
  let t : State := ⟨s.phase,fun q => s.basis (label f q)⟩
  have placed := run_rename_pool (label f) (Finset.range 10) (label_inj f hf) encode
    support.1 [] t s rfl (fun _ _ => rfl)
  exact placed.1.trans (zero_phase encode (by decide) t)

end ECDSAAdd.Entrant.MeasuredCodec5

end



-- ===== ECDSAAdd.Submission.Entrant.History5 =====
section

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.History5
open Arithmetic Secp256k1
attribute [local irreducible] run wires toffoliCount measurementCount

def historyId (start : Nat) (q : Fin 10) : Nat :=
  if q.val%2=0 then start+q.val/2 else 1028+start+q.val/2

def historyMap (w : Nat → Wire) (start : Nat) : Fin 10 → Wire := fun q => w (historyId start q)

def HistoryAbove (w : Nat → Wire) : Prop :=
  ∀j,(j<512 ∨ (1028≤j ∧ j<1540)) → 10≤w j

theorem historyId_region (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    historyId start q<512 ∨ (1028≤historyId start q ∧ historyId start q<1540) := by
  have hq := q.isLt
  unfold historyId
  split <;> omega

theorem historyId_bound (start : Nat) (hs : start+5≤512) (q : Fin 10) : historyId start q<1798 := by
  have h := historyId_region start hs q
  omega

theorem historyMap_injective (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) : Function.Injective (historyMap w start) := by
  intro a b eq
  have ids := skywalkPool_index_inj w hn _ _
    (historyId_bound start hs a) (historyId_bound start hs b) eq
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  unfold historyId at ids
  split_ifs at ids <;> omega





def encode (w : Nat → Wire) (start : Nat) : Program := MeasuredCodec5.encodeAt (historyMap w start)

def decode (w : Nat → Wire) (start : Nat) : Program := MeasuredCodec5.decodeAt (historyMap w start)


def packDue (i : Nat) : Bool := decide (5 ≤ i ∧ i % 5 = 0)
def packAfter (w : Nat → Wire) (i : Nat) : Program := if packDue i then encode w (i-5) else []
def decodeBefore (w : Nat → Wire) (i : Nat) : Program := if packDue i then decode w (i-5) else []

def encodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => encodePrefix w n++packAfter w n
def decodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => decodeBefore w n++decodePrefix w n

def allEncode (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => allEncode w n++encode w (5*n)




def decodeRange (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => decodeRange w (i+1) n++decodeBefore w i

def RawLegal (w : Nat → Wire) (n : Nat) (s : BasisState) : Prop :=
  ∀j,j<n → MeasuredCodec5.legalAt (historyMap w (5*j)) s


theorem packDue_true (i : Nat) (h : packDue i=true) : 5 ≤ i ∧ i % 5 = 0 := by
  simpa only [packDue,decide_eq_true_eq] using h

theorem encode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (encode w start)=9 ∧ measurementCount (encode w start)=4 := by
  have h := MeasuredCodec5.countsAt (historyMap w start)
  exact ⟨h.1,h.2.1⟩


theorem decode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (decode w start)=11 ∧ measurementCount (decode w start)=2 := by
  have h := MeasuredCodec5.countsAt (historyMap w start)
  exact h.2.2


theorem encode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase :=
  MeasuredCodec5.encodeAt_phase _ (historyMap_injective w hn start hs) s m legal







theorem encode_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) : GatePhysical (encode w start) :=
  (MeasuredCodec5.physicalAt _ (historyMap_injective w hn start hs)).1


theorem decode_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) : GatePhysical (decode w start) :=
  (MeasuredCodec5.physicalAt _ (historyMap_injective w hn start hs)).2


theorem codec_slots (w : Nat → Wire) (start : Nat) :
    Challenge.gateSlots (encode w start)=142 ∧ Challenge.gateSlots (decode w start)=140 :=
  MeasuredCodec5.slotsAt _


theorem encode_correct (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase ∧
      (run (encode w start) m s).basis (historyMap w start 5)=false ∧
      (run (encode w start) m s).basis (historyMap w start 9)=false :=
  MeasuredCodec5.encodeAt_correct _ (historyMap_injective w hn start hs) s m legal


theorem packAfter_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (packAfter w i)=9*(if packDue i then 1 else 0) ∧
    measurementCount (packAfter w i)=4*(if packDue i then 1 else 0) ∧
    toffoliCount (decodeBefore w i)=11*(if packDue i then 1 else 0) ∧
    measurementCount (decodeBefore w i)=2*(if packDue i then 1 else 0) := by
  have e := encode_counts w (i-5)
  have d := decode_counts w (i-5)
  cases due : packDue i
  · simp only [packAfter,decodeBefore,due,Bool.false_eq_true,if_false,
      toffoliCount,measurementCount,Nat.mul_zero]
    exact ⟨True.intro,True.intro,True.intro,True.intro⟩
  · simp only [packAfter,decodeBefore,due,if_true,Nat.mul_one]
    exact ⟨e.1,e.2,d.1,d.2⟩


theorem history_gate_mem (w : Nat → Wire) (start : Nat) (p : Program)
    (hp : p=encode w start ∨ p=decode w start) (q : Wire) (hq : q∈wires p) :
    ∃i:Fin 10,q=historyMap w start i := by
  have sub := MeasuredCodec5.supportAt (historyMap w start)
  have member : q∈Finset.univ.image (historyMap w start) := by
    rcases hp with rfl|rfl
    · exact sub.1 hq
    · exact sub.2 hq
  obtain ⟨i,_,eq⟩ := Finset.mem_image.mp member
  exact ⟨i,eq.symm⟩


theorem history_site_mem (w : Nat → Wire) (start : Nat) (q : Fin 10) :
    historyMap w start q∈wires (encode w start) := MeasuredCodec5.site_mem _ q


theorem windows_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a b : Nat) (ha : a+5≤512) (hb : b+5≤512) (hab : a+5≤b) :
    Disjoint (wires (encode w a)) (wires (encode w b)) := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  obtain ⟨i,hi⟩ := history_gate_mem w a _ (Or.inl rfl) q hqa
  obtain ⟨j,hj⟩ := history_gate_mem w b _ (Or.inl rfl) q hqb
  have eq := skywalkPool_index_inj w hn _ _ (historyId_bound a ha i)
    (historyId_bound b hb j) (hi.symm.trans hj)
  have hia := i.isLt
  have hjb := j.isLt
  unfold historyMap at eq
  unfold historyId at eq
  split_ifs at eq <;> omega






































theorem prefix_next_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : packDue n=true) :
    Disjoint (wires (encodePrefix w n)) (wires (encode w (n-5))) := by
  have nd := packDue_true n due
  have go : ∀k,k≤n → Disjoint (wires (encodePrefix w k)) (wires (encode w (n-5))) := by
    intro k hk
    induction k with
    | zero => simp [encodePrefix,wires]
    | succ k ih =>
      have prev := ih (by omega)
      have now : Disjoint (wires (packAfter w k)) (wires (encode w (n-5))) := by
        cases hd : packDue k
        · simp [packAfter,hd,wires]
        · have kd := packDue_true k hd
          have dis := windows_disjoint w hn (k-5) (n-5) (by omega) (by omega) (by omega)
          simpa only [packAfter,hd,if_true] using dis
      simpa only [encodePrefix,wires_append,Finset.disjoint_union_left] using And.intro prev now
  exact go n (Nat.le_refl _)


theorem prefix_next_legal (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n<512) (due : packDue n=true) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w (n-5)) s.basis) :
    MeasuredCodec5.legalAt (historyMap w (n-5)) (run (encodePrefix w n) m s).basis := by
  have dis := prefix_next_disjoint w hn n hb due
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  have same (q : Fin 10) : (run (encodePrefix w n) m s).basis (historyMap w (n-5) q)=
      s.basis (historyMap w (n-5) q) :=
    run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (n-5) q))
  intro i
  rw [same,same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp legal i


theorem encodePrefix_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hb : n≤512) (s : State) : (run (encodePrefix w n) [] s).phase=s.phase := by
  induction n with
  | zero => simp only [encodePrefix,run]
  | succ n ih =>
    rw [encodePrefix,run_append]
    simp only [List.take_nil,List.drop_nil]
    cases due : packDue n
    · simpa only [packAfter,due,Bool.false_eq_true,if_false,run] using ih (by omega)
    · have hd := packDue_true n due
      simpa only [packAfter,due,if_true,encode] using
        (MeasuredCodec5.encodeAt_zero_phase _ (historyMap_injective w hn (n-5) (by omega)) _).trans
          (ih (by omega))



theorem prefix_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (hn512 : n≤512) (s : State) (mE mD : List Bool)
    (legal : RawLegal w (n/5) s.basis) :
    run (decodePrefix w n) mD (run (encodePrefix w n) mE s)=s := by
  induction n generalizing mE mD with
  | zero => simp only [encodePrefix,decodePrefix,run]
  | succ n ih =>
    have old (a b : List Bool) := ih (by omega) a b (fun j hj => legal j (by omega))
    rw [encodePrefix,decodePrefix,run_append,run_append]
    cases due : packDue n
    · simp only [packAfter,decodeBefore,due,Bool.false_eq_true,if_false,run]
      exact old _ _
    · have bound := packDue_true n due
      have rawLegal : MeasuredCodec5.legalAt (historyMap w (n-5)) s.basis := by
        have dom := legal ((n-5)/5) (by omega)
        rwa [show 5*((n-5)/5)=n-5 by omega] at dom
      have dom := prefix_next_legal w hn n (by omega) due s
        (mE.take (measurementCount (encodePrefix w n))) rawLegal
      simp only [packAfter,decodeBefore,due,if_true,encode,decode]
      rw [MeasuredCodec5.roundtripAt _ (historyMap_injective w hn (n-5) (by omega)) _ _ _ dom]
      exact old _ _
























theorem allEncode_member (w : Nat → Wire) (n : Nat) (q : Wire) (hq : q∈wires (allEncode w n)) :
    ∃j,j<n ∧ q∈wires (encode w (5*j)) := by
  induction n with
  | zero => simp [allEncode,wires] at hq
  | succ n ih =>
    simp only [allEncode,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · obtain ⟨j,hj,member⟩ := ih hq
      exact ⟨j,by omega,member⟩
    · exact ⟨n,by omega,hq⟩

theorem allEncode_history_support (w : Nat → Wire) (n : Nat) (bound : 5*n≤512) :
    wires (allEncode w n)⊆(wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
  intro q hq
  obtain ⟨j,hj,member⟩ := allEncode_member w n q hq
  obtain ⟨i,rfl⟩ := history_gate_mem w (5*j) _ (Or.inl rfl) q member
  have region := historyId_region (5*j) (by omega) i
  apply List.mem_toFinset.mpr
  rcases region with h|h
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨historyId (5*j) i,by simp only [List.mem_range'_1]; omega,rfl⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨historyId (5*j) i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem allEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (outside : n≤j) (jb : 5*j+5≤512) :
    Disjoint (wires (allEncode w n)) (wires (encode w (5*j))) := by
  induction n with
  | zero => simp [allEncode,wires]
  | succ n ih =>
    have old := ih (by omega) (by omega)
    have now := windows_disjoint w hn (5*n) (5*j) (by omega) jb (by omega)
    simp only [allEncode,wires_append,Finset.disjoint_union_left]
    exact ⟨old,now⟩

theorem allEncode_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) :
    (run (allEncode w n) [] s).phase=s.phase := by
  induction n with
  | zero => simp only [allEncode,run]
  | succ n ih =>
    rw [allEncode,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact (MeasuredCodec5.encodeAt_zero_phase _ (historyMap_injective w hn _ (by omega)) _).trans
      (ih (by omega))



theorem allEncode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) (m : List Bool) (legal : RawLegal w n s.basis) :
    (run (allEncode w n) m s).phase=s.phase := by
  induction n generalizing m with
  | zero => simp only [allEncode,run]
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
    have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q))
    have dom : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
      apply (MeasuredCodec5.legalAt_iff _ _).mpr
      intro i
      rw [same,same]
      exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
    rw [allEncode,run_append]
    exact (encode_phase w hn (5*n) (by omega) before _ dom).trans
      (ih (by omega) _ (fun j hj => legal j (by omega)))

















theorem encodePrefix_index (w : Nat → Wire) (n : Nat) : encodePrefix w (5*n+1)=allEncode w n := by
  induction n with
  | zero => simp [encodePrefix,packAfter,packDue,allEncode]
  | succ n ih =>
    have index : 5*(n+1)+1=5*n+1+1+1+1+1+1 := by omega
    rw [index,encodePrefix,encodePrefix,encodePrefix,encodePrefix,encodePrefix,ih]
    have d1 : packDue (5*n+1)=false := by simp [packDue,Nat.add_mod]
    have d2 : packDue (5*n+1+1)=false := by simp [packDue,Nat.add_mod]
    have d3 : packDue (5*n+1+1+1)=false := by simp [packDue,Nat.add_mod]
    have d4 : packDue (5*n+1+1+1+1)=false := by simp [packDue,Nat.add_mod]
    have d5 : packDue (5*n+1+1+1+1+1)=true := by simp [packDue,Nat.add_mod]
    simp only [packAfter,d1,d2,d3,d4,d5,Bool.false_eq_true,if_false,if_true,List.append_nil]
    rw [show 5*n+1+1+1+1+1-5=5*n by omega]
    rfl

theorem encodePrefix_512 (w : Nat → Wire) : encodePrefix w 512=allEncode w 102 := by
  rw [show (512:Nat)=511+1 from rfl,encodePrefix]
  rw [show (511:Nat)=5*102+1 from rfl,encodePrefix_index]
  simp [packAfter,packDue]

end ECDSAAdd.Entrant.History5

end


-- ===== ECDSAAdd.Submission.Entrant.Placement5 =====
section

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Placement5
open Arithmetic MappedCompressed

def W (k : Nat) : Nat := 515+k
def H (k : Nat) : Nat := 1030+5*(k/2)+2*(k%2)
def workRegion (q : Nat) : Prop := 515≤q ∧ q≤718
def holeRegion (q : Nat) : Prop :=
  1030≤q ∧ q≤1537 ∧ ((q-1030)%5=0 ∨ (q-1030)%5=2)
def zeroRegion (q : Nat) : Prop := workRegion q ∨ holeRegion q
def omitted (q : Nat) : Prop := 515≤q ∧ q<717
def holeIndex (q : Nat) : Nat := 2*((q-1030)/5)+(q-1030)%5/2

instance (q : Nat) : Decidable (workRegion q) := by unfold workRegion; infer_instance
instance (q : Nat) : Decidable (holeRegion q) := by unfold holeRegion; infer_instance

theorem W_bound (k : Nat) (hk : k<204) : 515≤W k ∧ W k≤718 := by unfold W; omega
theorem H_bound (k : Nat) (hk : k<204) : 1030≤H k ∧ H k≤1537 := by unfold H; omega
theorem H_injective : Function.Injective H := by
  intro k l eq
  unfold H at eq
  omega
theorem H_region (k : Nat) (hk : k<204) : holeRegion (H k) := by
  have rem : (H k-1030)%5=2*(k%2) := by
    simp only [H,Nat.add_sub_cancel_left,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_add]
    omega
  have bounds := H_bound k hk
  unfold holeRegion
  rw [rem]
  omega
theorem H_index (k : Nat) : holeIndex (H k)=k := by
  unfold holeIndex H
  omega
theorem hole_recover (q : Nat) (hq : holeRegion q) :
    holeIndex q<204 ∧ H (holeIndex q)=q := by
  unfold holeRegion holeIndex H at *
  omega

private def baseFn (q : Nat) : Nat :=
  if workRegion q then H (q-515) else if holeRegion q then W (holeIndex q) else q

private theorem base_W (k : Nat) (hk : k<204) : baseFn (W k)=H k := by
  have region : workRegion (W k) := W_bound k hk
  simp only [baseFn,if_pos region]
  simp [W]

private theorem base_H (k : Nat) (hk : k<204) : baseFn (H k)=W k := by
  have outside : ¬workRegion (H k) := by
    have bound := H_bound k hk
    unfold workRegion
    omega
  simp only [baseFn,if_neg outside,if_pos (H_region k hk),H_index]

private theorem base_involutive : Function.Involutive baseFn := by
  intro q
  by_cases work : workRegion q
  · have hk : q-515<204 := by unfold workRegion at work; omega
    have eq : q=W (q-515) := by unfold workRegion at work; unfold W; omega
    rw [eq,base_W _ hk,base_H _ hk]
  · by_cases hole : holeRegion q
    · have recover := hole_recover q hole
      rw [←recover.2,base_H _ recover.1,base_W _ recover.1]
    · simp only [baseFn,if_neg work,if_neg hole]

def pi0 : Equiv.Perm Nat :=
  {toFun:=baseFn,invFun:=baseFn,left_inv:=base_involutive,right_inv:=base_involutive}

theorem pi0_W (k : Nat) (hk : k<204) : pi0 (W k)=H k := base_W k hk
theorem pi0_H (k : Nat) (hk : k<204) : pi0 (H k)=W k := base_H k hk
theorem pi0_outside (q : Nat) (hq : ¬zeroRegion q) : pi0 q=q := by
  have a : ¬workRegion q := fun h => hq (Or.inl h)
  have b : ¬holeRegion q := fun h => hq (Or.inr h)
  change baseFn q=q
  simp only [baseFn,if_neg a,if_neg b]

def spare0 : Nat := 717
def spare1 : Nat := 718

def pi (j : Nat) : Equiv.Perm Nat :=
  (Equiv.swap (W (2*j)) (H (2*j))).trans
    ((Equiv.swap (W (2*j+1)) (H (2*j+1))).trans
      ((Equiv.swap (H (2*j)) (H 202)).trans
        ((Equiv.swap (H (2*j+1)) (H 203)).trans pi0)))

private theorem WH_ne (k l : Nat) (hk : k<204) (hl : l<204) : W k≠H l := by
  have a := W_bound k hk
  have b := H_bound l hl
  omega

theorem pi_selected_even (j : Nat) (hj : j<102) : pi j (W (2*j))=spare0 := by
  have wh := WH_ne (2*j+1) (2*j) (by omega) (by omega)
  have hh : H (2*j)≠H (2*j+1) := H_injective.ne (by omega)
  have he : H 202≠H (2*j+1) := H_injective.ne (by omega)
  have hlast : H 202≠H 203 := H_injective.ne (by omega)
  simp only [pi,Equiv.trans_apply]
  rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne wh.symm hh,
    Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne he hlast,pi0_H 202 (by decide)]
  rfl

theorem pi_selected_odd (j : Nat) (hj : j<102) : pi j (W (2*j+1))=spare1 := by
  have ww : W (2*j+1)≠W (2*j) := by unfold W; omega
  have wh := WH_ne (2*j+1) (2*j) (by omega) (by omega)
  have hh : H (2*j+1)≠H (2*j) := H_injective.ne (by omega)
  have he : H (2*j+1)≠H 202 := H_injective.ne (by omega)
  simp only [pi,Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne ww wh,Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hh he,Equiv.swap_apply_left,pi0_H 203 (by decide)]
  rfl

theorem pi_other (j k : Nat) (hj : j<102) (hk : k<204)
    (he : k≠2*j) (ho : k≠2*j+1) : pi j (W k)=H k := by
  have ww0 : W k≠W (2*j) := by unfold W; omega
  have ww1 : W k≠W (2*j+1) := by unfold W; omega
  have wh0 := WH_ne k (2*j) hk (by omega)
  have wh1 := WH_ne k (2*j+1) hk (by omega)
  have wh2 := WH_ne k 202 hk (by decide)
  have wh3 := WH_ne k 203 hk (by decide)
  simp only [pi,Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne ww0 wh0,Equiv.swap_apply_of_ne_of_ne ww1 wh1,
    Equiv.swap_apply_of_ne_of_ne wh0 wh2,Equiv.swap_apply_of_ne_of_ne wh1 wh3,pi0_W k hk]

theorem pi_current_even (j : Nat) (hj : j<102) : pi j (H (2*j))=H (2*j) := by
  have ww : W (2*j)≠W (2*j+1) := by unfold W; omega
  have wh0 := WH_ne (2*j) (2*j) (by omega) (by omega)
  have wh1 := WH_ne (2*j) (2*j+1) (by omega) (by omega)
  have wh2 := WH_ne (2*j) 202 (by omega) (by decide)
  have wh3 := WH_ne (2*j) 203 (by omega) (by decide)
  simp only [pi,Equiv.trans_apply]
  rw [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne ww wh1,
    Equiv.swap_apply_of_ne_of_ne wh0 wh2,Equiv.swap_apply_of_ne_of_ne wh1 wh3,pi0_W _ (by omega)]

theorem pi_current_odd (j : Nat) (hj : j<102) : pi j (H (2*j+1))=H (2*j+1) := by
  have wh0 := WH_ne (2*j) (2*j+1) (by omega) (by omega)
  have hh : H (2*j+1)≠H (2*j) := H_injective.ne (by omega)
  have wh1 := WH_ne (2*j+1) (2*j) (by omega) (by omega)
  have wh2 := WH_ne (2*j+1) 202 (by omega) (by decide)
  have wh3 := WH_ne (2*j+1) (2*j+1) (by omega) (by omega)
  have wh4 := WH_ne (2*j+1) 203 (by omega) (by decide)
  simp only [pi,Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne wh0.symm hh,Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne wh1 wh2,Equiv.swap_apply_of_ne_of_ne wh3 wh4,pi0_W _ (by omega)]

theorem pi_outside (j q : Nat) (hj : j<102) (hq : ¬zeroRegion q) : pi j q=q := by
  have nw (k : Nat) (hk : k<204) : q≠W k := by
    intro eq; subst q; exact hq (Or.inl (W_bound k hk))
  have nh (k : Nat) (hk : k<204) : q≠H k := by
    intro eq; subst q; exact hq (Or.inr (H_region k hk))
  simp only [pi,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne
    (nw (2*j) (by omega)) (nh (2*j) (by omega)),
    Equiv.swap_apply_of_ne_of_ne (nw (2*j+1) (by omega)) (nh (2*j+1) (by omega)),
    Equiv.swap_apply_of_ne_of_ne (nh (2*j) (by omega)) (nh 202 (by omega)),
    Equiv.swap_apply_of_ne_of_ne (nh (2*j+1) (by omega)) (nh 203 (by omega)),pi0_outside q hq]

theorem nonhole_pi_safe (j q : Nat) (hj : j<102) (hq : ¬holeRegion q) : ¬omitted (pi j q) := by
  by_cases work : workRegion q
  · let k := q-515
    have hk : k<204 := by unfold k workRegion at *; omega
    have eq : q=W k := by unfold k W workRegion at *; omega
    rw [eq]
    by_cases even : k=2*j
    · rw [even,pi_selected_even j hj]; unfold omitted spare0; omega
    · by_cases odd : k=2*j+1
      · rw [odd,pi_selected_odd j hj]; unfold omitted spare1; omega
      · rw [pi_other j k hj hk even odd]
        have bound := H_bound k hk
        unfold omitted
        omega
  · rw [pi_outside j q hj (fun h => h.elim work hq)]
    unfold omitted workRegion at *
    omega

theorem nonhole_pi0_safe (q : Nat) (hq : ¬holeRegion q) : ¬omitted (pi0 q) := by
  by_cases work : workRegion q
  · have hk : q-515<204 := by unfold workRegion at *; omega
    have eq : q=W (q-515) := by unfold W workRegion at *; omega
    rw [eq,pi0_W _ hk]
    have bound := H_bound (q-515) hk
    unfold omitted
    omega
  · rw [pi0_outside q (fun h => h.elim work hq)]
    unfold omitted workRegion at *
    omega
















theorem shifted_zero_boundary (e : Equiv.Perm Nat)
    (fix : ∀q,¬zeroRegion q → e q=q) (s : State)
    (hz : ∀q,zeroRegion q → s.basis (base q)=false) :
    pullState (shifted e) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (shifted e q)=s.basis q
    by_cases small : q<16
    · change s.basis (shiftedFn e q)=s.basis q
      simp only [shiftedFn,if_pos small]
    · have eq : q=base (q-16) := by
        change q=q-16+16
        exact (Nat.sub_add_cancel (Nat.le_of_not_gt small)).symm
      rw [eq,shifted_base]
      by_cases clean : zeroRegion (q-16)
      · have mapped : zeroRegion (e (q-16)) := by
          by_contra outside
          have eq := e.injective (fix (e (q-16)) outside)
          exact outside (eq.symm ▸ clean)
        exact (hz _ mapped).trans (hz _ clean).symm
      · rw [fix _ clean]

def indices : List Nat := List.range' 0 515++List.range' 717 1081++
  List.range' 2056 258++List.range' 2400 12
def slots : List Wire := indices.map base

theorem mem_indices (q : Nat) : q∈indices ↔ MappedCompressed.live q ∧ ¬omitted q := by
  simp only [indices,List.mem_append,List.mem_range'_1]
  unfold MappedCompressed.live omitted
  omega

theorem indices_subset_old : indices⊆MappedCompressed.indices := by
  intro q hq
  have h := (mem_indices q).mp hq
  apply MappedCompressed.mem_indices q |>.mpr
  refine ⟨h.1,?_⟩
  unfold CompressedAllocation.omitted omitted at *
  omega

private theorem appendRange (xs : List Nat) (hd : xs.Nodup) (a n : Nat)
    (sep : ∀q∈xs,q<a ∨ a+n≤q) : (xs++List.range' a n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',List.disjoint_left.mpr ?_⟩
  intro q hq hr
  have hs := sep q hq
  simp only [List.mem_range'_1] at hr
  omega

theorem indices_nodup : indices.Nodup := by
  have a := appendRange (List.range' 0 515) List.nodup_range' 717 1081
    (by intro q h; simp only [List.mem_range'_1] at h; omega)
  have b := appendRange _ a 2056 258
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)
  exact appendRange _ b 2400 12
    (by intro q h; simp only [List.mem_append,List.mem_range'_1] at h; omega)








end ECDSAAdd.Entrant.Placement5

end


-- ===== ECDSAAdd.Submission.Entrant.FieldFrame5 =====
section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.History5
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed
attribute [local irreducible] run wires

def EncodedFieldFrame5 (w : Nat → Wire) (sign : Wire) (origin : BasisState)
    (X Y : Fp) (s : State) : Prop :=
  ∃raw:State,raw.phase=s.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y) raw.basis ∧ s=run (allEncode w 102) [] raw

def EncodedCanonicalFrame5 (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  ∃raw:State,raw.phase=s.phase ∧
    PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin
      X.val Y.val raw.basis ∧ s=run (allEncode base 102) [] raw












theorem encoded_canonical_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedCanonicalFrame5 origin X Y s) (ht : EncodedCanonicalFrame5 origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

def groupReadSites (w : Nat → Wire) (b sign eff : Wire) (start : Nat) : Finset Wire :=
  (sharedSites w sign).toFinset ∪ {b,eff} ∪ wires (encode w start)

def otherEncode (w : Nat → Wire) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if n=j then otherEncode w j n else otherEncode w j n++encode w (5*n)

theorem history_active_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    historyMap w start q∉sharedSites w sign := by
  let i := start+q.val/2
  let a := i-2
  let r : Fin 6 := ⟨2*(i-a)+q.val%2,by have := q.isLt; unfold a i; omega⟩
  have bound : a+3≤512 := by have := q.isLt; unfold a i; omega
  have same : historyMap w start q=compressedHistoryMap w a r := by
    change w (historyId start q)=w (compressedHistoryId a r)
    congr 1
    simp only [historyId,compressedHistoryId,r]
    unfold a i
    split_ifs <;> omega
  rw [same]
  exact CompressedFieldSupport.history_active_away w sign hn ho a bound r

theorem history_words_away (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    historyMap w start q∉(balancedSharedPorts w sign).r ∧
      historyMap w start q∉(balancedSharedPorts w sign).y := by
  have away := history_active_away w sign hn ho start hs q
  constructor <;> intro h <;> apply away
  all_goals
    simp only [sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem frame_history_legal (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (n : Nat) (bound : 5*n≤512) (origin current : BasisState) (X Y : Nat)
    (legal : RawLegal w n origin)
    (frame : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin X Y current) :
    RawLegal w n current := by
  intro j hj
  have same (q : Fin 10) : current (historyMap w (5*j) q)=origin (historyMap w (5*j) q) :=
    frame.2.2 _ (history_words_away w sign hn ho (5*j) (by omega) q).1
      (history_words_away w sign hn ho (5*j) (by omega) q).2
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [same,same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp (legal j hj) i


theorem otherEncode_outside (w : Nat → Wire) (n j : Nat) (h : n≤j) :
    otherEncode w j n=allEncode w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [otherEncode,if_neg (by omega),ih (by omega),allEncode]

theorem otherEncode_member (w : Nat → Wire) (n j : Nat) (q : Wire)
    (h : q∈wires (otherEncode w j n)) : ∃k,k<n ∧ k≠j ∧ q∈wires (encode w (5*k)) := by
  induction n with
  | zero => simp [otherEncode,wires] at h
  | succ n ih =>
    by_cases same : n=j
    · simp only [otherEncode,if_pos same] at h
      obtain ⟨k,hk,hj,member⟩ := ih h
      exact ⟨k,by omega,hj,member⟩
    · simp only [otherEncode,if_neg same,wires_append,Finset.mem_union] at h
      rcases h with h|h
      · obtain ⟨k,hk,hj,member⟩ := ih h
        exact ⟨k,by omega,hj,member⟩
      · exact ⟨n,by omega,same,h⟩

theorem otherEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) :
    Disjoint (wires (otherEncode w j n)) (wires (encode w (5*j))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  have sep : 5*k+5≤5*j ∨ 5*j+5≤5*k := by omega
  rcases sep with h|h
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) member hc
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) hc member

theorem allEncode_factor (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) :
    run (allEncode w n) [] s=run (otherEncode w j n) [] (run (encode w (5*j)) [] s) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases same : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [otherEncode,if_pos rfl,otherEncode_outside w n n (Nat.le_refl _)]
      exact (run_disjoint_commute (allEncode w n) (encode w (5*n)) dis [] [] s).symm
    · have prior := ih j (by omega) (by omega)
      have right : run (otherEncode w j (n+1)) [] (run (encode w (5*j)) [] s)=
          run (encode w (5*n)) [] (run (otherEncode w j n) [] (run (encode w (5*j)) [] s)) := by
        rw [otherEncode,if_neg (Ne.symm same),run_append]
        simp only [List.take_nil,List.drop_nil]
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [prior,right]

theorem otherEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hb : b∉skywalkPoolWires w) (hsign : sign∉skywalkPoolWires w) (heff : eff∉skywalkPoolWires w)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j)) :
    Disjoint (wires (otherEncode w j n)) (wires body) := by
  have pool := skywalkShared_integer_nodup w hn
  have groups := otherEncode_disjoint w pool n j bound hj
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  obtain ⟨r,rfl⟩ := history_gate_mem w (5*k) _ (Or.inl rfl) q member
  have own : historyMap w (5*k) r∈skywalkPoolWires w := by
    apply List.mem_map.mpr
    refine ⟨historyId (5*k) r,?_,rfl⟩
    simp only [List.mem_range'_1]
    have := historyId_bound (5*k) (by omega) r
    omega
  have away := history_active_away w sign hn hsign (5*k) (by omega) r
  have read := support used
  simp only [groupReadSites,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at read
  rcases read with (read|read)|read
  · exact away (List.mem_toFinset.mp read)
  · rcases read with eq|eq
    · exact hb (eq ▸ own)
    · exact heff (eq ▸ own)
  · exact Finset.disjoint_left.mp groups hq read

theorem window_transport_other (w : Nat → Wire) (start : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hs : start+5≤512) (other body : Program)
    (he : Disjoint (wires other) (wires (encode w start)))
    (hb : Disjoint (wires other) (wires body)) (s : State) (mO m0 m1 m2 m3 : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    run (encode w start) m3 (run body m2 (run (decode w start) m1
      (run other mO (run (encode w start) m0 s))))=
      run other mO (run (encode w start) m3 (run body m2 s)) := by
  have otherLegal : MeasuredCodec5.legalAt (historyMap w start) (run other mO s).basis := by
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    have same (q : Fin 10) : (run other mO s).basis (historyMap w start q)=s.basis (historyMap w start q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp he used (history_site_mem w start q))
    intro i
    rw [same,same]
    exact (MeasuredCodec5.legalAt_iff _ _).mp legal i
  rw [run_disjoint_commute other (encode w start) he mO m0 s]
  rw [show run (decode w start) m1 (run (encode w start) m0 (run other mO s))=run other mO s from
    MeasuredCodec5.roundtripAt _ (historyMap_injective w hn start hs) _ m0 m1 otherLegal]
  rw [←run_disjoint_commute other body hb mO m2 s]
  exact (run_disjoint_commute other (encode w start) he mO m3 (run body m2 s)).symm


private theorem zero_records (p : Program) (hm : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  rw [←run_take p m s,←run_take p n s,hm]
  simp only [List.take_zero]

theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hp : ∀q∈[b,sign,eff],q∉skywalkPoolWires w)
    (j : Nat) (hj : j<102) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s)
    (legal : RawLegal w 102 origin) :
    let out := run (decode w (5*j)++body++encode w (5*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have leg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin raw.basis _ _ legal frame
  have factor := allEncode_factor w pool 102 j (by decide) hj raw
  have hE := otherEncode_disjoint w pool 102 j (by decide) hj
  have hB := otherEncode_body_disjoint w b sign eff hn
    (hp b (by simp)) (hp sign (by simp)) (hp eff (by simp)) 102 j (by decide) hj body support
  let mb := m.drop 2
  let rawOut := run body mb raw
  have result := correct raw mb frame
  have outLeg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (5*j) pool (by omega)
    (otherEncode w j 102) body hE hB raw [] [] (m.take 2) mb (mb.drop (measurementCount body)) (leg j hj)
  have records : run (encode w (5*j)) (mb.drop (measurementCount body)) rawOut=
      run (encode w (5*j)) [] rawOut :=
    MeasuredCodec5.encodeAt_independent _ (historyMap_injective w pool _ (by omega)) _ _ _ (outLeg j hj)
  rw [records] at transport
  have back := allEncode_factor w pool 102 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (decode w (5*j)++body++encode w (5*j)) m s=run (allEncode w 102) [] rawOut := by
    rw [eq,factor]
    simp only [List.append_assoc]
    rw [run_append,(decode_counts w (5*j)).2,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allEncode_zero_phase w pool 102 (by decide) rawOut
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩


theorem encoded_disjoint_step (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkPoolWires w).Nodup) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (dis : Disjoint (wires (allEncode w 102)) (wires body))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s) :
    (run body m s).phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B (run body m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let rawOut := run body m raw
  have result := correct raw m frame
  have actual : run body m s=run (allEncode w 102) [] rawOut := by
    rw [encoded]
    exact (run_disjoint_commute (allEncode w 102) body dis [] m raw).symm
  rw [actual]
  have ep := allEncode_zero_phase w hn 102 (by decide) rawOut
  exact ⟨ep.trans (result.1.trans phase),rawOut,ep.symm,result.2,rfl⟩


theorem allEncode_hole (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) (m : List Bool)
    (legal : RawLegal w n s.basis) (port : Fin 10) (hole : port=5 ∨ port=9) :
    (run (allEncode w n) m s).basis (historyMap w (5*j) port)=false := by
  induction n generalizing j m with
  | zero => omega
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    by_cases current : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) := by
        apply run_preserves_outside
        intro used
        exact Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q)
      have domain : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
        apply (MeasuredCodec5.legalAt_iff _ _).mpr
        intro i
        rw [same,same]
        exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
      have result := encode_correct w hn (5*n) (by omega) before
        (m.drop (measurementCount (allEncode w n))) domain
      rw [allEncode,run_append]
      rcases hole with rfl|rfl
      · exact result.2.1
      · exact result.2.2
    · have older : j<n := by omega
      have prior := ih j (by omega) older (m.take (measurementCount (allEncode w n)))
        (fun k hk => legal k (by omega))
      have dis := windows_disjoint w hn (5*j) (5*n) (by omega) (by omega) (by omega)
      have keep := run_preserves_outside (encode w (5*n))
        (m.drop (measurementCount (allEncode w n))) before (historyMap w (5*j) port)
        (fun used => Finset.disjoint_left.mp dis (history_site_mem w (5*j) port) used)
      rw [allEncode,run_append]
      exact keep.trans prior


theorem allEncode_holes_zero (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (legal : RawLegal w 102 s.basis)
    (k : Nat) (hk : k<204) : (run (allEncode w 102) m s).basis (w (Placement5.H k))=false := by
  let port : Fin 10 := if k%2=0 then 5 else 9
  have hp : port=5 ∨ port=9 := by unfold port; split <;> simp
  have same : w (Placement5.H k)=historyMap w (5*(k/2)) port := by
    change w (Placement5.H k)=w (historyId (5*(k/2)) port)
    congr 1
    unfold Placement5.H historyId port
    split_ifs <;> omega
  rw [same]
  exact allEncode_hole w hn 102 (k/2) (by decide) (by omega) s m legal port hp

theorem encoded_work_zero (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (origin : BasisState) (env : Env w origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s)
    (q : Nat) (hq : Placement5.workRegion q) : s.basis (w q)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env w sign hn origin raw.basis _ _ env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero w raw.basis rawEnv.1 q
    (by unfold Placement5.workRegion at hq; omega) (by unfold Placement5.workRegion at hq; omega)
  have support := allEncode_history_support w 102 (by decide)
  have away : w q∉wires (allEncode w 102) := by
    intro used
    have member := List.mem_toFinset.mp (support used)
    rcases List.mem_append.mp member with member|member
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      simp only [List.mem_range'_1] at hk
      have same := skywalkShared_index_inj w hn k q (by omega)
        (by unfold Placement5.workRegion at hq; omega) eq
      unfold Placement5.workRegion at hq
      omega
  rw [encoded]
  exact (run_preserves_outside (allEncode w 102) [] raw _ away).trans zero

theorem encoded_zero_region (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (origin : BasisState) (env : Env w origin) (legal : RawLegal w 102 origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s) :
    ∀q,Placement5.zeroRegion q → s.basis (w q)=false := by
  intro q hq
  rcases hq with work|hole
  · exact encoded_work_zero w sign hn origin env X Y s frame q work
  · have recover := Placement5.hole_recover q hole
    obtain ⟨raw,_,rawFrame,encoded⟩ := frame
    have rawLegal := frame_history_legal w sign hn ho 102 (by decide) origin raw.basis _ _ legal rawFrame
    rw [encoded,←recover.2]
    exact allEncode_holes_zero w (skywalkShared_integer_nodup w hn) raw [] rawLegal _ recover.1

end ECDSAAdd.Entrant.History5

end


-- ===== ECDSAAdd.Submission.Entrant.LaneIFold =====
section

-- ===== LaneIFold =====

/-! Field cell fold without the carry-out position.

The original fold is a 257-wide mapped addition whose top position (`cout`)
is computed only to be cleared again by `CX minus cout`.  Here the addition is
256 wide; `cout` is never written.  A measurement of the (clean) `cout` wire
keeps the measurement count of the cell unchanged. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic BalancedCircuit BalancedField BalancedFold

def foldBitsI (L : Layout) : List MappedBit :=
  (List.range 256).map (fun i =>
    {wire:=some (if sparseF.testBit (i+1) then L.plus else L.minus),flip:=false})

theorem foldBits_split (L : Layout) :
    foldBits L=foldBitsI L++[{wire:=none,flip:=false}] := rfl

theorem foldBitsI_length (L : Layout) : (foldBitsI L).length=256 := by
  simp [foldBitsI]

theorem mappedValue_append_zero (bits : List MappedBit) (s : BasisState) :
    mappedValue (bits++[{wire:=none,flip:=false}]) s=mappedValue bits s := by
  induction bits with
  | nil => simp [mappedValue,MappedBit.value]
  | cons b bs ih => simp only [List.cons_append,mappedValue,ih]

theorem foldBitsI_value (L : Layout) (s : BasisState) :
    mappedValue (foldBitsI L) s=mappedValue (foldBits L) s := by
  rw [foldBits_split,mappedValue_append_zero]

theorem foldBitsI_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (foldBitsI L)) :
    w=L.plus ∨ w=L.minus := by
  apply foldBits_sources L w
  rw [foldBits_split]
  simp only [mappedWires,List.flatMap_append,List.mem_append] at hw ⊢
  exact Or.inl hw

def foldI (L : Layout) : Program :=
  [.measureX L.cout [] []]++mappedAdd (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity

def undoFoldI (L : Layout) : Program :=
  [.measureX L.cout [] []]++mappedSub (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity

theorem clean_measure (t : Wire) (s : State) (m : List Bool) (h : s.basis t=false) :
    run [.measureX t [] []] m s=s := by
  apply State.extensionality
  · simp [run,measureAndCorrect,correct,h]
  · funext q
    by_cases hq : q=t
    · subst q; simp [run,measureAndCorrect,correct,writeBit,h]
    · simp [run,measureAndCorrect,correct,writeBit,Function.update_of_ne hq]

theorem foldI_ND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::(foldTarget L++L.carry.take 255)).Nodup := by
  have big := foldND L hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp big q
  have tk : (L.carry.take 255).count q≤L.carry.count q :=
    (List.take_sublist 255 L.carry).count_le q
  simp only [List.count_append,List.count_cons,List.count_nil] at h tk ⊢
  omega

theorem foldI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (foldI L)=255 ∧ measurementCount (foldI L)=256 ∧
    toffoliCount (undoFoldI L)=255 ∧ measurementCount (undoFoldI L)=256 := by
  have w := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have a := mappedAdd_counts (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity bl cl
  have b := mappedSub_counts (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity bl cl
  simp only [foldI,undoFoldI,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,tl]
  norm_num [toffoliCount,measurementCount]

theorem fold_counts_old (L : Layout) (hw : L.Widths) :
    toffoliCount (fold L)=256 ∧ measurementCount (fold L)=256 ∧
    toffoliCount (BalancedInverse.undoFold L)=256 ∧
    measurementCount (BalancedInverse.undoFold L)=256 := by
  have w := BalancedCircuit.widths L hw
  have a := mappedAdd_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  have b := mappedSub_counts (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
    (by omega) (by omega)
  simp only [fold,BalancedInverse.undoFold,toffoliCount_append,measurementCount_append,
    a.1,a.2,b.1,b.2,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

/-- Same contract as `fold_correct`, for the 256-wide fold. -/
theorem foldI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    (run (foldI L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (foldI L) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (foldI L) m s).basis L.cout=false ∧
    ∀ w,w∉foldTarget L → (run (foldI L) m s).basis w=s.basis w := by
  have big := foldND L hn
  have nd := foldI_ND L hn
  have widths := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := widths.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,widths.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have coutAway : L.cout∉foldTarget L := by
    intro h
    have c := List.nodup_iff_count.mp big L.cout
    have pos := List.count_pos_iff.mpr h
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c
    omega
  have sourceAway : ∀ w∈mappedWires (foldBitsI L),w∉L.parity::(foldTarget L++L.carry.take 255) := by
    intro w h bad
    have c := List.nodup_iff_count.mp big w
    have tk : (L.carry.take 255).count w≤L.carry.count w :=
      (List.take_sublist 255 L.carry).count_le w
    have pos := List.count_pos_iff.mpr bad
    rcases foldBitsI_sources L w h with rfl|rfl
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
  have clean : ∀ q∈L.carry.take 255,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp hcarry q (List.mem_of_mem_take hq)
  have source : mappedValue (foldBitsI L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    rw [foldBitsI_value]
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have hadd := mappedAdd_correct (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity nd
    sourceAway bl cl s m.tail clean
  have actual : run (foldI L) m s=run (mappedAdd (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity) m.tail s := by
    have h0 := clean_measure L.cout s m hc
    simp only [foldI,List.singleton_append]
    simp only [run] at h0 ⊢
    rw [h0]
  rw [actual]
  refine ⟨hadd.1,?_,?_,hadd.2.1⟩
  · rw [hadd.2.2,source,hword,hp,tl]
    have fv := foldedSum_value T ht
    have bound := encodeWord_bound 256 (halfResult T)
    have fs : foldedSum T=toggledWord T/2+
        selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
    have mw : modulusWord=2^256 := rfl
    rw [show selectedSource (plusController T) (minusController T)+toggledWord T/2+
      (originalParity T).toNat=foldedSum T by omega,fv,mw]
    cases minusController T
    · simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
      exact Nat.mod_eq_of_lt bound
    · simp only [Bool.toNat_true,Nat.mul_one,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt bound
  · exact (hadd.2.1 L.cout coutAway).trans hc

/-- Same contract as `undoFold_correct`, for the 256-wide subtraction. -/
theorem undoFoldI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (undoFoldI L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (undoFoldI L) m s).basis=toggledWord T/2 ∧
    (run (undoFoldI L) m s).basis L.cout=false ∧
    ∀w,w∉foldTarget L → (run (undoFoldI L) m s).basis w=s.basis w := by
  have big := foldND L hn
  have nd := foldI_ND L hn
  have widths := BalancedCircuit.widths L hw
  have tl : (foldTarget L).length=256 := by
    have h := widths.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(foldTarget L).length := by
    rw [List.length_take,widths.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(foldTarget L).length := by rw [foldBitsI_length,tl]
  have coutAway : L.cout∉foldTarget L := by
    intro h
    have c := List.nodup_iff_count.mp big L.cout
    have pos := List.count_pos_iff.mpr h
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c
    omega
  have sourceAway : ∀ w∈mappedWires (foldBitsI L),w∉L.parity::(foldTarget L++L.carry.take 255) := by
    intro w h bad
    have c := List.nodup_iff_count.mp big w
    have tk : (L.carry.take 255).count w≤L.carry.count w :=
      (List.take_sublist 255 L.carry).count_le w
    have pos := List.count_pos_iff.mpr bad
    rcases foldBitsI_sources L w h with rfl|rfl
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
    · simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos tk
      omega
  have clean : ∀ q∈L.carry.take 255,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp hcarry q (List.mem_of_mem_take hq)
  have source : mappedValue (foldBitsI L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    rw [foldBitsI_value]
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have sub := BalancedInverse.mappedSub_any_correct (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity nd
    sourceAway bl cl s m.tail clean
  have actual : run (undoFoldI L) m s=run (mappedSub (foldBitsI L) (foldTarget L) (L.carry.take 255) L.parity) m.tail s := by
    have h0 := clean_measure L.cout s m hc
    simp only [undoFoldI,List.singleton_append]
    simp only [run] at h0 ⊢
    rw [h0]
  rw [actual]
  refine ⟨sub.1,?_,?_,sub.2.1⟩
  · rw [sub.2.2,source,hword,hp,tl]
    have fv := foldedSum_value T ht
    have bound := prepared_upper_bound T ht
    have fs : foldedSum T=toggledWord T/2+
        selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
    have mw : modulusWord=2^256 := rfl
    rw [mw] at fv bound
    have pb : (originalParity T).toNat≤1 := by cases originalParity T <;> decide
    cases hm : minusController T
    · rw [hm] at fv
      simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at fv
      rw [show encodeWord 256 (halfResult T)+2^256-selectedSource (plusController T) false-
        (originalParity T).toNat=toggledWord T/2+2^256 by rw [hm] at fs; omega,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt bound
    · rw [hm] at fv
      simp only [Bool.toNat_true,Nat.mul_one] at fv
      rw [show encodeWord 256 (halfResult T)+2^256-selectedSource (plusController T) true-
        (originalParity T).toNat=toggledWord T/2 by rw [hm] at fs; omega]
      exact Nat.mod_eq_of_lt bound
  · exact (sub.2.1 L.cout coutAway).trans hc

end ECDSAAdd.Entrant.LaneI



end


-- ===== ECDSAAdd.Submission.Entrant.LaneIKernel =====
section

set_option exponentiation.threshold 512

-- ===== LaneIKernel =====

/-! Forward and inverse field kernels using the 256-wide fold, and their exact
State equalities with the original kernels on the original kernel domain. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic BalancedCircuit BalancedField BalancedFold

section Core

def coreProgramI (L : Layout) : Program :=
  seedViews L++(rawAdd L++(prepareFold L++(foldI L++
    (rotateRight (rawTarget L)++releaseSelectors L))))

theorem coreI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (coreProgramI L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    t.basis L.parity=originalParity (rawSum B X Y) ∧
    t.basis L.sourceGuard=s.basis L.ymsb ∧
    (∀q∈coreClean L,t.basis q=false) ∧
    (∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q) := by
  let T := rawSum B X Y
  let P := originalParity T
  let N := decide (T<0)
  let H := negative (halfResult T)
  let m₁ := m.drop (measurementCount (rawAdd L))
  let m₂ := m₁.drop (measurementCount (foldI L))
  generalize eu : run (seedViews L) m s = u
  generalize ev : run (rawAdd L) m u = v
  generalize ew : run (prepareFold L) m₁ v = w
  generalize ez : run (foldI L) m₁ w = z
  generalize ea : run (rotateRight (rawTarget L)) m₂ z = a
  generalize et : run (releaseSelectors L) m₂ a = t
  have ht := rawSum_bounds B X Y hx hy
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have su := compose_seed_frame L hw hn s m hc
  rw [eu] at su
  have sv := seed_raw_signed L hw hn B X Y hx hy s m hs hr hyr hc
  simp only [run_append] at sv
  simp only [run_take] at sv
  simp only [show measurementCount (seedViews L)=0 from rfl,List.drop_zero] at sv
  rw [eu,ev] at sv
  have cu := (seed_signed L hw hn X Y s m hr hyr hc).2.2
  rw [eu] at cu
  have rf (q : Wire) (hq : q∉rawTarget L) : v.basis q=u.basis q :=
    by simpa only [ev] using rawAdd_frame L hw hn u m cu q hq
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have vp : v.basis L.parity=P :=
    (rf _ (away _ (by simp))).trans (by simpa only [eu] using seed_parity L hw hn B X Y s m hr hyr hc)
  have vo : v.basis L.one=N := word_sign L.r L.one v.basis T sv.2.1
  have vr : v.basis L.r0=P := by
    apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) v.basis T
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using sv.2.1
  have vz (q : Wire) (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) : v.basis q=false := by
    have cv := compose_clean_views L hn q hq
    have qo : q≠L.one := fun e => cv.1 (e ▸ (by simp [rawTarget]))
    exact (rf q cv.1).trans ((su.2.2 q cv.2.1 qo cv.2.2.1).trans (hc q cv.2.2.2))
  have wp := compose_prepare_bits L hn P N v m₁ vp vo vr
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at wp
  have pf (q : Wire) (hq : q∉rawTarget L) (hl : q≠L.lower)
      (hm : q≠L.minus) (hu : q≠L.plus) : w.basis q=v.basis q :=
    by
      simpa only [ew] using (compose_prepare_frame L hn P N v m₁ vp vo vr
        (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp)) q hq hl hm hu)
  have wpar : w.basis L.parity=P := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans vp
  have wc : w.basis L.cout=false := by
    exact (pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans (vz _ (by simp))
  have wcarry : regValue L.carry w.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qne (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact (pf q (away q (by simp [hq])) (qne _ (by simp))
      (qne _ (by simp)) (qne _ (by simp))).trans (vz q (by simp [hq]))
  have prepared := prepare_upper L hw hn T v m₁ sv.2.1 vp
    (vz _ (by simp)) (vz _ (by simp)) (vz _ (by simp))
  rw [ew] at prepared
  have zw := foldI_correct L hw hn T ht w m₁ wpar
    wp.2.2.2.2.1 wp.2.2.2.1 wc wcarry prepared
  rw [ez] at zw
  have z0 : z.basis L.r0=false :=
    (zw.2.2.2 _ (compose_not_fold_r0 L hn)).trans wp.2.1
  have az := rotate_folded L hw hn T ht z m₂ z0 zw.2.1
  rw [ea] at az
  have af (q : Wire) (hq : q∉rawTarget L) : a.basis q=w.basis q :=
    (az.2.2.2 q hq).trans (zw.2.2.2 q (compose_fold_subset L q hq))
  have ah : a.basis L.rmsb=H :=
    BalancedCleanup.result_msb L.toLayout hw (halfResult T) (halfResult_spec T ht).1 a.basis az.2.1
  have hp : a.basis L.parity=P := (af _ (away _ (by simp))).trans wpar
  have hsign : H=(N ^^ P) := halfResult_sign T ht
  have al : a.basis L.lower=(H ^^ P) := by
    rw [af _ (away _ (by simp)),wp.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have am : a.basis L.minus=(P && !H) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have au : a.basis L.plus=(P ^^ (P && !H)) := by
    rw [af _ (away _ (by simp)),wp.2.2.2.2.1,hsign]
    cases N <;> cases P <;> rfl
  have ta := compose_release_frame L hn P H a m₂ hp ah al am au
  rw [et] at ta
  have tf (q : Wire) (hl : q≠L.lower) (hm : q≠L.minus) (hu : q≠L.plus) :
      t.basis q=a.basis q := ta.2.2.2.2 q hl hm hu
  have tr : regValue L.r t.basis=encodeWord 256 (halfResult T) := by
    apply Eq.trans _ az.2.1
    apply regValue_congr
    intro q hq
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
    exact tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have tp : t.basis L.parity=P := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans hp
  have tg : t.basis L.sourceGuard=s.basis L.ymsb := by
    exact (tf _ (by assumption) (by assumption) (by assumption)).trans
      ((af _ (away _ (by simp))).trans
        ((pf _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans
          ((rf _ (away _ (by simp))).trans su.2.1)))
  have tz : ∀q∈coreClean L,t.basis q=false := by
    intro q hq
    simp only [coreClean,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|hq
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans
        ((az.2.2.2 _ (away _ (by simp))).trans zw.2.2.1)
    · exact ta.2.2.1
    · exact ta.2.2.2.1
    · exact ta.2.1
    · exact (tf _ (by assumption) (by assumption) (by assumption)).trans az.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
          q≠f := fun e => flagAway L hn f hf (by simp [e ▸ hq])
      exact (tf q (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((af q (away q (by simp [hq]))).trans
          ((pf q (away q (by simp [hq])) (neq _ (by simp)) (neq _ (by simp))
            (neq _ (by simp))).trans (vz q (by simp [hq]))))
  have frame : ∀q,q∉L.r → q≠L.parity → q≠L.sourceGuard → t.basis q=s.basis q := by
    intro q hqr hqp hqg
    by_cases hq : q∈coreClean L
    · exact (tz q hq).trans (hc q (coreClean_sub_work L q hq)).symm
    · have qo : q≠L.one := fun e => hq (by simp [coreClean,e])
      have ql : q≠L.lower := fun e => hq (by simp [coreClean,e])
      have qm : q≠L.minus := fun e => hq (by simp [coreClean,e])
      have qu : q≠L.plus := fun e => hq (by simp [coreClean,e])
      have qa : q∉rawTarget L := by simpa only [rawTarget,List.mem_append,
        List.mem_singleton,not_or] using And.intro hqr qo
      exact (tf q ql qm qu).trans ((af q qa).trans ((pf q qa ql qm qu).trans
        ((rf q qa).trans (su.2.2 q hqg qo hqp))))
  have actual : run (coreProgramI L) m s=t := by
    simp only [coreProgramI,run_append]
    simp only [run_take]
    simp only [
      show measurementCount (seedViews L)=0 from rfl,
      show measurementCount (prepareFold L)=0 from rfl,
      (rotate_counts (rawTarget L)).2.1,List.drop_zero]
    rw [eu,ev,ew,ez,ea,et]
  rw [actual]
  exact ⟨ta.1.trans (az.1.trans (zw.1.trans (wp.1.trans sv.1))),tr,tp,tg,tz,frame⟩


theorem coreI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (coreProgramI L)+1=toffoliCount (coreProgram L) ∧
    measurementCount (coreProgramI L)=measurementCount (coreProgram L) := by
  have a := foldI_counts L hw
  have b := fold_counts_old L hw
  simp only [coreProgramI,coreProgram,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

/-- The new core produces the identical complete State on the core domain. -/
theorem core_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (coreProgramI L) m s=run (coreProgram L) m s := by
  have fresh := coreI_correct L hw hn B X Y hx hy s m hs hr hyr hc
  have old := core_correct L hw hn B X Y hx hy s m hs hr hyr hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    by_cases hp : q=L.parity
    · subst q; exact fresh.2.2.1.trans old.2.2.1.symm
    by_cases hg : q=L.sourceGuard
    · subst q; exact fresh.2.2.2.1.trans old.2.2.2.1.symm
    exact (fresh.2.2.2.2.2 q hq hp hg).trans (old.2.2.2.2.2 q hq hp hg).symm

end Core

section Inverse
open BalancedInverse

def invProgramI (L : Layout) : Program :=
  [.CX L.ymsb L.sourceGuard]++recoverParity L++recoverSelectors L++
  rotateLeft (rawTarget L)++undoFoldI L++undoPreparation L++rawSubtract L++(seedViews L).reverse

private theorem initialWork (L : Layout) (a : Wire)
    (ha : a∈[L.parity,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorWork (L : Layout) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem frameWork (L : Layout) (a : Wire)
    (ha : a∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorAway (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) :
    a≠L.sourceGuard ∧ a≠L.parity := by
  have nd : ([L.sourceGuard,L.parity]++([L.cout,L.minus,L.plus,L.lower,L.one]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (allND L hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have sep := List.disjoint_left.mp (List.nodup_append'.mp nd).2.2
  exact ⟨fun e => sep (by simp [←e]) ha,fun e => sep (by simp [←e]) ha⟩


theorem invProgramI_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (invProgramI L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (result B R Y) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.r → t.basis q=s.basis q) := by
  let X := result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let m₁ := m.drop (measurementCount (recoverParity L))
  let m₂ := m₁.drop (measurementCount (undoFoldI L))
  let m₃ := m₂.drop (measurementCount (undoPreparation L))
  let m₄ := m₃.drop (measurementCount (rawSubtract L))
  generalize e₀ : run [.CX L.ymsb L.sourceGuard] m s=u₀
  generalize e₁ : run (recoverParity L) m u₀=u₁
  generalize e₂ : run (recoverSelectors L) m₁ u₁=u₂
  generalize e₃ : run (rotateLeft (rawTarget L)) m₁ u₂=u₃
  generalize e₄ : run (undoFoldI L) m₁ u₃=u₄
  generalize e₅ : run (undoPreparation L) m₂ u₄=u₅
  generalize e₆ : run (rawSubtract L) m₃ u₅=u₆
  generalize e₇ : run (seedViews L).reverse m₄ u₆=t
  have hx : Centered X := result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := result_half B R Y hr hy
  have rawRange : -((2^(257-1) : Nat) : Int)≤T ∧ T<((2^(257-1) : Nat) : Int) := by
    have c := BalancedField.constants
    norm_num at ⊢
    omega
  have w := BalancedCircuit.widths L hw
  have rlen := (BalancedCleanup.widths L.toLayout hw).2.1
  have ylen := (BalancedCleanup.widths L.toLayout hw).2.2.1
  have cnd : L.toLayout.wires.Nodup :=
    (List.nodup_append'.mp (show ([L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires).Nodup from hn)).2.1
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have zero (q : Wire) (hq : q∈work L) : s.basis q=false := hc q hq
  have f₀ (a : Wire) (ha : a≠L.sourceGuard) : u₀.basis a=s.basis a := by
    rw [←e₀]; simp only [run,writeBit,Function.update_of_ne ha]
  have guard₀ : u₀.basis L.sourceGuard=s.basis L.ymsb := by
    rw [←e₀]
    simp only [run,writeBit,Function.update_self]
    rw [hc L.sourceGuard (by simp [work])]
    simp only [Bool.false_xor]
  have R₀ : regValue L.r u₀.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have Y₀ : regValue L.y u₀.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 ylen s.basis Y hY)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have z₀ (a : Wire) (ha : a∈[L.parity,L.lower,L.one]++L.carry) : u₀.basis a=false := by
    have ne : a≠L.sourceGuard := by
      rcases List.mem_append.mp ha with ha|ha
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl <;> assumption
      · exact fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha])
    exact (f₀ a ne).trans (hc a (initialWork L a ha))
  have oneOracle := recoverParity_correct L hw cnd R Y B hr hy u₀ m R₀ Y₀
    ((f₀ _ (by assumption)).trans hs) (z₀ _ (by simp)) (z₀ _ (by simp))
    (fun a ha => z₀ a (by simp [ha])) (z₀ _ (by simp))
  have parity : decide (q < |2*R-signedY B Y|)=P := result_parity B R Y hr hy
  rw [parity,e₁] at oneOracle
  have p₁ : u₁.basis L.parity=P := by rw [oneOracle]; simp only [writeBit,Function.update_self]
  have f₁ (a : Wire) (hg : a≠L.sourceGuard) (hp : a≠L.parity) : u₁.basis a=s.basis a := by
    rw [oneOracle]; simp only [writeBit,Function.update_of_ne hp]; exact f₀ a hg
  have g₁ : u₁.basis L.sourceGuard=s.basis L.ymsb := by
    rw [oneOracle]; simpa only [writeBit,Function.update_of_ne (show L.sourceGuard≠L.parity by assumption)] using guard₀
  have z₁ (a : Wire) (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : u₁.basis a=false := by
    have ne := selectorAway L hn a ha
    exact (f₁ a ne.1 ne.2).trans (hc a (selectorWork L a ha))
  have R₁ : regValue L.r u₁.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₁ a (neq _ (by simp)) (neq _ (by simp))
  have sign₁ : u₁.basis L.rmsb=decide (halfResult T<0) := by
    rw [half]
    exact BalancedCleanup.result_msb L.toLayout hw R hr u₁.basis R₁
  have packet₂ := recoverSelectors_packet L hn T ht u₁ m₁ p₁ sign₁
    (z₁ _ (by simp)) (z₁ _ (by simp)) (z₁ _ (by simp))
  rw [e₂] at packet₂
  have f₂ (a : Wire) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) : u₂.basis a=u₁.basis a :=
    packet₂.2.2.2.2 a hl hm hu
  have R₂ : regValue L.r u₂.basis=encodeWord 256 R := by
    apply Eq.trans _ R₁
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have one₂ : u₂.basis L.one=false :=
    (f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp))
  have packet₃ := rotate_unfold L hw hn R u₂ m₁ one₂ R₂
  rw [e₃] at packet₃
  have f₃ (a : Wire) (ha : a∉rawTarget L) : u₃.basis a=u₂.basis a := packet₃.2.2.2 a ha
  have p₃ : u₃.basis L.parity=P := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans p₁)
  have c₃ : u₃.basis L.cout=false := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp)))
  have carry₃ : regValue L.carry u₃.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₃ a (away a (by simp [ha]))).trans
      ((f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans (z₁ a (by simp [ha])))
  have upper₃ : regValue (foldTarget L) u₃.basis=encodeWord 256 (halfResult T) := by
    rw [half]; exact packet₃.2.2.1
  have packet₄ := undoFoldI_correct L hw hn T ht u₃ m₁ p₃
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1) c₃ carry₃ upper₃
  rw [e₄] at packet₄
  have f₄ (a : Wire) (ha : a∉rawTarget L) : u₄.basis a=u₃.basis a :=
    packet₄.2.2.2 a (compose_fold_subset L a ha)
  have zero₄ : u₄.basis L.r0=false :=
    (packet₄.2.2.2 _ (compose_not_fold_r0 L hn)).trans packet₃.2.1
  have packet₅ := undoPreparation_packet L hw hn T ht u₄ m₂
    ((f₄ _ (away _ (by simp))).trans p₃) zero₄
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)) packet₄.2.1
  rw [e₅] at packet₅
  have f₅ (a : Wire) (ha : a∉rawTarget L) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) :
      u₅.basis a=u₁.basis a := (packet₅.2.2.2.2.2 a ha hl hm hu).trans
    ((f₄ a ha).trans ((f₃ a ha).trans (f₂ a hl hm hu)))
  have raw₅ : signedRegValue (rawTarget L) u₅.basis=T := by
    unfold signedRegValue
    rw [w.2.1,packet₅.2.1]
    exact decode_encodeWord 257 (by norm_num) T rawRange
  have Y₅ : signedRegValue L.y u₅.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₅ a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans (f₁ a (neq _ (by simp)) (neq _ (by simp)))
  have g₅ : u₅.basis L.sourceGuard=u₅.basis L.ymsb := by
    have left := (f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g₁
    have right := (f₅ L.ymsb (away L.ymsb (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f₁ L.ymsb (by assumption) (by assumption))
    exact left.trans right.symm
  have src₅ : signedRegValue (rawSource L) u₅.basis=Y := by
    exact (signed_extension L.ylow L.ymsb L.sourceGuard u₅.basis g₅).trans Y₅
  have carry₅ : regValue L.carry u₅.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (packet₅.2.2.2.2.2 a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans
      ((regValue_zero _ _).mp carry₃ a ha |> fun h => (f₄ a (away a (by simp [ha]))).trans h)
  have sign₅ : u₅.basis L.sign=B := (f₅ _ (away _ (by simp))
    (by assumption) (by assumption) (by assumption)).trans ((f₁ _ (by assumption) (by assumption)).trans hs)
  have packet₆ := rawSubtract_signed L hw hn B X Y hx u₅ m₃ sign₅ src₅ raw₅ carry₅
  rw [e₆] at packet₆
  have f₆ (a : Wire) (ha : a∉rawTarget L) : u₆.basis a=u₅.basis a := packet₆.2.2 a ha
  have Y₆ : signedRegValue L.y u₆.basis=Y := by
    apply Eq.trans _ Y₅
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => f₆ a (away a (by simp [ha])))
  have g₆ : u₆.basis L.sourceGuard=u₆.basis L.ymsb := by
    exact (f₆ _ (away _ (by simp))).trans (g₅.trans
      (f₆ _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p₆ : u₆.basis L.parity=P := (f₆ _ (away _ (by simp))).trans
    ((f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans p₁)
  have packet₇ := unseed_packet L hw hn B X Y hx u₆ m₄ packet₆.2.1 Y₆ g₆ p₆
  rw [e₇] at packet₇
  have f₇ (a : Wire) (hg : a≠L.sourceGuard) (ho : a≠L.one) (hp : a≠L.parity) :
      t.basis a=u₆.basis a := packet₇.2.2.2.2 a hg ho hp
  have actual : run (invProgramI L) m s=t := by
    simp only [invProgramI,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,List.drop_zero]
    rw [e₀,run_append,run_take,e₁,run_append,run_take]
    simp only [show measurementCount (recoverSelectors L)=0 from rfl,List.drop_zero]
    rw [e₂,run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero,
      e₃,run_append,run_take,e₄,run_append,run_take,e₅,run_append,run_take,e₆,e₇]

  have clean : ∀a∈work L,t.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact packet₇.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans ((packet₅.2.2.2.2.2 _ (away _ (by simp))
          (by assumption) (by assumption) (by assumption)).trans packet₄.2.2.1))
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.1)
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.2.1)
    · exact packet₇.2.2.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.1)
    · exact packet₇.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
        fun e => flagAway L hn f hf (by simp [e ▸ ha])
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a (away a (by simp [ha]))).trans ((regValue_zero _ _).mp carry₅ a ha))
  have frame : ∀a,a∉L.r → t.basis a=s.basis a := by
    intro a ha
    by_cases workA : a∈work L
    · exact (clean a workA).trans (hc a workA).symm
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a≠f :=
        fun e => workA (e.symm ▸ frameWork L f hf)
      have ar : a∉rawTarget L := by
        simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
        exact ⟨ha,neq _ (by simp)⟩
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a ar).trans ((f₅ a ar (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
          (f₁ a (neq _ (by simp)) (neq _ (by simp)))))
  have out : regValue L.r t.basis=encodeWord 256 X := by
    have corr := unseed_correlations L hw B X Y hx u₆ packet₆.2.1 Y₆ g₆ p₆
    have narrow : signedRegValue L.r u₆.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u₆.basis corr.1).symm.trans packet₆.2.1
    apply Eq.trans _ (word_encoding L.r 256 rlen u₆.basis X narrow)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  rw [actual]
  exact ⟨packet₇.1.trans (packet₆.1.trans (packet₅.1.trans (packet₄.1.trans
    (packet₃.1.trans (packet₂.1.trans (by rw [oneOracle,←e₀]; rfl)))))),out,clean,frame⟩


theorem invProgramI_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (invProgramI L)+1=toffoliCount (BalancedInverse.program L) ∧
    measurementCount (invProgramI L)=measurementCount (BalancedInverse.program L) := by
  have a := foldI_counts L hw
  have b := fold_counts_old L hw
  simp only [invProgramI,BalancedInverse.program,toffoliCount_append,measurementCount_append,
    a.2.2.1,a.2.2.2,b.2.2.1,b.2.2.2]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

theorem inv_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (invProgramI L) m s=run (BalancedInverse.program L) m s := by
  have fresh := invProgramI_correct L hw hn B R Y hr hy s m hs hR hY hc
  have old := BalancedInverse.program_correct L hw hn B R Y hr hy s m hs hR hY hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2 q hq).trans (old.2.2.2 q hq).symm

end Inverse

section Field
open DirectSkywalk

/-- Forward field kernel with the 256-wide fold. -/
def fieldProgramI (w : Nat → Wire) (sign : Wire) : Program :=
  coreProgramI (balancedSharedPorts w sign)++
    (TerminalParityOffset.program (OffsetCleanupBorrowedCaller.layout w sign)++
      [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard])

theorem fieldProgramI_counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (fieldProgramI w sign)+1=toffoliCount (OffsetBorrowedField.program w sign) ∧
    measurementCount (fieldProgramI w sign)=measurementCount (OffsetBorrowedField.program w sign) := by
  have c := coreI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [fieldProgramI,OffsetBorrowedField.program,toffoliCount_append,measurementCount_append]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

theorem fieldProgram_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) (s : State) (m : List Bool)
    (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyv : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (he : OffsetBorrowedCanonical.Env w s.basis) :
    run (fieldProgramI w sign) m s=run (OffsetBorrowedField.program w sign) m s := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have eq := core_eq (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign) nd B X Y hx hy s m hs hr hyv
    (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  have c := coreI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [fieldProgramI,OffsetBorrowedField.program]
  simp only [run_append,run_take]
  rw [c.2,eq]

end Field

section InverseField
open OffsetBorrowedInverse DirectSkywalk

def tailI (L : BalancedCircuit.Layout) : Program :=
  BalancedInverse.recoverSelectors L++rotateLeft (BalancedCircuit.rawTarget L)++
    undoFoldI L++BalancedInverse.undoPreparation L++
    BalancedInverse.rawSubtract L++(BalancedCircuit.seedViews L).reverse

/-- Inverse field kernel with the 256-wide subtraction. -/
def invFieldProgramI (w : Nat → Wire) (sign : Wire) : Program :=
  [.CX (balancedSharedPorts w sign).ymsb (balancedSharedPorts w sign).sourceGuard]++
    recoverParity w sign++tailI (balancedSharedPorts w sign)

theorem invFieldProgramI_counts (w : Nat → Wire) (sign : Wire) :
    toffoliCount (invFieldProgramI w sign)+1=toffoliCount (OffsetBorrowedInverse.program w sign) ∧
    measurementCount (invFieldProgramI w sign)=measurementCount (OffsetBorrowedInverse.program w sign) := by
  have a := foldI_counts (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  have b := fold_counts_old (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
  simp only [invFieldProgramI,OffsetBorrowedInverse.program,tailI,OffsetBorrowedInverse.tail,
    toffoliCount_append,measurementCount_append,a.2.2.1,a.2.2.2,b.2.2.1,b.2.2.2]
  refine ⟨?_,?_⟩ <;> first | omega | trivial

private theorem lower_mem_work (L : BalancedCircuit.Layout) : L.lower∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem one_mem_work (L : BalancedCircuit.Layout) : L.one∈BalancedCircuit.work L := by
  simp [BalancedCircuit.work]

private theorem carry_mem_work (L : BalancedCircuit.Layout) (a : Wire) (ha : a∈L.carry) :
    a∈BalancedCircuit.work L := List.mem_append_right _ ha

private theorem old_layout (L : BalancedCircuit.Layout) :
    invProgramI L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++tailI L := by
  simp only [invProgramI,tailI,List.append_assoc]

private theorem run_prefix (a b : Wire) (oracle rest : Program) (m : List Bool) (s : State) :
    run ([.CX a b]++oracle++rest) m s=
      run rest (m.drop (measurementCount oracle))
        (run oracle m (run [.CX a b] m s)) := by
  rw [List.append_assoc,run_append,run_take]
  change run (oracle++rest) m (run [.CX a b] m s)=_
  rw [run_append,run_take]

private theorem guard_records (a b : Wire) (m n : List Bool) (s : State) :
    run [.CX a b] m s=run [.CX a b] n s := by
  simp only [run]

private theorem index_ne (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (hne : i≠j) : w i≠w j :=
  fun h => hne (skywalkShared_index_inj w hn i j hi hj h)

/-- The borrowed bank omits precisely the live source guard. -/
private theorem bank_guard_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (a : Wire) (ha : a∈OffsetCleanupBorrowedCaller.carry w) : a≠w 765 := by
  simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at ha
  rcases ha with ha|ha
  · intro e
    exact arith_block_away w hn 765 512 253 (by omega) (by omega) (by omega) (e ▸ ha)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals exact index_ne w hn _ _ (by omega) (by omega) (by omega)














/-- 254 padding records align the 764-record original recovery with the
510-record replacement. Their actual XOR outputs agree on independent records. -/
theorem invField_equivI (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (invFieldProgramI w sign) m s=
      run (invProgramI (balancedSharedPorts w sign))
        (List.replicate 254 false++m) s := by
  let L := balancedSharedPorts w sign
  let n := List.replicate 254 false++m
  let u := run [.CX L.ymsb L.sourceGuard] m s
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have nd := balancedSharedPorts_nodup w sign hn own
  have widths := balancedSharedPorts_widths w sign
  have clean := balancedSharedPorts_clean w sign s.basis hw hu
  have keep (a : Wire) (ha : a≠L.sourceGuard) : u.basis a=s.basis a := by
    simp only [u,run,writeBit,Function.update_of_ne ha]
  have dataAway (a : Wire) (ha : a∈L.r++L.y++L.carry) : a≠L.sourceGuard :=
    fun e => flagAway L nd L.sourceGuard (by simp) (e ▸ ha)
  have R₁ : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 (BalancedCleanup.widths L.toLayout widths).2.1 s.basis R hR)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have Y₁ : regValue L.y u.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout widths).2.2.1 s.basis Y hY)
    exact regValue_congr _ _ _ (fun a ha => keep a (dataAway a (by simp [ha])))
  have scalar := scalarND L nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  rcases scalar with ⟨⟨_,_,_,_,gSign,gLower,gOne,_,_,_⟩,_⟩
  have S₁ : u.basis sign=B := (keep L.sign (Ne.symm gSign)).trans hS
  have low₁ : u.basis (w 1797)=false :=
    (keep L.lower (Ne.symm gLower)).trans (clean L.lower (lower_mem_work L))
  have one₁ : u.basis (w 1027)=false :=
    (keep L.one (Ne.symm gOne)).trans (clean L.one (one_mem_work L))
  have high_ne : w 1026≠L.sourceGuard := by
    change w 1026≠w 765
    exact index_ne w hn 1026 765 (by omega) (by omega) (by omega)
  have high₁ : u.basis (w 1026)=false := (keep _ high_ne).trans hhigh
  have carry₁ : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    exact (keep a (dataAway a (by simp [ha]))).trans (clean a (carry_mem_work L a ha))
  have bank₁ : ∀a∈OffsetCleanupBorrowedCaller.carry w,u.basis a=false := by
    intro a ha
    exact (keep a (by simpa only [L,balancedSharedPorts] using bank_guard_away w hn a ha)).trans
      (OffsetCleanupBorrowedCaller.entryCarry_clean w s.basis hw a ha)
  have oracle := recoverParity_equiv w sign hn hsOut R Y B hr hy u m n
    R₁ Y₁ S₁ low₁ one₁ high₁ carry₁ bank₁
  have oldCount : measurementCount (BalancedInverse.recoverParity L)=764 := by
    simpa only [BalancedInverse.recoverParity] using (BalancedCleanup.counts L.toLayout widths).2
  have freshCount : measurementCount (recoverParity w sign)=510 := by
    simpa only [recoverParity] using (BalancedCleanupOffsetZero.counts
      (OffsetCleanupBorrowedCaller.layout w sign) (OffsetCleanupBorrowedCaller.widths w sign)).2
  have align : n.drop 764=m.drop 510 := by simp [n,List.drop_append]
  have oldGuard : run [.CX L.ymsb L.sourceGuard] n s=u := guard_records _ _ n m s
  have freshRun : run (invFieldProgramI w sign) m s=
      run (tailI L) (m.drop 510) (run (recoverParity w sign) m u) := by
    rw [invFieldProgramI,run_prefix,freshCount]
  have oldRun : run (invProgramI L) n s=
      run (tailI L) (n.drop 764) (run (BalancedInverse.recoverParity L) n u) := by
    rw [old_layout,run_prefix,oldCount,oldGuard]
  rw [freshRun,oldRun,align,oracle]


theorem invField_eq (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hsOut : sign∉skywalkSharedWires w)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y)
    (hS : s.basis sign=B)
    (hw : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0)
    (hhigh : s.basis (w 1026)=false) :
    run (invFieldProgramI w sign) m s=run (OffsetBorrowedInverse.program w sign) m s := by
  have own : sign∉balancedSharedIds.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact hsOut (arith_mem w 0 2314 i (by omega) (balancedSharedIds_bound i hi))
  have fresh := invField_equivI w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  have old := program_equiv w sign hn hsOut R Y B hr hy s m hR hY hS hw hu hhigh
  have mid := inv_eq (balancedSharedPorts w sign) (balancedSharedPorts_widths w sign)
    (balancedSharedPorts_nodup w sign hn own) B R Y hr hy s (List.replicate 254 false++m) hS hR hY
    (balancedSharedPorts_clean w sign s.basis hw hu)
  rw [fresh,old,mid]

end InverseField

end ECDSAAdd.Entrant.LaneI



end


-- ===== ECDSAAdd.Submission.Entrant.ArithAvoid =====
section

/-! The mapped Skywalk arithmetic never touches the logical labels `769`,
`2313` or `2401`–`2408`.

The published support certificate for the arithmetic (`controlled_support`)
places it inside the full 1,899-label inventory.  The arithmetic's actual
gates come from the integer universe (labels below 1,798), from the field
sites (`fieldSite`) and from the history packets, all relocated by the
allocation permutations, which only move labels inside the work/hole region.
None of these is one of the labels above, so their physical images (the
auxiliary carry-in and eight classification/control metadata sites) are not
in the arithmetic's support. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt
attribute [local irreducible] compactSkywalkTick compactSkywalkReverseTick
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed
  NativeFirstDirect.forward NativeFirstDirect.inverse NativeFirstKnown.inverse

/-- Logical labels avoided by the arithmetic. -/
def badIdx (q : Nat) : Prop := q = 769 ∨ q = 2313 ∨ (2401 ≤ q ∧ q ≤ 2408)

/-- A physical wire that is not the image (under `base`) of a bad label. -/
def goodW (q : Wire) : Prop := ¬ (q = 769 + 16 ∨ q = 2313 + 16 ∨ (2401 + 16 ≤ q ∧ q ≤ 2408 + 16))
















theorem base_good (q : Nat) (h : ¬ badIdx q) : goodW (base q) := by
  show ¬ (q + 16 = 769 + 16 ∨ q + 16 = 2313 + 16 ∨ (2401 + 16 ≤ q + 16 ∧ q + 16 ≤ 2408 + 16))
  unfold badIdx at h; omega











































/-! Field side. -/

















































































































































/-! Integer side. -/























































































/-! The zero-divisor wrapper never uses its auxiliary carry-in. -/







































end ECDSAAdd.Entrant

end


-- ===== ECDSAAdd.Submission.Entrant.HalfLane =====
section

/-! Source: submission94960368-af01-4326-b69e-f43f55712c0a;
original half-field method: submission8e13f110-79c6-44fd-a3a3-0730950fc6e8. -/

/-! Resource facts for the halving-endpoint field segment that the Lane A
kernel needs besides its contract: avoided logical labels and a gate-slot
bound.  The segment is the unchanged entry-trimmed replay plus two halving
converters and one narrow copy, all on field sites. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfLane
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed Secp256k1

section Avoid
attribute [local irreducible] wires



















end Avoid

section Slots
open Challenge Baselines
attribute [local irreducible] renameProgram copyRegister mixedTranscriptUnitTrace MappedCompressed.logicalCell
  MappedCompressed.mappedGroup MappedCompressed.mappedGroups
  EntryMappedFieldSegmentTrim.firstGroup PenultimateSwapIdentity.cell
  mappedAdd mappedSub rotateRight rotateLeft

theorem replay_gateSlots_le (divide : Bool) :
    gateSlots (PenultimateMapped.replay divide) ≤ 13941000 := by
  have g := mappedGroups_gateSlots_le divide 1 169
  have f := firstGroup_gateSlots_le divide
  have p := penultimateCell_gateSlots_le divide
  have replayEq (A B C : Program) (d : Bool) :
      gateSlots (if d then A++B++C else C++B++A) = gateSlots A+gateSlots B+gateSlots C := by
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte,gateSlots_append]
    omega
  rw [PenultimateMapped.replay,replayEq,rename_gateSlots]
  omega

private theorem convert_gateSlots_generic (L : BalancedConvert.Layout) (hw : L.Widths) :
    gateSlots (HalfConvert.center L) ≤ 6000 ∧ gateSlots (HalfConvert.canonical L) ≤ 6000 := by
  have w : L.word.length=256 :=
    BalancedConvert.word_length L hw
  have a := mappedAdd_gateSlots_le (HalfConvert.lowCorrection L)
    L.low (L.carry.take 254) L.cin
  have b := mappedSub_gateSlots_le (HalfConvert.lowCorrection L)
    L.low (L.carry.take 254) L.cin
  obtain ⟨r1,r2⟩ := rotate_gateSlots_le L.word
  rw [HalfConvert.lowCorrection_length] at a b
  rw [w] at r1 r2
  rw [hw.1] at b
  simp only [HalfConvert.center,HalfConvert.canonical,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega


theorem convert_gateSlots_le :
    gateSlots HalfField.centerT ≤ 6000 ∧ gateSlots HalfField.canonT ≤ 6000 :=
  convert_gateSlots_generic HalfField.tgt (balancedSharedTargetConvert_widths base)


theorem segment_gateSlots_le (divide : Bool) :
    gateSlots (HalfField.segment divide) ≤ 14100000 := by
  have rp := replay_gateSlots_le divide
  have cv := convert_gateSlots_le
  have cp : gateSlots HalfField.copyN ≤ 256 := by
    simp only [HalfField.copyN,HalfField.ports,copyRegister_gateSlots,balancedSharedPorts_r,wireBlock_length]
    omega
  cases divide <;> simp only [HalfField.segment,Bool.false_eq_true,↓reduceIte,gateSlots_append] <;> omega

end Slots

end ECDSAAdd.Entrant.HalfLane

end


-- ===== ECDSAAdd.Submission.Entrant.LaneICell =====
section

/-! Source: submission 898d9e8d-5646-41d3-977d-9c617d7ea1eb,
commit 5139f277ef3ab3b85f356982e3d22429a8cebe85. -/
set_option exponentiation.threshold 512

-- ===== LaneICell =====

/-! Field cells, replays and the endpoint cell built on the 256-wide fold
kernels, with exact State equality to the original cells on their frames,
and an instruction-level inclusion into the original programs. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.LaneI
open ECDSAAdd.Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical

/-! ### Generic State-equality composition -/

theorem seq_eq (P P' Q Q' : Program) (s : State) (m : List Bool)
    (hc : measurementCount P'=measurementCount P)
    (hp : run P' (m.take (measurementCount P)) s=run P (m.take (measurementCount P)) s)
    (hq : run Q' (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)=
      run Q (m.drop (measurementCount P)) (run P (m.take (measurementCount P)) s)) :
    run (P'++Q') m s=run (P++Q) m s := by
  rw [run_append,run_append,hc,hp,hq]

theorem window_split (b source flag : Wire) (c : Bool) (P : Program) :
    transcriptSelectWindow b source flag c P=
      (transcriptSelectCompute b source flag c++transcriptSelectExpose flag c)++
        (P++(transcriptSelectExpose flag c++transcriptSelectErase b source flag c)) := by
  simp only [transcriptSelectWindow,List.append_assoc]

private theorem select_startI (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hf : s.basis flag=false) :
    run (transcriptSelectCompute b source flag constant ++
      transcriptSelectExpose flag constant) m s=
      ⟨s.phase,mixedTranscriptBase s.basis b source flag constant⟩ := by
  rw [run_append,transcriptSelectCompute_correct b source flag constant hn]
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases hq : q=flag
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,mixedTranscriptBit,
          writeBit,Function.update,hf,hb,hs]
    · cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,writeBit,Function.update,hq]

theorem select_start_frame (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false) (X Y : Nat) :
    Triple (PairFrame z a base X Y)
      (transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant)
      (PairFrame z a (mixedTranscriptBase base b source flag constant) X Y) := by
  intro s m h
  have hz : s.basis flag=false := (h.2.2 flag hf.1 hf.2).trans hzero
  rw [select_startI b source flag constant hn s m hz]
  refine ⟨rfl,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => by
      simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
        fun he => hf.1 (he ▸ hq)])).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => by
      simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
        fun he => hf.2 (he ▸ hq)])).trans h.2.1
  · intro q hqz hqa
    by_cases hq : q=flag
    · subst q
      simp [mixedTranscriptBase,mixedTranscriptBit,writeBit,
        h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
    · simpa [mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa

theorem window_eq (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false) (X Y : Nat)
    (P P' : Program) (hc : measurementCount P'=measurementCount P)
    (heq : ∀ (t : State) (r : List Bool),
      PairFrame z a (mixedTranscriptBase base b source flag constant) X Y t.basis →
      run P' r t=run P r t)
    (s : State) (m : List Bool) (h : PairFrame z a base X Y s.basis) :
    run (transcriptSelectWindow b source flag constant P') m s=
      run (transcriptSelectWindow b source flag constant P) m s := by
  rw [window_split,window_split]
  have start := select_start_frame b source flag constant z a hn hb hs hf base hzero X Y
  apply seq_eq _ _ _ _ s m rfl rfl
  apply seq_eq _ _ _ _ _ _ hc _ rfl
  exact heq _ _ (start s _ h).2

theorem window_counts_eq (b source flag : Wire) (c : Bool) (P P' : Program)
    (hc : measurementCount P'=measurementCount P) :
    measurementCount (transcriptSelectWindow b source flag c P')=
      measurementCount (transcriptSelectWindow b source flag c P) := by
  rw [(transcriptSelectWindow_counts b source flag c P').2,
    (transcriptSelectWindow_counts b source flag c P).2,hc]

theorem window_toffoli (b source flag : Wire) (c : Bool) (P P' : Program) (k : Nat)
    (hc : toffoliCount P'+k=toffoliCount P) :
    toffoliCount (transcriptSelectWindow b source flag c P')+k=
      toffoliCount (transcriptSelectWindow b source flag c P) := by
  rw [(transcriptSelectWindow_counts b source flag c P').1,
    (transcriptSelectWindow_counts b source flag c P).1,←hc]
  omega

/-! ### Instruction-level inclusion -/

/-- Every instruction of `P'` occurs in `P`, except clean measurements of
wires already used by `P`; and `P'` has no more syntax slots than `P`. -/
def InstrSub (P' P : Program) : Prop :=
  (∀ i∈P', i∈P ∨ ∃ t∈wires P, i=.measureX t [] []) ∧
    Challenge.gateSlots P'≤Challenge.gateSlots P

theorem mem_wires_iff (P : Program) (q : Wire) : q∈wires P ↔ ∃ i∈P, q∈i.wires := by
  induction P with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires,Finset.mem_union,ih,List.mem_cons]
    constructor
    · rintro (h|⟨j,hj,hq⟩)
      · exact ⟨i,Or.inl rfl,h⟩
      · exact ⟨j,Or.inr hj,hq⟩
    · rintro ⟨j,(rfl|hj),hq⟩
      · exact Or.inl hq
      · exact Or.inr ⟨j,hj,hq⟩

theorem InstrSub.wires_sub {P' P : Program} (h : InstrSub P' P) : wires P'⊆wires P := by
  intro q hq
  obtain ⟨i,hi,hq⟩ := (mem_wires_iff P' q).mp hq
  rcases h.1 i hi with hi|⟨t,ht,rfl⟩
  · exact (mem_wires_iff P q).mpr ⟨i,hi,hq⟩
  · have : q=t := by simpa [Instr.wires,correctionWires] using hq
    subst q; exact ht

theorem InstrSub.physical {P' P : Program} (h : InstrSub P' P) (hp : GatePhysical P) :
    GatePhysical P' := by
  intro i hi
  rcases h.1 i hi with hi|⟨t,_,rfl⟩
  · exact hp i hi
  · trivial

theorem InstrSub.slots {P' P : Program} (h : InstrSub P' P) :
    Challenge.gateSlots P'≤Challenge.gateSlots P := h.2

theorem InstrSub.refl (P : Program) : InstrSub P P := ⟨fun i hi => Or.inl hi,le_refl _⟩

theorem InstrSub.append {P₁' P₁ P₂' P₂ : Program} (h₁ : InstrSub P₁' P₁) (h₂ : InstrSub P₂' P₂) :
    InstrSub (P₁'++P₂') (P₁++P₂) := by
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rcases h₁.1 i hi with h|⟨t,ht,e⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr ⟨t,by rw [wires_append]; exact Finset.mem_union_left _ ht,e⟩
    · rcases h₂.1 i hi with h|⟨t,ht,e⟩
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr ⟨t,by rw [wires_append]; exact Finset.mem_union_right _ ht,e⟩
  · simp only [Challenge.gateSlots_append]
    exact Nat.add_le_add h₁.2 h₂.2

theorem InstrSub.rename (f : Wire → Wire) {P' P : Program} (h : InstrSub P' P) :
    InstrSub (renameProgram f P') (renameProgram f P) := by
  refine ⟨?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    rcases h.1 j hj with h|⟨t,ht,rfl⟩
    · exact Or.inl (List.mem_map.mpr ⟨j,h,rfl⟩)
    · refine Or.inr ⟨f t,?_,?_⟩
      · rw [renameProgram_support]; exact Finset.mem_image_of_mem f ht
      · simp [renameInstr]
  · simp only [Baselines.rename_gateSlots]
    exact h.2

theorem InstrSub.window (b source flag : Wire) (c : Bool) {P' P : Program} (h : InstrSub P' P) :
    InstrSub (transcriptSelectWindow b source flag c P') (transcriptSelectWindow b source flag c P) := by
  simp only [transcriptSelectWindow]
  exact (((InstrSub.refl _).append (InstrSub.refl _)).append h |>.append (InstrSub.refl _)).append
    (InstrSub.refl _)

theorem InstrSub.trans {P'' P' P : Program} (h₁ : InstrSub P'' P') (h₂ : InstrSub P' P) :
    InstrSub P'' P := by
  refine ⟨?_,h₁.2.trans h₂.2⟩
  intro i hi
  rcases h₁.1 i hi with h|⟨t,ht,e⟩
  · exact h₂.1 i h
  · exact Or.inr ⟨t,h₂.wires_sub ht,e⟩

/-! ### The narrow fold is an instruction subset of the wide fold -/

theorem mappedAdd_mem_extend (bs : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (b : MappedBit) (y c : Wire) (hl : bs.length=ys.length) (hc : cs.length+1=ys.length) :
    (∀ i∈mappedAdd bs ys cs cin, i∈mappedAdd (bs++[b]) (ys++[y]) (cs++[c]) cin) ∧
    Challenge.gateSlots (mappedAdd bs ys cs cin)≤
      Challenge.gateSlots (mappedAdd (bs++[b]) (ys++[y]) (cs++[c]) cin) := by
  induction ys generalizing bs cs cin with
  | nil => simp at hc
  | cons y0 ys ih =>
    cases bs with
    | nil => simp at hl
    | cons b0 bs =>
      cases ys with
      | nil =>
        have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        have hcs : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst hb; subst hcs
        simp only [List.nil_append,List.cons_append,mappedAdd,Challenge.gateSlots_append]
        refine ⟨fun i hi => ?_,by omega⟩
        simp only [List.mem_append]
        exact Or.inr hi
      | cons y1 ys =>
        cases bs with
        | nil => simp at hl
        | cons b1 bs =>
          cases cs with
          | nil => simp at hc
          | cons c0 cs =>
            have hrec := ih (b1::bs) cs c0 (by simpa using hl) (by simpa using hc)
            simp only [List.cons_append] at hrec
            simp only [List.cons_append,mappedAdd,Challenge.gateSlots_append]
            refine ⟨fun i hi => ?_,by omega⟩
            simp only [List.mem_append] at hi ⊢
            rcases hi with ((h|h)|h)|h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inl (Or.inr (hrec.1 i h)))
            · exact Or.inl (Or.inr h)
            · exact Or.inr h

theorem carry_split (L : BalancedCircuit.Layout) (hw : L.Widths) :
    ∃ c, L.carry=L.carry.take 255++[c] := by
  have len := (BalancedCircuit.widths L hw).2.2.2.2
  have d : (L.carry.drop 255).length=1 := by rw [List.length_drop,len]
  obtain ⟨c,hc⟩ := List.length_eq_one_iff.mp d
  exact ⟨c,by rw [←hc,List.take_append_drop]⟩

theorem foldI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (foldI L) (BalancedCircuit.fold L) := by
  obtain ⟨c,hc⟩ := carry_split L hw
  have w := BalancedCircuit.widths L hw
  have tl : (BalancedCircuit.foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(BalancedCircuit.foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(BalancedCircuit.foldTarget L).length := by rw [foldBitsI_length,tl]
  have ext := mappedAdd_mem_extend (foldBitsI L) (BalancedCircuit.foldTarget L) (L.carry.take 255)
    L.parity {wire:=none,flip:=false} L.cout c bl cl
  rw [←hc,←foldBits_split] at ext
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with h|h
    · right
      refine ⟨L.cout,?_,by simpa using h⟩
      simp only [BalancedCircuit.fold,wires_append]
      apply Finset.mem_union_right
      simp [wires,Instr.wires]
    · left
      simp only [BalancedCircuit.fold]
      exact List.mem_append_left _ (ext.1 i h)
  · have e := ext.2
    simp only [foldI,BalancedCircuit.fold,Challenge.gateSlots_append]
    simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,Challenge.instructionSlots,
      List.length_nil]
    omega

theorem undoFoldI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (undoFoldI L) (BalancedInverse.undoFold L) := by
  obtain ⟨c,hc⟩ := carry_split L hw
  have w := BalancedCircuit.widths L hw
  have tl : (BalancedCircuit.foldTarget L).length=256 := by
    have h := w.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil] at h
    omega
  have cl : (L.carry.take 255).length+1=(BalancedCircuit.foldTarget L).length := by
    rw [List.length_take,w.2.2.2.2,tl]; decide
  have bl : (foldBitsI L).length=(BalancedCircuit.foldTarget L).length := by rw [foldBitsI_length,tl]
  have ext := mappedAdd_mem_extend (foldBitsI L) (BalancedCircuit.foldTarget L) (L.carry.take 255)
    L.parity {wire:=none,flip:=false} L.cout c bl cl
  rw [←hc,←foldBits_split] at ext
  have nots : ∀ i∈notRegister (BalancedCircuit.foldTarget L),
      i∈notRegister (BalancedCircuit.foldTarget L++[L.cout]) := by
    intro i hi
    simp only [notRegister,List.map_append] at hi ⊢
    exact List.mem_append_left _ hi
  have notSlots (r : List Wire) : Challenge.gateSlots (notRegister r)=r.length := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      simp only [notRegister,List.map_cons,Baselines.gateSlots_cons,Challenge.instructionSlots,
        List.length_cons] at ih ⊢
      rw [ih]; omega
  refine ⟨?_,?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with h|h
    · right
      refine ⟨L.cout,?_,by simpa using h⟩
      simp only [BalancedInverse.undoFold,wires_append]
      apply Finset.mem_union_left
      simp [wires,Instr.wires]
    · left
      simp only [BalancedInverse.undoFold,mappedSub] at h ⊢
      simp only [List.mem_append] at h ⊢
      rcases h with (h|h)|h
      · exact Or.inr (Or.inl (Or.inl (nots i h)))
      · exact Or.inr (Or.inl (Or.inr (ext.1 i h)))
      · exact Or.inr (Or.inr (nots i h))
  · have e := ext.2
    simp only [undoFoldI,BalancedInverse.undoFold,mappedSub,Challenge.gateSlots_append,notSlots,
      List.length_append,List.length_cons,List.length_nil]
    simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,Challenge.instructionSlots,
      List.length_nil]
    omega

theorem coreI_sub (L : BalancedCircuit.Layout) (hw : L.Widths) :
    InstrSub (coreProgramI L) (BalancedCircuit.coreProgram L) := by
  simp only [coreProgramI,BalancedCircuit.coreProgram]
  exact (InstrSub.refl _).append ((InstrSub.refl _).append ((InstrSub.refl _).append
    ((foldI_sub L hw).append (InstrSub.refl _))))

theorem fieldProgramI_sub (w : Nat → Wire) (sign : Wire) :
    InstrSub (fieldProgramI w sign) (OffsetBorrowedField.program w sign) := by
  simp only [fieldProgramI,OffsetBorrowedField.program]
  exact (coreI_sub _ (balancedSharedPorts_widths w sign)).append (InstrSub.refl _)

theorem invFieldProgramI_sub (w : Nat → Wire) (sign : Wire) :
    InstrSub (invFieldProgramI w sign) (OffsetBorrowedInverse.program w sign) := by
  simp only [invFieldProgramI,OffsetBorrowedInverse.program,tailI,OffsetBorrowedInverse.tail]
  exact ((InstrSub.refl _).append (InstrSub.refl _)).append
    (((((((InstrSub.refl _).append (InstrSub.refl _)).append
      (undoFoldI_sub _ (balancedSharedPorts_widths w sign))).append (InstrSub.refl _)).append
      (InstrSub.refl _)).append (InstrSub.refl _)))

/-! ### Kernels wrapped by the sign flips -/

/-- Inside an `X sign` wrapper, the new forward kernel gives the old State. -/
theorem xwrap_forward_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (C : Program) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++(fieldProgramI w sign++C)) m s=
      run ([.X sign]++(OffsetBorrowedField.program w sign++C)) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  apply seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X sign] (m.take (measurementCount [.X sign])) s=u
  have us := BalancedCleanupOffset.x_run sign s (m.take (measurementCount [.X sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  apply seq_eq _ _ _ _ _ _ (fieldProgramI_counts w sign).2 _ rfl
  exact fieldProgram_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u _ ug ur uy ue

/-- Inside an `X sign` wrapper, the new inverse kernel gives the old State. -/
theorem xwrap_inverse_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (C : Program) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++(invFieldProgramI w sign++C)) m s=
      run ([.X sign]++(OffsetBorrowedInverse.program w sign++C)) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  apply seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X sign] (m.take (measurementCount [.X sign])) s=u
  have us := BalancedCleanupOffset.x_run sign s (m.take (measurementCount [.X sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  apply seq_eq _ _ _ _ _ _ (invFieldProgramI_counts w sign).2 _ rfl
  exact invField_eq w sign hn ho (centerFp X) (centerFp Y) (!base sign)
    (centerFp_bounds X) (centerFp_bounds Y) u _ ur uy ug ue.1 ue.2.1 ue.2.2

/-! ### Forward cell -/

def bodyFI (w : Nat → Wire) (sign effS : Wire) : Program :=
  [.X sign]++fieldProgramI w sign++[.X sign]++
    swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y

def cellFI (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (bodyFI w sign effS))

theorem bodyFI_counts (w : Nat → Wire) (sign effS : Wire) :
    measurementCount (bodyFI w sign effS)=measurementCount (OffsetBorrowedCanonical.body w sign effS) ∧
    toffoliCount (bodyFI w sign effS)+1=toffoliCount (OffsetBorrowedCanonical.body w sign effS) := by
  have c := fieldProgramI_counts w sign
  simp only [bodyFI,OffsetBorrowedCanonical.body,measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem cellFI_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    measurementCount (cellFI w b g swap sign effS ig is)=
      measurementCount (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) ∧
    toffoliCount (cellFI w b g swap sign effS ig is)+1=
      toffoliCount (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) := by
  have c := bodyFI_counts w sign effS
  exact ⟨window_counts_eq _ _ _ _ _ _ (window_counts_eq _ _ _ _ _ _ c.1),
    window_toffoli _ _ _ _ _ _ 1 (window_toffoli _ _ _ _ _ _ 1 c.2)⟩

theorem cellFI_sub (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    InstrSub (cellFI w b g swap sign effS ig is) (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) := by
  apply InstrSub.window; apply InstrSub.window
  simp only [bodyFI,OffsetBorrowedCanonical.body]
  exact (((InstrSub.refl _).append (fieldProgramI_sub w sign)).append (InstrSub.refl _)).append
    (InstrSub.refl _)

theorem bodyFI_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (bodyFI w sign effS) m s=run (OffsetBorrowedCanonical.body w sign effS) m s := by
  simp only [bodyFI,OffsetBorrowedCanonical.body,List.append_assoc]
  exact xwrap_forward_eq w sign hn ho base he X Y _ s m h

theorem cellFI_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (cellFI w b g swap sign effS ig is) m s=
      run (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have c := bodyFI_counts w sign effS
  apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _
    (window_counts_eq _ _ _ _ _ _ c.1) _ s m h
  intro t r ht
  apply window_eq b swap effS is _ _ ss (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS _ _ _ _ c.1 _ t r ht
  intro t' r' ht'
  exact bodyFI_eq w sign effS hn ho bs se X Y t' r' ht'

/-! ### Inverse cell -/

def doubleII (w : Nat → Wire) (sign : Wire) : Program :=
  [.X sign]++invFieldProgramI w sign++[.X sign]

def bodyII (w : Nat → Wire) (sign effS : Wire) : Program :=
  swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y++doubleII w sign

def cellII (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (bodyII w sign effS))

theorem bodyII_counts (w : Nat → Wire) (sign effS : Wire) :
    measurementCount (bodyII w sign effS)=measurementCount (OffsetBorrowedInverseCanonical.body w sign effS) ∧
    toffoliCount (bodyII w sign effS)+1=toffoliCount (OffsetBorrowedInverseCanonical.body w sign effS) := by
  have c := invFieldProgramI_counts w sign
  simp only [bodyII,doubleII,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double,
    measurementCount_append,toffoliCount_append]
  constructor <;> omega

theorem cellII_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    measurementCount (cellII w b g swap sign effS ig is)=
      measurementCount (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) ∧
    toffoliCount (cellII w b g swap sign effS ig is)+1=
      toffoliCount (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) := by
  have c := bodyII_counts w sign effS
  exact ⟨window_counts_eq _ _ _ _ _ _ (window_counts_eq _ _ _ _ _ _ c.1),
    window_toffoli _ _ _ _ _ _ 1 (window_toffoli _ _ _ _ _ _ 1 c.2)⟩

theorem cellII_sub (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) :
    InstrSub (cellII w b g swap sign effS ig is)
      (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) := by
  apply InstrSub.window; apply InstrSub.window
  simp only [bodyII,doubleII,OffsetBorrowedInverseCanonical.body,OffsetBorrowedInverseCanonical.double]
  exact (InstrSub.refl _).append (((InstrSub.refl _).append (invFieldProgramI_sub w sign)).append
    (InstrSub.refl _))

private theorem swap_pairI (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem bodyII_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (bodyII w sign effS) m s=run (OffsetBorrowedInverseCanonical.body w sign effS) m s := by
  let L := balancedSharedPorts w sign
  have len := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  simp only [bodyII,OffsetBorrowedInverseCanonical.body]
  apply seq_eq _ _ _ _ s m rfl rfl
  have sw := swap_pairI L.r L.y effS (len.2.1.trans len.2.2.1.symm) hsw base
    (centerWord X) (centerWord Y) s (m.take (measurementCount (swapRegisters effS L.r L.y))) h
  generalize run (swapRegisters effS L.r L.y) (m.take (measurementCount (swapRegisters effS L.r L.y))) s=u at sw ⊢
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) u.basis := by
    cases e : base effS <;> simpa only [A,B,e,Bool.false_eq_true,if_true,if_false] using sw.2
  simp only [doubleII,OffsetBorrowedInverseCanonical.double,List.append_assoc]
  exact xwrap_inverse_eq w sign hn ho base he A B _ u _ view

theorem cellII_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (cellII w b g swap sign effS ig is) m s=
      run (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have c := bodyII_counts w sign effS
  apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _
    (window_counts_eq _ _ _ _ _ _ c.1) _ s m h
  intro t r ht
  apply window_eq b swap effS is _ _ ss (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS _ _ _ _ c.1 _ t r ht
  intro t' r' ht'
  exact bodyII_eq w sign effS hn ho hl.swapND bs se X Y t' r' ht'

/-! ### Replays -/

def replayFI (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => cellFI w b l.1.1 l.1.2 sign effS l.2.1 l.2.2++replayFI w b sign effS ls

def replayII (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => replayII w b sign effS ls++cellII w b l.1.1 l.1.2 sign effS l.2.1 l.2.2

theorem replayFI_counts (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    measurementCount (replayFI w b sign effS ls)=measurementCount (OffsetBorrowedCanonical.replay w b sign effS ls) ∧
    toffoliCount (replayFI w b sign effS ls)+ls.length=toffoliCount (OffsetBorrowedCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => simp [replayFI,OffsetBorrowedCanonical.replay]
  | cons l ls ih =>
    have c := cellFI_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2
    simp only [replayFI,OffsetBorrowedCanonical.replay,measurementCount_append,toffoliCount_append,
      List.length_cons]
    constructor <;> omega

theorem replayII_counts (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    measurementCount (replayII w b sign effS ls)=measurementCount (OffsetBorrowedInverseCanonical.replay w b sign effS ls) ∧
    toffoliCount (replayII w b sign effS ls)+ls.length=toffoliCount (OffsetBorrowedInverseCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => simp [replayII,OffsetBorrowedInverseCanonical.replay]
  | cons l ls ih =>
    have c := cellII_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2
    simp only [replayII,OffsetBorrowedInverseCanonical.replay,measurementCount_append,toffoliCount_append,
      List.length_cons]
    constructor <;> omega

theorem replayFI_sub (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    InstrSub (replayFI w b sign effS ls) (OffsetBorrowedCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => exact InstrSub.refl _
  | cons l ls ih => exact (cellFI_sub _ _ _ _ _ _ _ _).append ih

theorem replayII_sub (w : Nat → Wire) (b sign effS : Wire) (ls : List MixedTranscriptLetter) :
    InstrSub (replayII w b sign effS ls) (OffsetBorrowedInverseCanonical.replay w b sign effS ls) := by
  induction ls with
  | nil => exact InstrSub.refl _
  | cons l ls ih => exact ih.append (cellII_sub _ _ _ _ _ _ _ _)

theorem replayFI_eq (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (replayFI w b sign effS ls) m s=run (OffsetBorrowedCanonical.replay w b sign effS ls) m s := by
  induction ls generalizing X Y s m with
  | nil => rfl
  | cons l ls ih =>
    let next := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have fr := OffsetBorrowedCanonical.cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he X Y
    simp only [replayFI,OffsetBorrowedCanonical.replay]
    apply seq_eq _ _ _ _ s m (cellFI_counts _ _ _ _ _ _ _ _).1
      (cellFI_eq w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl (ho sign (by simp)) (ho effS (by simp))
        base hg0 hs0 he X Y s _ h)
    exact ih (fun q hq => hf q (by simp [hq])) next.1 next.2 _ _ (fr s _ h).2

theorem replayII_eq (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (replayII w b sign effS ls) m s=run (OffsetBorrowedInverseCanonical.replay w b sign effS ls) m s := by
  induction ls generalizing X Y s m with
  | nil => rfl
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have hr : MixedTranscriptReplayLayout w b sign effS ls := fun q hq => hf q (by simp [hq])
    have fr := OffsetBorrowedInverseCanonical.replay_frame w b sign effS hn ls hr ho base hg0 hs0 he X Y
    simp only [replayII,OffsetBorrowedInverseCanonical.replay]
    apply seq_eq _ _ _ _ s m (replayII_counts _ _ _ _ _).1 (ih hr X Y s _ h)
    exact cellII_eq w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn hl (ho sign (by simp)) (ho effS (by simp))
      base hg0 hs0 he _ _ _ _ (fr s _ h).2

/-! ### Endpoint cells (no S window) -/

def trimFI (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig ([.X flag]++fieldProgramI w flag++[.X flag])

def trimII (w : Nat → Wire) (b g flag : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g flag ig ([.X flag]++invFieldProgramI w flag++[.X flag])

theorem trim_counts (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    measurementCount (trimFI w b g flag ig)=measurementCount (EndpointSwapTrim.forward w b g flag ig) ∧
    toffoliCount (trimFI w b g flag ig)+1=toffoliCount (EndpointSwapTrim.forward w b g flag ig) ∧
    measurementCount (trimII w b g flag ig)=measurementCount (EndpointSwapTrim.inverse w b g flag ig) ∧
    toffoliCount (trimII w b g flag ig)+1=toffoliCount (EndpointSwapTrim.inverse w b g flag ig) := by
  have f := fieldProgramI_counts w flag
  have i := invFieldProgramI_counts w flag
  have a : measurementCount ([.X flag]++fieldProgramI w flag++[.X flag])=
      measurementCount ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) := by
    simp only [measurementCount_append]; omega
  have b' : toffoliCount ([.X flag]++fieldProgramI w flag++[.X flag])+1=
      toffoliCount ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) := by
    simp only [toffoliCount_append]; omega
  have c : measurementCount ([.X flag]++invFieldProgramI w flag++[.X flag])=
      measurementCount ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag]) := by
    simp only [measurementCount_append]; omega
  have d : toffoliCount ([.X flag]++invFieldProgramI w flag++[.X flag])+1=
      toffoliCount ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag]) := by
    simp only [toffoliCount_append]; omega
  exact ⟨window_counts_eq _ _ _ _ _ _ a,window_toffoli _ _ _ _ _ _ 1 b',
    window_counts_eq _ _ _ _ _ _ c,window_toffoli _ _ _ _ _ _ 1 d⟩

theorem trim_sub (w : Nat → Wire) (b g flag : Wire) (ig : Bool) :
    InstrSub (trimFI w b g flag ig) (EndpointSwapTrim.forward w b g flag ig) ∧
    InstrSub (trimII w b g flag ig) (EndpointSwapTrim.inverse w b g flag ig) := by
  constructor
  · apply InstrSub.window
    exact ((InstrSub.refl _).append (fieldProgramI_sub w flag)).append (InstrSub.refl _)
  · apply InstrSub.window
    exact ((InstrSub.refl _).append (invFieldProgramI_sub w flag)).append (InstrSub.refl _)

theorem trim_eq (divide : Bool) (w : Nat → Wire) (b g swap sign effS : Wire) (ig : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false)
    (he : Env w base) (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (if divide then trimFI w b g sign ig else trimII w b g sign ig) m s=
      run (if divide then EndpointSwapTrim.forward w b g sign ig
        else EndpointSwapTrim.inverse w b g sign ig) m s := by
  let bg := mixedTranscriptBase base b g sign ig
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ge : Env w bg := env_write w sign ho base _ he
  have tc := trim_counts w b g sign ig
  have ci : measurementCount ([.X sign]++invFieldProgramI w sign++[.X sign])=
      measurementCount ([.X sign]++OffsetBorrowedInverse.program w sign++[.X sign]) := by
    have i := invFieldProgramI_counts w sign
    simp only [measurementCount_append]; omega
  have cf : measurementCount ([.X sign]++fieldProgramI w sign++[.X sign])=
      measurementCount ([.X sign]++OffsetBorrowedField.program w sign++[.X sign]) := by
    have i := fieldProgramI_counts w sign
    simp only [measurementCount_append]; omega
  cases divide
  · simp only [Bool.false_eq_true,if_false]
    apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
      (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _ ci _ s m h
    intro t r ht
    simp only [List.append_assoc]
    exact xwrap_inverse_eq w sign hn ho bg ge X Y _ t r ht
  · simp only [if_true]
    apply window_eq b g sign ig _ _ sg (hl.outside b (by simp)) (hl.outside g (by simp))
      (hl.outside sign (by simp [balancedSharedPorts])) base hg0 _ _ _ _ cf _ s m h
    intro t r ht
    simp only [List.append_assoc]
    exact xwrap_forward_eq w sign hn ho bg ge X Y _ t r ht

end ECDSAAdd.Entrant.LaneI

end


-- ===== ECDSAAdd.Submission.Entrant.Replay5 =====
section

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Replay5
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

def letters (j : Nat) : List MixedTranscriptLetter :=
  (List.range 5).map (fun k => tapeLetter (5*j+k))

def body (divide : Bool) (j : Nat) : Program :=
  if divide then LaneI.replayFI base (base 2400) (base 2409) (base 2410) (letters j)
  else LaneI.replayII base (base 2400) (base 2409) (base 2410) (letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++body divide j++History5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstSwap : Program :=
  EntryFieldSeedCancellation.selectedSwap base (base 2400) (base 1028) (base 2409) (base 2410)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def restLetters : List MixedTranscriptLetter :=
  (List.range' 1 4).map tapeLetter

def firstRest (divide : Bool) : Program :=
  if divide then LaneI.replayFI base (base 2400) (base 2409) (base 2410) restLetters
  else LaneI.replayII base (base 2400) (base 2409) (base 2410) restLetters

def firstBody (divide : Bool) : Program :=
  if divide then firstSwap++firstRest true else firstRest false++firstSwap

def baseFirstPacket (divide : Bool) : Program :=
  History5.decode base 0++firstBody divide++History5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  if divide then LaneI.trimFI base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  else LaneI.trimII base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def replay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

theorem letters_layouts
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    ∀j,j<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters j) := by
  intro j hj l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range.mp hk
  simpa only [tapeLetter] using mixedTape_getD_layout base (base 2400) (base 2409) (base 2410)
    hf (5*j+k) (by omega)

theorem history_controls (start i : Nat) (hi : i<5) :
    base (start+i)∈wires (History5.encode base start) ∧
      base (1028+start+i)∈wires (History5.encode base start) := by
  have a := History5.history_site_mem base start ⟨2*i,by omega⟩
  have b := History5.history_site_mem base start ⟨2*i+1,by omega⟩
  have ea : History5.historyMap base start ⟨2*i,by omega⟩=base (start+i) := by
    unfold History5.historyMap History5.historyId
    congr 1
    simp [Nat.mul_mod]
  have eb : History5.historyMap base start ⟨2*i+1,by omega⟩=base (1028+start+i) := by
    unfold History5.historyMap History5.historyId
    congr 1
    simp [Nat.add_mod,Nat.mul_mod]
    omega
  exact ⟨ea ▸ a,eb ▸ b⟩

theorem letters_controls (j : Nat) (hj : j<102) :
    ∀l∈letters j,l.1.1∈wires (History5.encode base (5*j)) ∧ l.1.2∈wires (History5.encode base (5*j)) := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range.mp hk
  have tape := mixedTape_base_getD (5*j+k) (by omega)
  simpa only [tapeLetter,tape,Nat.add_assoc] using history_controls (5*j) k bound

theorem raw_support (divide : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (shared : (sharedSites w sign).toFinset⊆W) (hb : b∈W) (he : eff∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) :
    wires (if divide then LaneI.replayFI w b sign eff ls else LaneI.replayII w b sign eff ls)⊆W := by
  induction ls with
  | nil => cases divide <;> simp [LaneI.replayFI,LaneI.replayII,wires]
  | cons l ls ih =>
    have cell := cells_active w b l.1.1 l.1.2 sign eff l.2.1 l.2.2 W shared hb
      (controls l (by simp)).1 (controls l (by simp)).2 he
    have f := (LaneI.cellFI_sub w b l.1.1 l.1.2 sign eff l.2.1 l.2.2).wires_sub.trans cell.1
    have i := (LaneI.cellII_sub w b l.1.1 l.1.2 sign eff l.2.1 l.2.2).wires_sub.trans cell.2
    have rest := ih (fun k hk => controls k (by simp [hk]))
    cases divide <;> simp only [Bool.false_eq_true,if_false,if_true,LaneI.replayFI,LaneI.replayII,
      wires_append,Finset.union_subset_iff] at rest ⊢
    · exact ⟨rest,i⟩
    · exact ⟨f,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) := by
  apply raw_support
  · intro q hq; exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
  · simp [History5.groupReadSites]
  · simp [History5.groupReadSites]
  · intro l hl
    have c := letters_controls j hj l hl
    exact ⟨Finset.mem_union_right _ c.1,Finset.mem_union_right _ c.2⟩

theorem raw_frame (divide : Bool) (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign eff ls)
    (ho : ∀q∈[b,sign,eff],q∉skywalkSharedWires w) (origin : BasisState)
    (hg0 : origin sign=false) (hs0 : origin eff=false) (env : Env w origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y))
      (if divide then LaneI.replayFI w b sign eff ls else LaneI.replayII w b sign eff ls)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin b ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin b ls) (X,Y)).2)) := by
  intro s m input
  cases divide
  · have same := LaneI.replayII_eq w b sign eff hn ls hf ho origin hg0 hs0 env X Y s m input
    simp only [Bool.false_eq_true,if_false] at same ⊢
    rw [same]
    simpa only [Bool.not_false,directionalPayload,if_true] using
      OffsetBorrowedInverseCanonical.replay_frame w b sign eff hn ls hf ho origin hg0 hs0 env X Y s m input
  · have same := LaneI.replayFI_eq w b sign eff hn ls hf ho origin hg0 hs0 env X Y s m input
    simp only [if_true] at same ⊢
    rw [same]
    simpa only [Bool.not_true,directionalPayload,Bool.false_eq_true,if_false] using
      OffsetBorrowedCanonical.replay_frame w b sign eff hn ls hf ho origin hg0 hs0 env X Y s m input

theorem body_counts (divide : Bool) (j : Nat)
    (hn : (skywalkSharedWires base).Nodup)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters j))
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base) :
    toffoliCount (body divide j)=5*(if divide then 1279 else 1280) ∧
      measurementCount (body divide j)=5125 := by
  have len : (letters j).length=5 := by simp [letters]
  have f := OffsetBorrowedCanonical.replay_counts base _ _ _ hn (letters j) hf ho
  have i := OffsetBorrowedInverseCanonical.replay_counts base _ _ _ hn (letters j) hf ho
  have fn := LaneI.replayFI_counts base (base 2400) (base 2409) (base 2410) (letters j)
  have iv := LaneI.replayII_counts base (base 2400) (base 2409) (base 2410) (letters j)
  rw [len] at f i fn iv
  cases divide <;> simp only [body,Bool.false_eq_true,if_false,if_true] <;> constructor <;> omega

theorem basePacket_frame (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (legal : History5.RawLegal base 102 origin) :
    (run (basePacket divide j) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters j)) (X,Y)).2
        (run (basePacket divide j) m s) := by
  exact History5.encoded_window_step base (base 2400) (base 2409) (base 2410) hn hp j hj origin
    X Y _ _ _ (body_support divide j hj)
    (raw_frame divide base (base 2400) (base 2409) (base 2410) hn (letters j) hf ho origin hg0 hs0 env X Y)
    s m input legal


theorem placed_eq (e : Equiv.Perm Nat) (P : Program)
    (fix : ∀q,¬Placement5.zeroRegion q → e q=q) (s : State) (m : List Bool)
    (input : ∀q,Placement5.zeroRegion q → s.basis (base q)=false)
    (output : ∀q,Placement5.zeroRegion q → (run P m s).basis (base q)=false) :
    run (renameProgram (shifted e) P) m s=run P m s := by
  apply pullState_perm_injective (shifted e)
  rw [run_rename _ (shifted e).injective,
    Placement5.shifted_zero_boundary e fix s input,
    Placement5.shifted_zero_boundary e fix (run P m s) output]

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have fresh := basePacket_frame divide j hj hn ho hp hf origin hg0 hs0 env X Y s m input legal
  have eq := placed_eq (Placement5.pi j) (basePacket divide j) (Placement5.pi_outside j · hj ·) s m
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal X Y s input)
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


def groupsPayload (divide : Bool) (origin : BasisState) (j n : Nat) (Q : Fp×Fp) : Fp×Fp :=
  PacketSequence.payload divide
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters k)) V) j n Q

theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters k))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (groupsPayload divide origin j n (X,Y)).1
        (groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (letters k)) V)
    (fun V t => History5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk hn ho hp (hf k hk) origin hg0 hs0 env legal
      V.1 V.2 t records h⟩) j n bound (X,Y) s m input
  exact result.2

def firstPayload (divide : Bool) (origin : BasisState) (Q : Fp×Fp) : Fp×Fp :=
  let S := mixedTranscriptBit origin (base 2400) (base 1028)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  if divide then directionalPayload false (mixedTranscriptControls origin (base 2400) restLetters)
      (if S then (Q.2,Q.1) else Q)
  else let V := directionalPayload true (mixedTranscriptControls origin (base 2400) restLetters) Q
    if S then (V.2,V.1) else V

private theorem rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem first_layout
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ hf 0 (by decide)) ho
  rw [mixedTape_base_getD 0 (by decide)] at layout
  exact layout

private theorem swap_rest_frame (r y : List Wire) (origin : BasisState) (S divide : Bool)
    (F : Fp×Fp → Fp×Fp) (sw rest : Program)
    (hs : ∀X Y, Triple (PairFrame r y origin (centerWord X) (centerWord Y)) sw
      (PairFrame r y origin (centerWord (if S then Y else X)) (centerWord (if S then X else Y))))
    (hr : ∀X Y, Triple (PairFrame r y origin (centerWord X) (centerWord Y)) rest
      (PairFrame r y origin (centerWord (F (X,Y)).1) (centerWord (F (X,Y)).2))) (X Y : Fp) :
    Triple (PairFrame r y origin (centerWord X) (centerWord Y))
      (if divide then sw++rest else rest++sw)
      (PairFrame r y origin
        (centerWord (if divide then F (if S then (Y,X) else (X,Y))
          else let V := F (X,Y); if S then (V.2,V.1) else V).1)
        (centerWord (if divide then F (if S then (Y,X) else (X,Y))
          else let V := F (X,Y); if S then (V.2,V.1) else V).2)) := by
  cases divide
  · have result := (hr X Y).seq (hs (F (X,Y)).1 (F (X,Y)).2)
    cases S <;> simpa only [Bool.false_eq_true,if_false,if_true] using result
  · have result := (hs X Y).seq (hr (if S then Y else X) (if S then X else Y))
    cases S <;> simpa only [Bool.false_eq_true,if_false,if_true] using result

theorem firstBody_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (firstPayload divide origin (X,Y)).1) (centerWord (firstPayload divide origin (X,Y)).2)) := by
  have swap := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (first_layout ho hf) origin hs0
  have rest := raw_frame divide base (base 2400) (base 2409) (base 2410) hn restLetters
    (rest_layout hf) ho origin hg0 hs0 env
  have result := swap_rest_frame (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y origin
    (mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2)
    divide (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) restLetters))
    firstSwap (firstRest divide) swap rest X Y
  cases divide <;> simpa only [firstBody,firstRest,firstPayload,Bool.false_eq_true,if_false,if_true,
    Bool.not_false,Bool.not_true] using result

theorem firstBody_support (divide : Bool) :
    wires (firstBody divide)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 := by
  let W := History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0
  have shared : (sharedSites base (base 2409)).toFinset⊆W :=
    fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hb : base 2400∈W := by simp [W,History5.groupReadSites]
  have he : base 2410∈W := by simp [W,History5.groupReadSites]
  have hs : base 1028∈W := Finset.mem_union_right _ (by simpa using (history_controls 0 0 (by decide)).2)
  have swap : wires firstSwap⊆W := by
    apply DirectSupport.selectWindow _ _ _ _ _ W hb hs he
    have sub : wires (swapRegisters (base 2410) (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y)⊆wires (OffsetBorrowedCanonical.body base (base 2409) (base 2410)) := by
      rw [OffsetBorrowedCanonical.body,wires_append]
      exact Finset.subset_union_right
    exact sub.trans (bodies_active base (base 2409) (base 2410) W shared he).1
  have rest : wires (firstRest divide)⊆W := by
    apply raw_support divide base (base 2400) (base 2409) (base 2410) restLetters W shared hb he
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    have controls := history_controls 0 k (by omega)
    simp only [Nat.zero_add] at controls
    simpa only [tapeLetter,tape] using
      (show base k∈W ∧ base (1028+k)∈W from
        ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩)
  cases divide <;> simp only [firstBody,Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff]
  · exact ⟨rest,swap⟩
  · exact ⟨swap,rest⟩

theorem firstPacket_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (firstPayload divide origin (X,Y)).1
        (firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := History5.encoded_window_step base (base 2400) (base 2409) (base 2410) hn hp 0 (by decide)
    origin X Y _ _ _ (firstBody_support divide) (firstBody_frame divide hn ho hf origin hg0 hs0 env X Y) s m input legal
  have eq := placed_eq (Placement5.pi 0) (baseFirstPacket divide) (Placement5.pi_outside 0 · (by decide) ·) s m
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal X Y s input)
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


def endPayload (divide : Bool) (origin : BasisState) (Q : Fp×Fp) : Fp×Fp :=
  let G := mixedTranscriptBit origin (base 2400) (base 510)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  (if divide then (Q.1+(if G then Q.2 else -Q.2))/2 else 2*Q.1+(if G then -Q.2 else Q.2),Q.2)

theorem rawEnd_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2400,base 510} := by
  let W := (sharedSites base (base 2409)).toFinset∪{base 2400,base 510}
  have shared : (sharedSites base (base 2409)).toFinset⊆W := Finset.subset_union_left
  have sign : base 2409∈W := shared (by simp [sharedSites])
  have x : wires [.X (base 2409)]⊆W := by simpa [wires,Instr.wires] using sign
  have f := (LaneI.fieldProgramI_sub base (base 2409)).wires_sub.trans
    (kernels_support base (base 2409)).1
  have i := (LaneI.invFieldProgramI_sub base (base 2409)).wires_sub.trans
    (kernels_support base (base 2409)).2
  have fw : wires ([.X (base 2409)]++LaneI.fieldProgramI base (base 2409)++[.X (base 2409)])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨x,f.trans shared⟩,x⟩
  have iv : wires ([.X (base 2409)]++LaneI.invFieldProgramI base (base 2409)++[.X (base 2409)])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨x,i.trans shared⟩,x⟩
  have hb : base 2400∈W := by simp [W]
  have hg : base 510∈W := by simp [W]
  cases divide <;> simp only [rawEnd,Bool.false_eq_true,if_false,if_true,LaneI.trimFI,LaneI.trimII]
  · exact DirectSupport.selectWindow _ _ _ _ _ W hb hg sign iv
  · exact DirectSupport.selectWindow _ _ _ _ _ W hb hg sign fw

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (History5.allEncode base 102)) (wires (rawEnd divide)) := by
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member base 102 q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q member
  have read := rawEnd_support divide used
  rcases Finset.mem_union.mp read with read|read
  · exact History5.history_active_away base (base 2409) hn (hp _ (by simp)) (5*j) (by omega) r
      (List.mem_toFinset.mp read)
  · have bound := History5.historyId_bound (5*j) (by omega) r
    have own : History5.historyMap base (5*j) r∈skywalkPoolWires base := by
      exact List.mem_map.mpr ⟨History5.historyId (5*j) r,by simp only [List.mem_range'_1]; omega,rfl⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at read
    rcases read with eq|eq
    · exact hp _ (by simp) (eq ▸ own)
    · have same := base_injective eq
      have rr := r.isLt
      unfold History5.historyId at same
      split_ifs at same <;> omega

theorem rawEnd_frame (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (env : Env base origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (endPayload divide origin (X,Y)).1) (centerWord (endPayload divide origin (X,Y)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ hf 510 (by decide)) ho
  rw [mixedTape_base_getD 510 (by decide)] at layout
  have nd : [base 2400,base 510,base 2409].Nodup := by decide
  have old := EndpointSwapTrim.partial_frame divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 hn (ho _ (by simp)) nd
    (layout.outside _ (by simp)) (layout.outside _ (by simp))
    (layout.outside _ (by simp [balancedSharedPorts])) origin hg0 env X Y
  intro s m input
  have same := LaneI.trim_eq divide base (base 2400) (base 510) (base 1538) (base 2409) (base 2410)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 hn layout (ho _ (by simp)) origin hg0 env X Y s m input
  simp only [rawEnd]
  rw [same]
  simpa only [endPayload] using old s m input

theorem endPacket_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (env : Env base origin)
    (legal : History5.RawLegal base 102 origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (endPayload divide origin (X,Y)).1
        (endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := History5.encoded_disjoint_step base (base 2409) (skywalkShared_integer_nodup base hn) origin
    X Y _ _ _ (rawEnd_disjoint divide hn hp) (rawEnd_frame divide hn ho hf origin hg0 env X Y) s m input
  have eq := placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal X Y s input)
    (History5.encoded_zero_region base (base 2409) hn (hp _ (by simp)) origin env legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] indexedLetters mixedTranscriptTape mixedTranscriptUnitTrace
  PenultimateSwapIdentity.penultimatePayload trimLetters groupsPayload firstPayload endPayload
  SkywalkTrace.trace SkywalkTrace.next Nat.iterate

private theorem forward_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplay (a++b) Q=skywalkPayloadReplay b (skywalkPayloadReplay a Q) := by
  induction a generalizing Q with
  | nil => rfl
  | cons l ls ih => exact ih (skywalkPayloadCell l.1 l.2 Q)

private theorem inverse_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplayInverse (a++b) Q=skywalkPayloadReplayInverse a (skywalkPayloadReplayInverse b Q) := by
  induction a with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append,skywalkPayloadReplayInverse,ih]

attribute [local irreducible] skywalkPayloadReplay skywalkPayloadReplayInverse

theorem letters_indexed (j : Nat) : letters j=indexedLetters (5*j) 5 := by
  simp only [letters,indexedLetters]
theorem letters_zero : letters 0=tapeLetter 0::restLetters := by
  simp only [letters,restLetters,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
  rfl

private theorem groups_forward_succ (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
      (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (letters j)) Q) := by
  simp only [groupsPayload,PacketSequence.payload,if_true,Bool.not_true,directionalPayload,
    Bool.false_eq_true,if_false]

private theorem groups_inverse_succ (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload false origin j (n+1) Q=skywalkPayloadReplayInverse
      (mixedTranscriptControls origin (base 2400) (letters j)) (groupsPayload false origin (j+1) n Q) := by
  simp only [groupsPayload,PacketSequence.payload,Bool.false_eq_true,if_false,Bool.not_false,
    directionalPayload,if_true]

theorem forward_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload true origin j n Q=skywalkPayloadReplay
      (mixedTranscriptControls origin (base 2400) (indexedLetters (5*j) (5*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,PacketSequence.payload,indexedLetters,Nat.mul_zero,List.range_zero,
      List.map_nil,mixedTranscriptControls,skywalkPayloadReplay]
  | succ n ih =>
    have recur : groupsPayload true origin j (n+1) Q=groupsPayload true origin (j+1) n
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (letters j)) Q) := groups_forward_succ j n origin Q
    have len : 5*(n+1)=5+5*n := by omega
    have start : 5*(j+1)=5*j+5 := by omega
    rw [recur,ih,len,indexedLetters_append]
    simp only [mixedTranscriptControls,List.map_append,forward_append,start,←letters_indexed]

theorem inverse_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload false origin j n Q=skywalkPayloadReplayInverse
      (mixedTranscriptControls origin (base 2400) (indexedLetters (5*j) (5*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,PacketSequence.payload,indexedLetters,Nat.mul_zero,List.range_zero,
      List.map_nil,mixedTranscriptControls,skywalkPayloadReplayInverse]
  | succ n ih =>
    have recur : groupsPayload false origin j (n+1) Q=skywalkPayloadReplayInverse
        (mixedTranscriptControls origin (base 2400) (letters j)) (groupsPayload false origin (j+1) n Q) := groups_inverse_succ j n origin Q
    have len : 5*(n+1)=5+5*n := by omega
    have start : 5*(j+1)=5*j+5 := by omega
    rw [recur,ih,len,indexedLetters_append]
    simp only [mixedTranscriptControls,List.map_append,inverse_append,start,←letters_indexed]

private theorem first_forward_payload (origin : BasisState) (Y : Fp) :
    firstPayload true origin (Y,0)=skywalkPayloadReplay
      (mixedTranscriptControls origin (base 2400) (letters 0)) (2*Y,0) := by
  have half : (2*Y)/2=Y := mul_div_cancel_left₀ Y (by decide)
  rw [letters_zero]
  simp only [firstPayload,if_true,directionalPayload,Bool.false_eq_true,if_false,
    mixedTranscriptControls,List.map_cons,skywalkPayloadReplay]
  rw [show tapeLetter 0=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from
    mixedTape_base_getD 0 (by decide)]
  simp only [skywalkPayloadCell,neg_zero,ite_self,add_zero,half]

private theorem first_inverse_of_full (origin : BasisState) (Q : Fp×Fp) (Z : Fp)
    (old : skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) (letters 0)) Q=(2*Z,0)) :
    firstPayload false origin Q=(Z,0) := by
  rw [letters_zero] at old
  simp only [mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse] at old
  rw [show tapeLetter 0=((base 0,base 1028),mixedTranscriptUnitTrace.getD 0 (false,false)) from
    mixedTape_base_getD 0 (by decide)] at old
  have removed := EntryInversePayload.remove_final_double _ _ _ Z old
  simpa only [firstPayload,Bool.false_eq_true,if_false,directionalPayload,if_true,mixedTranscriptControls] using removed

private theorem trim_split : trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
  have one : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  have split := indexedLetters_append 0 510 1
  rw [one] at split
  simpa only [Nat.zero_add,trimLetters] using split

theorem forward_payload (origin : BasisState) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    endPayload true origin (groupsPayload true origin 1 101 (firstPayload true origin (Y,0)))=(Z,Z) := by
  let A := PenultimateSwapIdentity.penultimatePayload origin Y
  have middle : groupsPayload true origin 1 101 (firstPayload true origin (Y,0))=A := by
    have recur : groupsPayload true origin 0 102 (2*Y,0)=groupsPayload true origin 1 101
        (skywalkPayloadReplay (mixedTranscriptControls origin (base 2400) (letters 0)) (2*Y,0)) := groups_forward_succ 0 101 origin (2*Y,0)
    rw [first_forward_payload,←recur,forward_groups_payload]
    unfold A PenultimateSwapIdentity.penultimatePayload
    simp only [Nat.reduceMul]
  rw [middle]
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have whole := trimLetters_quotient origin x Y hx0 hx trace
  rw [trim_split] at whole
  simp only [mixedTranscriptControls,List.map_append,forward_append,List.map_cons,List.map_nil,
    skywalkPayloadReplay] at whole
  have letter := mixedTape_base_getD 510 (by decide)
  rw [show tapeLetter 510=((base 510,base 1538),mixedTranscriptUnitTrace.getD 510 (false,false)) from letter] at whole
  have dup := PenultimateSwapIdentity.penultimate_half_dup origin x Y hx0 hx trace
  rw [show tapeLetter 510=((base 510,base 1538),mixedTranscriptUnitTrace.getD 510 (false,false)) from letter] at dup
  change (A.1+(if mixedTranscriptBit origin (base 2400) (base 510)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 then A.2 else -A.2))/2=A.2 at dup
  have same : skywalkPayloadCell
      (mixedTranscriptBit origin (base 2400) (base 510) (mixedTranscriptUnitTrace.getD 510 (false,false)).1)
      (mixedTranscriptBit origin (base 2400) (base 1538) (mixedTranscriptUnitTrace.getD 510 (false,false)).2) A=(A.2,A.2) := by
    simp only [skywalkPayloadCell,dup]
    split <;> rfl
  have foldPayload : skywalkPayloadReplay
      (List.map (fun l : MixedTranscriptLetter =>
        (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1,
         mixedTranscriptBit origin (base 2400) l.1.2 l.2.2)) (indexedLetters 0 510)) (2*Y,0)=A := by
    unfold A PenultimateSwapIdentity.penultimatePayload mixedTranscriptControls
    rfl
  rw [foldPayload] at whole
  have out : (A.2,A.2)=(Z,Z) := same.symm.trans whole
  simpa only [endPayload,if_true,dup] using out

theorem inverse_payload (origin : BasisState) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    firstPayload false origin (groupsPayload false origin 1 101 (endPayload false origin (Y,Y)))=(Z,0) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  let A := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (Y,Y)
  have head : endPayload false origin (Y,Y)=A := by
    have letter := mixedTape_base_getD 510 (by decide)
    simp only [A,mixedTranscriptControls,List.map_cons,List.map_nil,skywalkPayloadReplayInverse,tapeLetter,letter]
    simp only [skywalkPayloadUncell,endPayload,Bool.false_eq_true,if_false]
    simp only [ite_self,Prod.fst,Prod.snd]
  rw [head]
  apply first_inverse_of_full
  have recur : groupsPayload false origin 0 102 A=skywalkPayloadReplayInverse
      (mixedTranscriptControls origin (base 2400) (letters 0)) (groupsPayload false origin 1 101 A) := groups_inverse_succ 0 101 origin A
  rw [←recur,inverse_groups_payload]
  have old := EntryInversePayload.inverse_boundary origin x Y hx0 hx trace
  rw [EntryInversePayload.inverse_groups_payload] at old
  exact old

theorem forward_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (replay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true hn ho hp hf origin hg0 hs0 env legal Y 0 a m1 h
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) hn ho hp (letters_layouts hf)
        origin hg0 hs0 env legal _ _ b m2 first.2
      rw [hbc] at middle
      have last := endPacket_frame true hn ho hp hf origin hg0 env legal _ _ c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [replay,if_true,List.append_assoc] using result input

theorem inverse_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (replay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false hn ho hp hf origin hg0 env legal Y Y a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) hn ho hp (letters_layouts hf)
        origin hg0 hs0 env legal _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false hn ho hp hf origin hg0 hs0 env legal _ _ c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [replay,Bool.false_eq_true,if_false,List.append_assoc] using result input

section Counts

private theorem sign_pairND (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w) :
    (sign::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts w sign) nd sign
    (by simp [balancedSharedPorts])
  exact List.nodup_cons.mpr ⟨by
    intro h
    rcases List.mem_append.mp h with h|h
    · exact aw (by simp [h])
    · exact aw (by simp [h]),balancedSharedLayout_pairND w sign hn⟩

theorem packet_counts (divide : Bool) (j : Nat)
    (hn : (skywalkSharedWires base).Nodup)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters j))
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base) :
    toffoliCount (packet divide j)=(if divide then 6415 else 6420) ∧
      measurementCount (packet divide j)=5131 := by
  have raw := body_counts divide j hn hf ho
  have e := History5.encode_counts base (5*j)
  have d := History5.decode_counts base (5*j)
  have renamed := renameProgram_counts (shifted (Placement5.pi j)) (basePacket divide j)
  change toffoliCount (renameProgram _ (basePacket divide j))=_ ∧
    measurementCount (renameProgram _ (basePacket divide j))=_
  rw [renamed.1,renamed.2]
  simp only [basePacket,toffoliCount_append,measurementCount_append]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at raw ⊢
  all_goals constructor <;> omega


theorem groups_counts (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (letters k))
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base) :
    toffoliCount (groups divide j n)=n*(if divide then 6415 else 6420) ∧
      measurementCount (groups divide j n)=n*5131 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_counts divide j hn (hf j (by omega)) ho
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append] at head rest ⊢
    all_goals constructor <;> omega


theorem firstSwap_counts
    (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount firstSwap=257 ∧ measurementCount firstSwap=1 := by
  have width := BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  have sw := swapRegisters_resources (base 2410) _ _ (width.2.1.trans width.2.2.1.symm)
    (sign_pairND base (base 2410) hn ho)
  have sel := transcriptSelectWindow_counts (base 2400) (base 1028) (base 2410)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters (base 2410) (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y)
  simp only [firstSwap,EntryFieldSeedCancellation.selectedSwap,sel.1,sel.2,sw.1,sw.2.1,width.2.1]
  norm_num

theorem firstPacket_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base) :
    toffoliCount (firstPacket divide)=(if divide then 5393 else 5397) ∧
      measurementCount (firstPacket divide)=4107 := by
  have len : restLetters.length=4 := by simp only [restLetters,List.length_map,List.length_range']
  have f := OffsetBorrowedCanonical.replay_counts base _ _ _ hn restLetters (rest_layout hf) ho
  have i := OffsetBorrowedInverseCanonical.replay_counts base _ _ _ hn restLetters (rest_layout hf) ho
  have fn := LaneI.replayFI_counts base (base 2400) (base 2409) (base 2410) restLetters
  have iv := LaneI.replayII_counts base (base 2400) (base 2409) (base 2410) restLetters
  rw [len] at f i fn iv
  have sw := firstSwap_counts hn (ho _ (by simp))
  have e := History5.encode_counts base 0
  have d := History5.decode_counts base 0
  have renamed := renameProgram_counts (shifted (Placement5.pi 0)) (baseFirstPacket divide)
  change toffoliCount (renameProgram _ (baseFirstPacket divide))=_ ∧
    measurementCount (renameProgram _ (baseFirstPacket divide))=_
  rw [renamed.1,renamed.2]
  simp only [baseFirstPacket,firstBody,firstRest,toffoliCount_append,measurementCount_append]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true,toffoliCount_append,measurementCount_append]
  all_goals constructor <;> omega


theorem endPacket_counts (divide : Bool) :
    toffoliCount (endPacket divide)=(if divide then 1022 else 1023) ∧
      measurementCount (endPacket divide)=1024 := by
  have old := EndpointSwapTrim.counts base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  have fresh := LaneI.trim_counts base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  have renamed := renameProgram_counts (shifted Placement5.pi0) (rawEnd divide)
  simp only [endPacket,renamed.1,renamed.2]
  cases divide <;> simp only [rawEnd,Bool.false_eq_true,if_false,if_true]
  all_goals constructor <;> omega

theorem replay_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base) :
    toffoliCount (replay divide)=(if divide then 654330 else 654840) ∧
      measurementCount (replay divide)=523362 := by
  have first := firstPacket_counts divide hn hf ho
  have rest := groups_counts divide 1 101 (by decide) hn (letters_layouts hf) ho
  have last := endPacket_counts divide
  cases divide <;> simp only [replay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at first rest last ⊢
  all_goals constructor <;> omega


end Counts

section Physical
open RecordedQuantum





























































































































end Physical

section Slots
open Challenge Baselines
attribute [local irreducible] gateSlots






























































end Slots

end ECDSAAdd.Entrant.Replay5

end


section
-- ===== AccBuild =====

/-! Short integer accumulator for fold corrections.
A list of signed shifted sources is summed exactly (no modular reduction)
into a short accumulator by in-place adders/subtractors, then removed again
by the inverse operations in reverse order. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.Acc
open Arithmetic

def tx (Z : List Wire) (w : Nat) (f : MeasuredSquareFold) : List Wire :=
  f.src++Z.take (w-f.shift-f.src.length)
def ty (acc : List Wire) (f : MeasuredSquareFold) : List Wire := acc.drop f.shift
def tc (bank : List Wire) (w : Nat) (f : MeasuredSquareFold) : List Wire := bank.take (w-f.shift-1)

def op (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold) : Program :=
  if neg then subInPlace (tx Z w f) (ty acc f) (tc bank w f) cin
  else addInPlace (tx Z w f) (ty acc f) (tc bank w f) cin

def build (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => op acc Z bank cin w f.negative f++build acc Z bank cin w fs

def unbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => unbuild acc Z bank cin w fs++op acc Z bank cin w (!f.negative) f

def step (base : BasisState) (neg : Bool) (V : Nat) (f : MeasuredSquareFold) : Nat :=
  if neg then V-regValue f.src base*2^f.shift else V+regValue f.src base*2^f.shift

def accVal (base : BasisState) : Nat → List MeasuredSquareFold → Nat
  | V,[] => V
  | V,f::fs => accVal base (step base f.negative V f) fs

def Valid (base : BasisState) (w : Nat) : Nat → List MeasuredSquareFold → Prop
  | _,[] => True
  | V,f::fs => (if f.negative then regValue f.src base*2^f.shift≤V
      else V+regValue f.src base*2^f.shift<2^w) ∧ Valid base w (step base f.negative V f) fs

structure FitsLen (Z bank : List Wire) (w : Nat) (f : MeasuredSquareFold) : Prop where
  len : f.src.length+f.shift<w
  zpad : w-f.shift-f.src.length≤Z.length
  bankLen : w-f.shift-1≤bank.length

structure Fits (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold) : Prop
    extends FitsLen Z bank w f where
  nd : (cin::(f.src++acc++Z++bank)).Nodup

theorem fits_lengths (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    (tx Z w f).length=(ty acc f).length ∧ (tc bank w f).length+1=(ty acc f).length ∧
      (ty acc f).length=w-f.shift := by
  have l := hf.len; have z := hf.zpad; have b := hf.bankLen
  simp only [tx,ty,tc,List.length_append,List.length_take,List.length_drop,hacc]
  rw [Nat.min_eq_left z,Nat.min_eq_left b]
  refine ⟨?_,?_,?_⟩
  · generalize f.src.length=k at l ⊢
    generalize f.shift=j at l ⊢
    omega
  · generalize f.shift=j at l ⊢
    omega
  · trivial

theorem fits_nodup (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hf : Fits acc Z bank cin w f) :
    (cin::(tx Z w f++ty acc f++tc bank w f)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hf.nd q
  have a := (List.take_sublist (w-f.shift-f.src.length) Z).count_le q
  have b := (List.drop_sublist f.shift acc).count_le q
  have c := (List.take_sublist (w-f.shift-1) bank).count_le q
  simp only [tx,ty,tc,List.count_cons,List.count_append] at h a b c ⊢
  omega

theorem op_wires (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (op acc Z bank cin w neg f)=(cin::(tx Z w f++ty acc f++tc bank w f)).toFinset := by
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  cases neg
  · simp only [op,Bool.false_eq_true,if_false]
    exact addInPlace_wires _ _ _ _ L.1 L.2.1
  · simp only [op,if_true,subInPlace,wires_append,notRegister_wires,addInPlace_wires _ _ _ _ L.1 L.2.1]
    ext q
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto

theorem op_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (op acc Z bank cin w neg f)⊆(cin::(f.src++acc++Z++bank)).toFinset := by
  rw [op_wires acc Z bank cin w neg f hacc hf]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,tx,ty,tc] at hq ⊢
  rcases hq with h|((h|h)|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inr (List.mem_of_mem_take h)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr (List.mem_of_mem_drop h))))
  · exact Or.inr (Or.inr (List.mem_of_mem_take h))

theorem op_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    toffoliCount (op acc Z bank cin w neg f)=w-f.shift-1 ∧
    measurementCount (op acc Z bank cin w neg f)=w-f.shift-1 := by
  have L := fits_lengths acc Z bank cin w f hacc hf
  have c := addInPlace_counts (tx Z w f) (ty acc f) (tc bank w f) cin L.1 L.2.1
  rw [L.2.2] at c
  have n := notRegister_counts (ty acc f)
  cases neg
  · simpa only [op,Bool.false_eq_true,if_false] using c
  · simp only [op,if_true,subInPlace,toffoliCount_append,measurementCount_append,n.1,n.2,c.1,c.2]
    omega

theorem op_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold)
    (hf : Fits acc Z bank cin w f) : GatePhysical (op acc Z bank cin w neg f) := by
  have nd := fits_nodup acc Z bank cin w f hf
  have nd' : (cin::tx Z w f++ty acc f++tc bank w f).Nodup := by simpa using nd
  cases neg
  · simpa only [op,Bool.false_eq_true,if_false] using addInPlace_physical _ _ _ _ nd'
  · simpa only [op,if_true] using subInPlace_physical _ _ _ _ nd'

theorem op_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (neg : Bool) (f : MeasuredSquareFold) :
    Challenge.gateSlots (op acc Z bank cin w neg f)≤12*(tx Z w f).length+2*(ty acc f).length := by
  have a := Baselines.addInPlace_gateSlots_le (tx Z w f) (ty acc f) (tc bank w f) cin
  have b := Baselines.subInPlace_gateSlots_le (tx Z w f) (ty acc f) (tc bank w f) cin
  cases neg
  · simp only [op,Bool.false_eq_true,if_false]; omega
  · simp only [op,if_true]; omega

/-- One exact signed shifted accumulation step. -/
theorem op_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) (base : BasisState)
    (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (neg : Bool) (V : Nat)
    (hok : if neg then regValue f.src base*2^f.shift≤V else V+regValue f.src base*2^f.shift<2^w) :
    Triple (SquareFrame acc base V) (op acc Z bank cin w neg f)
      (SquareFrame acc base (step base neg V f)) := by
  intro s m hs
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have nd := fits_nodup acc Z bank cin w f hf
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  let T := regValue f.src base
  let x := tx Z w f
  let y := ty acc f
  let c := tc bank w f
  have xv : regValue x s.basis=T := by
    have zero : regValue (Z.take (w-f.shift-f.src.length)) s.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have hq' := List.mem_of_mem_take hq
      exact (same q (Or.inl (by simp [hq']))).trans (hz q hq')
    have src : regValue f.src s.basis=T :=
      regValue_congr _ _ _ (fun q hq => same q (Or.inl (by simp [hq])))
    simp only [x,tx,regValue_append,zero,src,Nat.mul_zero,Nat.add_zero]
  have cv : regValue c s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hq' := List.mem_of_mem_take hq
    exact (same q (Or.inl (by simp [hq']))).trans (hb q hq')
  have iv : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have accNd : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop accNd (show f.shift≤f.shift by omega)
  have shiftLe : f.shift≤acc.length := by have := hf.len; omega
  have split (t : BasisState) : regValue acc t=regValue (acc.take f.shift) t+2^f.shift*regValue y t := by
    have h := regValue_append (acc.take f.shift) (acc.drop f.shift) t
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left shiftLe] at h
    exact h
  have lowLt : regValue (acc.take f.shift) s.basis<2^f.shift := by
    have h := regValue_lt (acc.take f.shift) s.basis
    rwa [List.length_take,Nat.min_eq_left shiftLe] at h
  have yLt : regValue y s.basis<2^(w-f.shift) := by
    have h := regValue_lt y s.basis; rwa [L.2.2] at h
  have vsplit := split s.basis
  rw [hs.1] at vsplit
  -- the operation's own spec: values of x, y, cin, carry
  have post : (run (op acc Z bank cin w neg f) m s).phase=s.phase ∧
      regValue x (run (op acc Z bank cin w neg f) m s).basis=T ∧
      regValue y (run (op acc Z bank cin w neg f) m s).basis=
        (if neg then (regValue y s.basis+2^y.length-T)%2^y.length
          else (T+regValue y s.basis)%2^y.length) ∧
      (run (op acc Z bank cin w neg f) m s).basis cin=false ∧
      regValue c (run (op acc Z bank cin w neg f) m s).basis=0 := by
    cases neg
    · have h := addInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) false s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds,Bool.toNat_false,Nat.add_zero] at h
      simp only [op,Bool.false_eq_true,if_false]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
    · have h := subInPlace_spec x y c cin nd L.1 L.2.1 T (regValue y s.basis) s m
        ⟨⟨⟨xv,rfl⟩,iv⟩,cv⟩
      simp only [Holds.holds] at h
      simp only [op,if_true]
      exact ⟨h.1,h.2.1.1.1,h.2.1.1.2,h.2.1.2,h.2.2⟩
  let r := run (op acc Z bank cin w neg f) m s
  have frame (q : Wire) (hq : q∉y) : r.basis q=s.basis q := by
    by_cases hx : q∈x
    · exact (regValue_eq_iff x r.basis s.basis).mp (post.2.1.trans xv.symm) q hx
    by_cases hc : q∈c
    · exact ((regValue_zero _ _).mp post.2.2.2.2 q hc).trans ((regValue_zero _ _).mp cv q hc).symm
    by_cases hi' : q=cin
    · subst q; exact post.2.2.2.1.trans iv.symm
    apply run_preserves_outside
    rw [op_wires acc Z bank cin w neg f hacc hf]
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  have lowSame : regValue (acc.take f.shift) r.basis=regValue (acc.take f.shift) s.basis :=
    regValue_congr _ _ _ (fun q hq => frame q (fun hy => List.disjoint_left.mp dis hq hy))
  refine ⟨post.1,?_,?_⟩
  · rw [split r.basis,lowSame,post.2.2.1]
    rw [L.2.2]
    have hok' := hok
    simp only [T] at post ⊢
    generalize hlo : regValue (acc.take f.shift) s.basis=lo at vsplit lowLt
    generalize hY : regValue y s.basis=Y at vsplit yLt ⊢
    generalize hT : regValue f.src base=T0 at hok' ⊢
    have pw : 2^w=2^f.shift*2^(w-f.shift) := by
      rw [←pow_add]; congr 1; have := hf.len; omega
    cases neg
    · simp only [Bool.false_eq_true,if_false] at hok' ⊢
      simp only [step,Bool.false_eq_true,if_false,hT]
      have bound : T0+Y<2^(w-f.shift) := by
        have h1 : 2^f.shift*(T0+Y)<2^f.shift*2^(w-f.shift) := by
          rw [←pw]; rw [vsplit] at hok'; nlinarith
        exact Nat.lt_of_mul_lt_mul_left h1
      rw [Nat.mod_eq_of_lt bound,vsplit]
      ring
    · simp only [if_true] at hok' ⊢
      simp only [step,if_true,hT]
      have le : T0≤Y := by
        by_contra hlt
        have h1 : 2^f.shift*(Y+1)≤2^f.shift*T0 := Nat.mul_le_mul_left _ (by omega)
        rw [vsplit] at hok'
        nlinarith
      have e : Y+2^(w-f.shift)-T0=(Y-T0)+2^(w-f.shift) := by omega
      rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),vsplit,Nat.mul_sub]
      have m1 : 2^f.shift*T0≤2^f.shift*Y := Nat.mul_le_mul_left _ le
      have m2 : T0*2^f.shift=2^f.shift*T0 := Nat.mul_comm _ _
      omega
  · intro q hq
    have hy : q∉y := fun h => hq (List.mem_of_mem_drop h)
    exact (frame q hy).trans (hs.2 q hq)

theorem step_valid_lt (base : BasisState) (w : Nat) (V : Nat) (f : MeasuredSquareFold) (hV : V<2^w)
    (h : if f.negative then regValue f.src base*2^f.shift≤V else V+regValue f.src base*2^f.shift<2^w) :
    step base f.negative V f<2^w := by
  cases hn : f.negative <;> simp only [hn,step,Bool.false_eq_true,if_false,if_true] at h ⊢ <;> omega

theorem accVal_lt (base : BasisState) (w : Nat) (fs : List MeasuredSquareFold) :
    ∀ V,V<2^w → Valid base w V fs → accVal base V fs<2^w := by
  induction fs with
  | nil => intro V hV _; exact hV
  | cons f fs ih =>
    intro V hV hv
    exact ih _ (step_valid_lt base w V f hV hv.1) hv.2

theorem build_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    ∀ V,Valid base w V fs → Triple (SquareFrame acc base V) (build acc Z bank cin w fs)
      (SquareFrame acc base (accVal base V fs)) := by
  induction fs with
  | nil => intro V _ s m h; exact ⟨rfl,h⟩
  | cons f fs ih =>
    intro V hv
    have h1 := op_triple acc Z bank cin w f hacc (hf f (by simp)) base hz hb hi f.negative V hv.1
    have h2 := ih (fun g hg => hf g (by simp [hg])) _ hv.2
    exact h1.seq h2

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    ∀ V,V<2^w → Valid base w V fs → Triple (SquareFrame acc base (accVal base V fs))
      (unbuild acc Z bank cin w fs) (SquareFrame acc base V) := by
  induction fs with
  | nil => intro V _ _ s m h; exact ⟨rfl,h⟩
  | cons f fs ih =>
    intro V hV hv
    have V1 := step_valid_lt base w V f hV hv.1
    have h1 := ih (fun g hg => hf g (by simp [hg])) _ V1 hv.2
    have ok : if (!f.negative) then regValue f.src base*2^f.shift≤step base f.negative V f
        else step base f.negative V f+regValue f.src base*2^f.shift<2^w := by
      have := hv.1
      cases hn : f.negative <;> simp only [hn,step,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_true,if_false] at this ⊢ <;> omega
    have h2 := op_triple acc Z bank cin w f hacc (hf f (by simp)) base hz hb hi (!f.negative) _ ok
    have back : step base (!f.negative) (step base f.negative V f) f=V := by
      have := hv.1
      cases hn : f.negative <;> simp only [hn,step,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        if_true,if_false] at this ⊢ <;> omega
    rw [back] at h2
    exact h1.seq h2

theorem valid_congr (b1 b2 : BasisState) (w : Nat) (fs : List MeasuredSquareFold)
    (h : ∀f∈fs,regValue f.src b1=regValue f.src b2) :
    ∀ V,(Valid b1 w V fs ↔ Valid b2 w V fs) ∧ accVal b1 V fs=accVal b2 V fs := by
  induction fs with
  | nil => intro V; exact ⟨Iff.rfl,rfl⟩
  | cons f fs ih =>
    intro V
    have e := h f (by simp)
    have t := ih (fun g hg => h g (by simp [hg]))
    have se : step b1 f.negative V f=step b2 f.negative V f := by simp only [step,e]
    simp only [Valid,accVal,e,se]
    exact ⟨and_congr_right (fun _ => (t _).1),(t _).2⟩

theorem accVal_cast (base : BasisState) (w : Nat) (fs : List MeasuredSquareFold) :
    ∀ V,Valid base w V fs →
      (accVal base V fs : ZMod SquareReduction.p)=V+CuccaroStreamedSquareWideLayout.measuredSignedSum base fs := by
  induction fs with
  | nil => intro V _; simp [accVal,CuccaroStreamedSquareWideLayout.measuredSignedSum]
  | cons f fs ih =>
    intro V hv
    rw [accVal,ih _ hv.2]
    have h1 := hv.1
    simp only [CuccaroStreamedSquareWideLayout.measuredSignedSum,
      CuccaroStreamedSquareWideLayout.measuredSignedPayload,
      CuccaroStreamedSquareWideLayout.measuredFoldPayload]
    cases hn : f.negative <;> simp only [hn,step,Bool.false_eq_true,if_false,if_true] at h1 ⊢
    · push_cast; ring
    · rw [Nat.cast_sub h1]; push_cast; ring

def buildT (w : Nat) : List MeasuredSquareFold → Nat
  | [] => 0
  | f::fs => (w-f.shift-1)+buildT w fs

theorem build_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    (toffoliCount (build acc Z bank cin w fs)=buildT w fs ∧
      measurementCount (build acc Z bank cin w fs)=buildT w fs) ∧
    (toffoliCount (unbuild acc Z bank cin w fs)=buildT w fs ∧
      measurementCount (unbuild acc Z bank cin w fs)=buildT w fs) := by
  induction fs with
  | nil => simp [build,unbuild,buildT,toffoliCount,measurementCount]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    have a := op_counts acc Z bank cin w f.negative f hacc (hf f (by simp))
    have b := op_counts acc Z bank cin w (!f.negative) f hacc (hf f (by simp))
    simp only [build,unbuild,buildT,toffoliCount_append,measurementCount_append]
    refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> omega

theorem build_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (S : Finset Wire)
    (hS : ∀f∈fs,(cin::(f.src++acc++Z++bank)).toFinset⊆S) :
    wires (build acc Z bank cin w fs)⊆S ∧ wires (unbuild acc Z bank cin w fs)⊆S := by
  induction fs with
  | nil => simp [build,unbuild,wires]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg])) (fun g hg => hS g (by simp [hg]))
    have a := (op_support acc Z bank cin w f.negative f hacc (hf f (by simp))).trans (hS f (by simp))
    have b := (op_support acc Z bank cin w (!f.negative) f hacc (hf f (by simp))).trans (hS f (by simp))
    simp only [build,unbuild,wires_append,Finset.union_subset_iff]
    exact ⟨⟨a,t.1⟩,⟨t.2,b⟩⟩

theorem build_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    GatePhysical (build acc Z bank cin w fs) ∧ GatePhysical (unbuild acc Z bank cin w fs) := by
  induction fs with
  | nil => simp [build,unbuild,GatePhysical]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    simp only [build,unbuild,gatePhysical_append]
    exact ⟨⟨op_physical _ _ _ _ _ _ _ (hf f (by simp)),t.1⟩,⟨t.2,op_physical _ _ _ _ _ _ _ (hf f (by simp))⟩⟩

theorem build_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    Challenge.gateSlots (build acc Z bank cin w fs)≤fs.length*(14*w) ∧
      Challenge.gateSlots (unbuild acc Z bank cin w fs)≤fs.length*(14*w) := by
  induction fs with
  | nil => simp [build,unbuild,Challenge.gateSlots]
  | cons f fs ih =>
    have t := ih (fun g hg => hf g (by simp [hg]))
    have L := fits_lengths acc Z bank cin w f hacc (hf f (by simp))
    have a := op_gateSlots acc Z bank cin w f.negative f
    have b := op_gateSlots acc Z bank cin w (!f.negative) f
    rw [L.1,L.2.2] at a b
    simp only [build,unbuild,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    constructor <;> omega

/-! Seeded accumulation: when the first term is positive it is added into a
zero accumulator, so the shifted window can be filled by a plain CX copy
(no Toffoli); the matching last step of the clear is the same copy. -/

def seedOp (acc Z : List Wire) (w : Nat) (f : MeasuredSquareFold) : Program :=
  copyRegister none (tx Z w f) (ty acc f)

def baseBuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => (if f.negative then op acc Z bank cin w true f else seedOp acc Z w f)++
      build acc Z bank cin w fs

def baseUnbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | [] => []
  | f::fs => unbuild acc Z bank cin w fs++
      (if f.negative then op acc Z bank cin w false f else seedOp acc Z w f)

def baseBuildT (w : Nat) : List MeasuredSquareFold → Nat
  | [] => 0
  | f::fs => (if f.negative then w-f.shift-1 else 0)+buildT w fs

theorem seed_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) (base : BasisState)
    (hz : ∀q∈Z,base q=false) (V W : Nat)
    (hVW : (V=0 ∧ W=regValue f.src base*2^f.shift) ∨ (V=regValue f.src base*2^f.shift ∧ W=0)) :
    Triple (SquareFrame acc base V) (seedOp acc Z w f) (SquareFrame acc base W) := by
  intro s m hs
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have nd := fits_nodup acc Z bank cin w f hf
  have xy : (tx Z w f++ty acc f).Nodup :=
    (List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    have b := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append] at h b
    split at h <;> omega
  have xv : regValue (tx Z w f) s.basis=regValue f.src base := by
    have zero : regValue (Z.take (w-f.shift-f.src.length)) s.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have hq' := List.mem_of_mem_take hq
      exact (hs.2 q (away q (by simp [hq']))).trans (hz q hq')
    have src : regValue f.src s.basis=regValue f.src base :=
      regValue_congr _ _ _ (fun q hq => hs.2 q (away q (by simp [hq])))
    simp only [tx,regValue_append,zero,src,Nat.mul_zero,Nat.add_zero]
  have accNd : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop accNd (show f.shift≤f.shift by omega)
  have shiftLe : f.shift≤acc.length := by have := hf.len; omega
  have split (t : BasisState) : regValue acc t=regValue (acc.take f.shift) t+2^f.shift*regValue (ty acc f) t := by
    have h := regValue_append (acc.take f.shift) (acc.drop f.shift) t
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left shiftLe] at h
    exact h
  have lowLt : regValue (acc.take f.shift) s.basis<2^f.shift := by
    have h := regValue_lt (acc.take f.shift) s.basis
    rwa [List.length_take,Nat.min_eq_left shiftLe] at h
  have pos : 0<2^f.shift := Nat.two_pow_pos _
  have vs := split s.basis
  rw [hs.1] at vs
  have vmod : V%2^f.shift=0 := by
    rcases hVW with ⟨rfl,_⟩|⟨rfl,_⟩
    · simp
    · exact Nat.mul_mod_left _ _
  have low0 : regValue (acc.take f.shift) s.basis=0 := by
    have h := congrArg (· % 2^f.shift) vs
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowLt] at h
    omega
  have yv : regValue (ty acc f) s.basis*2^f.shift=V := by
    rw [low0,Nat.zero_add] at vs; rw [vs, Nat.mul_comm]
  have cp := copyRegister_correct none (tx Z w f) (ty acc f) L.1 xy (by simp) s m
  simp only [copyValue] at cp
  let r := run (seedOp acc Z w f) m s
  have lowSame : regValue (acc.take f.shift) r.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => cp.2.1 q (fun hy => List.disjoint_left.mp dis hq hy))).trans low0
  refine ⟨cp.1,?_,?_⟩
  · change regValue acc r.basis=W
    rw [split r.basis,lowSame,Nat.zero_add]
    change 2^f.shift*regValue (ty acc f) (run (copyRegister none (tx Z w f) (ty acc f)) m s).basis=W
    rw [cp.2.2,xv]
    rcases hVW with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have y0 : regValue (ty acc f) s.basis=0 := by
        have := yv; rw [Nat.mul_eq_zero] at this
        rcases this with h|h
        · exact h
        · omega
      rw [y0,Nat.zero_xor,Nat.mul_comm]
    · have yT : regValue (ty acc f) s.basis=regValue f.src base :=
        Nat.eq_of_mul_eq_mul_right pos yv
      rw [yT,Nat.xor_self,Nat.mul_zero]
  · intro q hq
    have hy : q∉ty acc f := fun h => hq (List.mem_of_mem_drop h)
    exact (cp.2.1 q hy).trans (hs.2 q hq)

theorem baseBuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base 0) (baseBuild acc Z bank cin w fs)
      (SquareFrame acc base (accVal base 0 fs)) := by
  cases fs with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons f fs =>
    have hf1 := hf f (by simp)
    have rest := build_triple acc Z bank cin w hacc base hz hb hi fs
      (fun g hg => hf g (by simp [hg])) _ hv.2
    have first : Triple (SquareFrame acc base 0)
        (if f.negative then op acc Z bank cin w true f else seedOp acc Z w f)
        (SquareFrame acc base (step base f.negative 0 f)) := by
      have h1 := hv.1
      cases hn : f.negative
      · simp only [Bool.false_eq_true,if_false]
        apply seed_triple acc Z bank cin w f hacc hf1 base hz
        left; simp [step]
      · simp only [if_true]
        simp only [hn,if_true] at h1
        exact op_triple acc Z bank cin w f hacc hf1 base hz hb hi true 0 (by simpa using h1)
    exact first.seq rest

theorem baseUnbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base (accVal base 0 fs)) (baseUnbuild acc Z bank cin w fs)
      (SquareFrame acc base 0) := by
  cases fs with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons f fs =>
    have hf1 := hf f (by simp)
    have V1 := step_valid_lt base w 0 f (Nat.two_pow_pos w) hv.1
    have rest := unbuild_triple acc Z bank cin w hacc base hz hb hi fs
      (fun g hg => hf g (by simp [hg])) _ V1 hv.2
    have last : Triple (SquareFrame acc base (step base f.negative 0 f))
        (if f.negative then op acc Z bank cin w false f else seedOp acc Z w f)
        (SquareFrame acc base 0) := by
      have h1 := hv.1
      have pw := Nat.two_pow_pos w
      cases hn : f.negative
      · simp only [Bool.false_eq_true,if_false]
        apply seed_triple acc Z bank cin w f hacc hf1 base hz
        right; simp [step]
      · simp only [if_true]
        simp only [hn,if_true] at h1
        have h2 := op_triple acc Z bank cin w f hacc hf1 base hz hb hi false (step base true 0 f)
          (by simp only [step,if_true,Bool.false_eq_true,if_false]; omega)
        have back : step base false (step base true 0 f) f=0 := by
          simp only [step,if_true,Bool.false_eq_true,if_false]; omega
        rw [back] at h2; exact h2
    exact rest.seq last

theorem seed_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : FitsLen Z bank w f) :
    toffoliCount (seedOp acc Z w f)=0 ∧ measurementCount (seedOp acc Z w f)=0 := by
  have L := fits_lengths acc Z bank cin w f hacc hf
  have c := copyRegister_counts none (tx Z w f) (ty acc f) L.1
  simpa [seedOp] using c

theorem baseBuild_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    (toffoliCount (baseBuild acc Z bank cin w fs)=baseBuildT w fs ∧
      measurementCount (baseBuild acc Z bank cin w fs)=baseBuildT w fs) ∧
    (toffoliCount (baseUnbuild acc Z bank cin w fs)=baseBuildT w fs ∧
      measurementCount (baseUnbuild acc Z bank cin w fs)=baseBuildT w fs) := by
  cases fs with
  | nil => simp [baseBuild,baseUnbuild,baseBuildT,toffoliCount,measurementCount]
  | cons f fs =>
    have t := build_counts acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg]))
    have c := seed_counts acc Z bank cin w f hacc (hf f (by simp))
    have a := op_counts acc Z bank cin w true f hacc (hf f (by simp))
    have b := op_counts acc Z bank cin w false f hacc (hf f (by simp))
    cases hn : f.negative <;>
      simp only [baseBuild,baseUnbuild,baseBuildT,hn,if_true,Bool.false_eq_true,if_false,
        toffoliCount_append,measurementCount_append] <;> omega

theorem seed_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (f : MeasuredSquareFold)
    (hacc : acc.length=w) (hf : Fits acc Z bank cin w f) :
    wires (seedOp acc Z w f)⊆(cin::(f.src++acc++Z++bank)).toFinset := by
  have L := fits_lengths acc Z bank cin w f hacc hf.toFitsLen
  have h := op_support acc Z bank cin w false f hacc hf
  rw [op_wires acc Z bank cin w false f hacc hf] at h
  refine Finset.Subset.trans ?_ h
  rw [seedOp,copyRegister_wires none _ _ L.1]
  split
  · exact Finset.empty_subset _
  · intro q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,Option.toList_none,List.nil_append] at hq ⊢
    tauto

theorem baseBuild_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (S : Finset Wire)
    (hS : ∀f∈fs,(cin::(f.src++acc++Z++bank)).toFinset⊆S) :
    wires (baseBuild acc Z bank cin w fs)⊆S ∧ wires (baseUnbuild acc Z bank cin w fs)⊆S := by
  cases fs with
  | nil => simp [baseBuild,baseUnbuild,wires]
  | cons f fs =>
    have t := build_support acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg])) S
      (fun g hg => hS g (by simp [hg]))
    have hf1 := hf f (by simp)
    have hS1 := hS f (by simp)
    have first (neg : Bool) : wires (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f)⊆S := by
      split
      · exact (op_support acc Z bank cin w neg f hacc hf1).trans hS1
      · exact (seed_support acc Z bank cin w f hacc hf1).trans hS1
    simp only [baseBuild,baseUnbuild,wires_append,Finset.union_subset_iff]
    exact ⟨⟨first true,t.1⟩,⟨t.2,first false⟩⟩

theorem baseBuild_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    GatePhysical (baseBuild acc Z bank cin w fs) ∧ GatePhysical (baseUnbuild acc Z bank cin w fs) := by
  cases fs with
  | nil => simp [baseBuild,baseUnbuild,GatePhysical]
  | cons f fs =>
    have t := build_physical acc Z bank cin w fs (fun g hg => hf g (by simp [hg]))
    have hf1 := hf f (by simp)
    have first (neg : Bool) : GatePhysical (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f) := by
      split
      · exact op_physical _ _ _ _ _ _ _ hf1
      · have L := fits_lengths acc Z bank cin w f hacc hf1.toFitsLen
        have nd := fits_nodup acc Z bank cin w f hf1
        exact copyRegister_physical none _ _
          ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
    simp only [baseBuild,baseUnbuild,gatePhysical_append]
    exact ⟨⟨first true,t.1⟩,⟨t.2,first false⟩⟩

theorem baseBuild_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    Challenge.gateSlots (baseBuild acc Z bank cin w fs)≤fs.length*(14*w) ∧
      Challenge.gateSlots (baseUnbuild acc Z bank cin w fs)≤fs.length*(14*w) := by
  cases fs with
  | nil => simp [baseBuild,baseUnbuild,Challenge.gateSlots]
  | cons f fs =>
    have t := build_gateSlots acc Z bank cin w hacc fs (fun g hg => hf g (by simp [hg]))
    have L := fits_lengths acc Z bank cin w f hacc (hf f (by simp))
    have first (neg : Bool) :
        Challenge.gateSlots (if f.negative then op acc Z bank cin w neg f else seedOp acc Z w f)≤14*w := by
      split
      · have a := op_gateSlots acc Z bank cin w neg f
        rw [L.1,L.2.2] at a; omega
      · have c : Challenge.gateSlots (seedOp acc Z w f)≤(tx Z w f).length := by
          simp [seedOp,Baselines.copyRegister_gateSlots]
        rw [L.1,L.2.2] at c; omega
    have f1 := first true
    have f2 := first false
    simp only [baseBuild,baseUnbuild,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    constructor <;> omega

theorem fits_prefix (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hn : n≤w) (hf : Fits acc Z bank cin w f)
    (hlen : f.src.length+f.shift<n) : Fits (acc.take n) Z bank cin n f := by
  refine ⟨⟨hlen,?_,?_⟩,?_⟩
  · have h := hf.zpad
    omega
  · have h := hf.bankLen
    omega
  · apply List.nodup_iff_count_le_one.mpr
    intro q
    have h := List.nodup_iff_count_le_one.mp hf.nd q
    have take := (List.take_sublist n acc).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega

/-- Run a short operation inside a full accumulator frame. The high bits
stay zero; the original frame base may have arbitrary accumulator bits. -/
theorem op_prefix_triple (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hacc : acc.length=w) (hn : n≤w)
    (hf : Fits acc Z bank cin w f) (hlen : f.src.length+f.shift<n)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) (neg : Bool) (V : Nat) (hV : V<2^n)
    (hok : if neg then regValue f.src base*2^f.shift≤V
      else V+regValue f.src base*2^f.shift<2^n) :
    Triple (SquareFrame acc base V) (op (acc.take n) Z bank cin n neg f)
      (SquareFrame acc base (step base neg V f)) := by
  intro s m hs
  have hnd := List.nodup_iff_count_le_one.mp hf.nd
  have away (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h := hnd q
    have a := List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b := List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (q : Wire) (hq : q∈f.src++Z++bank ∨ q=cin) : s.basis q=base q :=
    hs.2 q (away q hq)
  have source : regValue f.src s.basis=regValue f.src base :=
    regValue_congr _ _ _ (fun q hq => same q (Or.inl (by simp [hq])))
  have pref := regValue_take_drop_of_lt acc n V s.basis (by omega) hs.1 hV
  have len : (acc.take n).length=n := by simp [List.length_take,hacc,Nat.min_eq_left hn]
  have small := op_triple (acc.take n) Z bank cin n f len
    (fits_prefix acc Z bank cin w n f hn hf hlen) s.basis
    (fun q hq => (same q (Or.inl (by simp [hq]))).trans (hz q hq))
    (fun q hq => (same q (Or.inl (by simp [hq]))).trans (hb q hq))
    ((same cin (Or.inr rfl)).trans hi) neg V (by simpa only [source] using hok)
    s m ⟨pref.1,fun _ _ => rfl⟩
  have value : step s.basis neg V f=step base neg V f := by simp only [step,source]
  rw [value] at small
  have ndacc : acc.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h := hnd q
    simp only [List.count_cons,List.count_append] at h
    split at h <;> omega
  have dis := List.disjoint_take_drop ndacc (show n≤n by omega)
  have high : regValue (acc.drop n)
      (run (op (acc.take n) Z bank cin n neg f) m s).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) pref.2
    intro q hq
    exact small.2.2 q (fun low => List.disjoint_left.mp dis low hq)
  refine ⟨small.1,?_,?_⟩
  · have split := regValue_append (acc.take n) (acc.drop n)
      (run (op (acc.take n) Z bank cin n neg f) m s).basis
    rw [List.take_append_drop,small.2.1,high,Nat.mul_zero,Nat.add_zero] at split
    exact split
  · intro q hq
    exact (small.2.2 q (fun h => hq (List.mem_of_mem_take h))).trans (hs.2 q hq)

theorem op_prefix_counts (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hacc : acc.length=w) (hn : n≤w)
    (hf : Fits acc Z bank cin w f) (hlen : f.src.length+f.shift<n) (neg : Bool) :
    toffoliCount (op (acc.take n) Z bank cin n neg f)=n-f.shift-1 ∧
    measurementCount (op (acc.take n) Z bank cin n neg f)=n-f.shift-1 := by
  exact op_counts (acc.take n) Z bank cin n neg f
    (by simp [List.length_take,hacc,Nat.min_eq_left hn])
    (fits_prefix acc Z bank cin w n f hn hf hlen).toFitsLen

theorem op_prefix_support (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hacc : acc.length=w) (hn : n≤w)
    (hf : Fits acc Z bank cin w f) (hlen : f.src.length+f.shift<n) (neg : Bool) :
    wires (op (acc.take n) Z bank cin n neg f)⊆
      (cin::(f.src++acc++Z++bank)).toFinset := by
  have old := op_support (acc.take n) Z bank cin n neg f
    (by simp [List.length_take,hacc,Nat.min_eq_left hn])
    (fits_prefix acc Z bank cin w n f hn hf hlen)
  intro q hq
  have h := old hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  have take : q∈acc.take n → q∈acc := List.mem_of_mem_take
  tauto

theorem op_prefix_physical (acc Z bank : List Wire) (cin : Wire) (w n : Nat)
    (f : MeasuredSquareFold) (hn : n≤w) (hf : Fits acc Z bank cin w f)
    (hlen : f.src.length+f.shift<n) (neg : Bool) :
    GatePhysical (op (acc.take n) Z bank cin n neg f) :=
  op_physical _ _ _ _ _ _ _ (fits_prefix acc Z bank cin w n f hn hf hlen)

def earlyTerm (src : List Wire) (negative : Bool) (shift : Nat) : MeasuredSquareFold :=
  ⟨negative,true,src,shift⟩

@[simp] theorem earlyTerm_src (src : List Wire) (negative : Bool) (shift : Nat) :
    (earlyTerm src negative shift).src=src := rfl
@[simp] theorem earlyTerm_negative (src : List Wire) (negative : Bool) (shift : Nat) :
    (earlyTerm src negative shift).negative=negative := rfl

def earlyPrefix (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  seedOp acc Z 163 (earlyTerm src false 4)++
    op (acc.take 141) Z bank cin 141 false (earlyTerm src false 10)++
    op (acc.take 141) Z bank cin 141 true (earlyTerm src true 6)

def earlyPrefixClear (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  op (acc.take 141) Z bank cin 141 false (earlyTerm src true 6)++
    op (acc.take 141) Z bank cin 141 true (earlyTerm src false 10)++
    seedOp acc Z 163 (earlyTerm src false 4)

theorem earlyPrefix_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Fits acc Z bank cin 163 (earlyTerm src false 4))
    (hf10 : Fits acc Z bank cin 163 (earlyTerm src false 10))
    (hf6 : Fits acc Z bank cin 163 (earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base 0) (earlyPrefix acc Z bank cin src)
      (SquareFrame acc base (976*regValue src base)) := by
  let H := regValue src base
  have hH : H<2^130 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have seed := seed_triple acc Z bank cin 163 (earlyTerm src false 4) hacc hf4 base hz
    0 (16*H) (Or.inl (by simp [earlyTerm,H,Nat.mul_comm]))
  have add : Triple (SquareFrame acc base (16*H))
      (op (acc.take 141) Z bank cin 141 false (earlyTerm src false 10))
      (SquareFrame acc base (1040*H)) := by
    have h := op_prefix_triple acc Z bank cin 163 141 (earlyTerm src false 10) hacc
      (by decide) hf10 (by simp only [earlyTerm]; omega) base hz hb hi false (16*H)
      (by norm_num at hH ⊢;omega) (by norm_num [earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : step base false (16*H) (earlyTerm src false 10)=1040*H := by
      norm_num [step,earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H))
      (op (acc.take 141) Z bank cin 141 true (earlyTerm src true 6))
      (SquareFrame acc base (976*H)) := by
    have h := op_prefix_triple acc Z bank cin 163 141 (earlyTerm src true 6) hacc
      (by decide) hf6 (by simp only [earlyTerm]; omega) base hz hb hi true (1040*H)
      (by norm_num at hH ⊢;omega) (by norm_num [earlyTerm];dsimp [H];omega)
    have value : step base true (1040*H) (earlyTerm src true 6)=976*H := by
      norm_num [step,earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  exact (seed.seq add).seq sub

theorem earlyPrefixClear_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Fits acc Z bank cin 163 (earlyTerm src false 4))
    (hf10 : Fits acc Z bank cin 163 (earlyTerm src false 10))
    (hf6 : Fits acc Z bank cin 163 (earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (earlyPrefixClear acc Z bank cin src)
      (SquareFrame acc base 0) := by
  let H := regValue src base
  have hH : H<2^130 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have add : Triple (SquareFrame acc base (976*H))
      (op (acc.take 141) Z bank cin 141 false (earlyTerm src true 6))
      (SquareFrame acc base (1040*H)) := by
    have h := op_prefix_triple acc Z bank cin 163 141 (earlyTerm src true 6) hacc
      (by decide) hf6 (by simp only [earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : step base false (976*H) (earlyTerm src true 6)=1040*H := by
      norm_num [step,earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H))
      (op (acc.take 141) Z bank cin 141 true (earlyTerm src false 10))
      (SquareFrame acc base (16*H)) := by
    have h := op_prefix_triple acc Z bank cin 163 141 (earlyTerm src false 10) hacc
      (by decide) hf10 (by simp only [earlyTerm]; omega) base hz hb hi true (1040*H)
      (by norm_num at hH ⊢;omega) (by norm_num [earlyTerm];dsimp [H];omega)
    have value : step base true (1040*H) (earlyTerm src false 10)=16*H := by
      norm_num [step,earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have seed := seed_triple acc Z bank cin 163 (earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [earlyTerm,H,Nat.mul_comm]))
  exact (add.seq sub).seq seed

theorem earlyPrefix_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Fits acc Z bank cin 163 (earlyTerm src false 4))
    (hf10 : Fits acc Z bank cin 163 (earlyTerm src false 10))
    (hf6 : Fits acc Z bank cin 163 (earlyTerm src true 6)) :
    (toffoliCount (earlyPrefix acc Z bank cin src)=264 ∧
      measurementCount (earlyPrefix acc Z bank cin src)=264) ∧
    (toffoliCount (earlyPrefixClear acc Z bank cin src)=264 ∧
      measurementCount (earlyPrefixClear acc Z bank cin src)=264) := by
  have seed := seed_counts acc Z bank cin 163 (earlyTerm src false 4) hacc hf4.toFitsLen
  have add := op_prefix_counts acc Z bank cin 163 141 (earlyTerm src false 10) hacc
    (by decide) hf10 (by simp only [earlyTerm]; omega) false
  have sub := op_prefix_counts acc Z bank cin 163 141 (earlyTerm src true 6) hacc
    (by decide) hf6 (by simp only [earlyTerm]; omega) true
  have addClear := op_prefix_counts acc Z bank cin 163 141 (earlyTerm src true 6) hacc
    (by decide) hf6 (by simp only [earlyTerm]; omega) false
  have subClear := op_prefix_counts acc Z bank cin 163 141 (earlyTerm src false 10) hacc
    (by decide) hf10 (by simp only [earlyTerm]; omega) true
  simp only [earlyPrefix,earlyPrefixClear,toffoliCount_append,measurementCount_append,
    seed.1,seed.2,add.1,add.2,sub.1,sub.2,addClear.1,addClear.2,subClear.1,subClear.2]
  norm_num [earlyTerm]

theorem earlyPrefix_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Fits acc Z bank cin 163 (earlyTerm src false 4))
    (hf10 : Fits acc Z bank cin 163 (earlyTerm src false 10))
    (hf6 : Fits acc Z bank cin 163 (earlyTerm src true 6)) :
    wires (earlyPrefix acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset ∧
    wires (earlyPrefixClear acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset := by
  have seed := seed_support acc Z bank cin 163 (earlyTerm src false 4) hacc hf4
  have add := op_prefix_support acc Z bank cin 163 141 (earlyTerm src false 10) hacc
    (by decide) hf10 (by simp only [earlyTerm]; omega) false
  have sub := op_prefix_support acc Z bank cin 163 141 (earlyTerm src true 6) hacc
    (by decide) hf6 (by simp only [earlyTerm]; omega) true
  have addClear := op_prefix_support acc Z bank cin 163 141 (earlyTerm src true 6) hacc
    (by decide) hf6 (by simp only [earlyTerm]; omega) false
  have subClear := op_prefix_support acc Z bank cin 163 141 (earlyTerm src false 10) hacc
    (by decide) hf10 (by simp only [earlyTerm]; omega) true
  simp only [earlyTerm] at seed add sub addClear subClear
  simp only [earlyPrefix,earlyPrefixClear,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨seed,add⟩,sub⟩,⟨⟨addClear,subClear⟩,seed⟩⟩

theorem earlyPrefix_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : Fits acc Z bank cin 163 (earlyTerm src false 4))
    (hf10 : Fits acc Z bank cin 163 (earlyTerm src false 10))
    (hf6 : Fits acc Z bank cin 163 (earlyTerm src true 6)) :
    GatePhysical (earlyPrefix acc Z bank cin src) ∧
    GatePhysical (earlyPrefixClear acc Z bank cin src) := by
  have seed : GatePhysical (seedOp acc Z 163 (earlyTerm src false 4)) := by
    have len := fits_lengths acc Z bank cin 163 (earlyTerm src false 4) hacc hf4.toFitsLen
    have nd := fits_nodup acc Z bank cin 163 (earlyTerm src false 4) hf4
    exact copyRegister_physical none _ _
      ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
  have add := op_prefix_physical acc Z bank cin 163 141 (earlyTerm src false 10)
    (by decide) hf10 (by simp only [earlyTerm]; omega) false
  have sub := op_prefix_physical acc Z bank cin 163 141 (earlyTerm src true 6)
    (by decide) hf6 (by simp only [earlyTerm]; omega) true
  have addClear := op_prefix_physical acc Z bank cin 163 141 (earlyTerm src true 6)
    (by decide) hf6 (by simp only [earlyTerm]; omega) false
  have subClear := op_prefix_physical acc Z bank cin 163 141 (earlyTerm src false 10)
    (by decide) hf10 (by simp only [earlyTerm]; omega) true
  simp only [earlyPrefix,earlyPrefixClear,gatePhysical_append]
  exact ⟨⟨⟨seed,add⟩,sub⟩,⟨⟨addClear,subClear⟩,seed⟩⟩



/-- Select only the three common early H terms. Other accumulators keep
exactly the seeded implementation above. -/
def EarlyH (w : Nat) : List MeasuredSquareFold → Prop
  | a::b::c::_ => w=163 ∧ a.src.length≤130 ∧ b.src=a.src ∧ c.src=a.src ∧
      a.shift=4 ∧ b.shift=10 ∧ c.shift=6 ∧
      a.negative=false ∧ b.negative=false ∧ c.negative=true ∧
      a.canonical=true ∧ b.canonical=true ∧ c.canonical=true
  | _ => False

instance (w : Nat) (fs : List MeasuredSquareFold) : Decidable (EarlyH w fs) := by
  cases fs with
  | nil => unfold EarlyH; infer_instance
  | cons a fs =>
    cases fs with
    | nil => unfold EarlyH; infer_instance
    | cons b fs =>
      cases fs with
      | nil => unfold EarlyH; infer_instance
      | cons c fs => unfold EarlyH; infer_instance

theorem earlyH_info (w : Nat) (fs : List MeasuredSquareFold) (h : EarlyH w fs) :
    ∃ src tail,w=163 ∧ src.length≤130 ∧
      fs=earlyTerm src false 4::earlyTerm src false 10::earlyTerm src true 6::tail := by
  cases fs with
  | nil => exact False.elim h
  | cons a fs =>
    cases fs with
    | nil => exact False.elim h
    | cons b fs =>
      cases fs with
      | nil => exact False.elim h
      | cons c tail =>
        rcases a with ⟨an,ac,asrc,aj⟩
        rcases b with ⟨bn,bc,bsrc,bj⟩
        rcases c with ⟨cn,cc,csrc,cj⟩
        simp only [EarlyH] at h
        rcases h with ⟨hw,hlen,hb,hc,haj,hbj,hcj,han,hbn,hcn,hac,hbc,hcc⟩
        subst_vars
        exact ⟨_,tail,rfl,hlen,rfl⟩

def earlyBuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | a::_::_::tail => earlyPrefix acc Z bank cin a.src++build acc Z bank cin w tail
  | _ => []
def earlyUnbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) : List MeasuredSquareFold → Program
  | a::_::_::tail => unbuild acc Z bank cin w tail++earlyPrefixClear acc Z bank cin a.src
  | _ => []
def earlyBuildT (w : Nat) : List MeasuredSquareFold → Nat
  | _::_::_::tail => 264+buildT w tail
  | _ => 0

def sbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) (fs : List MeasuredSquareFold) : Program :=
  if EarlyH w fs then earlyBuild acc Z bank cin w fs else baseBuild acc Z bank cin w fs
def sunbuild (acc Z bank : List Wire) (cin : Wire) (w : Nat) (fs : List MeasuredSquareFold) : Program :=
  if EarlyH w fs then earlyUnbuild acc Z bank cin w fs else baseUnbuild acc Z bank cin w fs
def sbuildT (w : Nat) (fs : List MeasuredSquareFold) : Nat :=
  if EarlyH w fs then earlyBuildT w fs else baseBuildT w fs

theorem early_steps (base : BasisState) (src : List Wire) :
    step base true (step base false (step base false 0 (earlyTerm src false 4))
      (earlyTerm src false 10)) (earlyTerm src true 6)=976*regValue src base := by
  norm_num [step,earlyTerm]
  omega

theorem sbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base 0) (sbuild acc Z bank cin w fs)
      (SquareFrame acc base (accVal base 0 fs)) := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have hf4 := hf (earlyTerm src false 4) (by simp)
    have hf10 := hf (earlyTerm src false 10) (by simp)
    have hf6 := hf (earlyTerm src true 6) (by simp)
    have vt := hv.2.2.2
    change Valid base 163
      (step base true (step base false (step base false 0 (earlyTerm src false 4))
        (earlyTerm src false 10)) (earlyTerm src true 6)) tail at vt
    rw [early_steps] at vt
    have head := earlyPrefix_triple acc Z bank cin src hacc hlen hf4 hf10 hf6 base hz hb hi
    have rest := build_triple acc Z bank cin 163 hacc base hz hb hi tail
      (fun f hf' => hf f (by simp [hf'])) (976*regValue src base) vt
    rw [sbuild,if_pos h,earlyBuild]
    simpa only [accVal,earlyTerm_src,earlyTerm_negative,early_steps] using head.seq rest
  · simpa only [sbuild,if_neg h] using baseBuild_triple acc Z bank cin w hacc base hz hb hi fs hf hv

theorem sunbuild_triple (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false) (hi : base cin=false)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (hv : Valid base w 0 fs) :
    Triple (SquareFrame acc base (accVal base 0 fs)) (sunbuild acc Z bank cin w fs)
      (SquareFrame acc base 0) := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have hf4 := hf (earlyTerm src false 4) (by simp)
    have hf10 := hf (earlyTerm src false 10) (by simp)
    have hf6 := hf (earlyTerm src true 6) (by simp)
    have vt := hv.2.2.2
    change Valid base 163
      (step base true (step base false (step base false 0 (earlyTerm src false 4))
        (earlyTerm src false 10)) (earlyTerm src true 6)) tail at vt
    rw [early_steps] at vt
    have hH : regValue src base<2^130 :=
      lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hlen)
    have bound : 976*regValue src base<2^163 := by norm_num at hH ⊢;omega
    have rest := unbuild_triple acc Z bank cin 163 hacc base hz hb hi tail
      (fun f hf' => hf f (by simp [hf'])) (976*regValue src base) bound vt
    have head := earlyPrefixClear_triple acc Z bank cin src hacc hlen hf4 hf10 hf6 base hz hb hi
    rw [sunbuild,if_pos h,earlyUnbuild]
    simpa only [accVal,earlyTerm_src,earlyTerm_negative,early_steps] using rest.seq head
  · simpa only [sunbuild,if_neg h] using baseUnbuild_triple acc Z bank cin w hacc base hz hb hi fs hf hv


theorem earlyPrefix_counts_len (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : FitsLen Z bank 163 (earlyTerm src false 4))
    (hf10 : FitsLen Z bank 163 (earlyTerm src false 10))
    (hf6 : FitsLen Z bank 163 (earlyTerm src true 6)) :
    (toffoliCount (earlyPrefix acc Z bank cin src)=264 ∧
      measurementCount (earlyPrefix acc Z bank cin src)=264) ∧
    (toffoliCount (earlyPrefixClear acc Z bank cin src)=264 ∧
      measurementCount (earlyPrefixClear acc Z bank cin src)=264) := by
  have narrow (f : MeasuredSquareFold) (hf : FitsLen Z bank 163 f)
      (hl : f.src.length+f.shift<141) : FitsLen Z bank 141 f := by
    refine ⟨hl,?_,?_⟩
    · have h := hf.zpad; omega
    · have h := hf.bankLen; omega
  have len : (acc.take 141).length=141 := by simp [List.length_take,hacc]
  have seed := seed_counts acc Z bank cin 163 (earlyTerm src false 4) hacc hf4
  have a (neg : Bool) := op_counts (acc.take 141) Z bank cin 141 neg (earlyTerm src false 10) len
    (narrow _ hf10 (by simp only [earlyTerm]; omega))
  have b (neg : Bool) := op_counts (acc.take 141) Z bank cin 141 neg (earlyTerm src true 6) len
    (narrow _ hf6 (by simp only [earlyTerm]; omega))
  simp only [earlyPrefix,earlyPrefixClear,toffoliCount_append,measurementCount_append,
    seed.1,seed.2,(a false).1,(a false).2,(b true).1,(b true).2,
    (b false).1,(b false).2,(a true).1,(a true).2]
  norm_num [earlyTerm]

theorem sbuild_counts (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    (toffoliCount (sbuild acc Z bank cin w fs)=sbuildT w fs ∧
      measurementCount (sbuild acc Z bank cin w fs)=sbuildT w fs) ∧
    (toffoliCount (sunbuild acc Z bank cin w fs)=sbuildT w fs ∧
      measurementCount (sunbuild acc Z bank cin w fs)=sbuildT w fs) := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have head := earlyPrefix_counts_len acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have rest := build_counts acc Z bank cin 163 hacc tail (fun f hf' => hf f (by simp [hf']))
    simp only [sbuild,sunbuild,sbuildT,if_pos h,earlyBuild,earlyUnbuild,earlyBuildT,earlyTerm_src,
      toffoliCount_append,measurementCount_append]
    rcases head with ⟨⟨ht,hm⟩,⟨hct,hcm⟩⟩
    rcases rest with ⟨⟨rt,rm⟩,⟨rct,rcm⟩⟩
    omega
  · simpa only [sbuild,sunbuild,sbuildT,if_neg h] using baseBuild_counts acc Z bank cin w hacc fs hf

theorem sbuild_support (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) (S : Finset Wire)
    (hS : ∀f∈fs,(cin::(f.src++acc++Z++bank)).toFinset⊆S) :
    wires (sbuild acc Z bank cin w fs)⊆S ∧ wires (sunbuild acc Z bank cin w fs)⊆S := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have head := earlyPrefix_support acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have place : (cin::(src++acc++Z++bank)).toFinset⊆S :=
      hS (earlyTerm src false 4) (by simp)
    have rest := build_support acc Z bank cin 163 hacc tail
      (fun f hf' => hf f (by simp [hf'])) S (fun f hf' => hS f (by simp [hf']))
    simp only [sbuild,sunbuild,if_pos h,earlyBuild,earlyUnbuild,earlyTerm_src,wires_append,Finset.union_subset_iff]
    exact ⟨⟨head.1.trans place,rest.1⟩,⟨rest.2,head.2.trans place⟩⟩
  · simpa only [sbuild,sunbuild,if_neg h] using baseBuild_support acc Z bank cin w hacc fs hf S hS

theorem sbuild_physical (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,Fits acc Z bank cin w f) :
    GatePhysical (sbuild acc Z bank cin w fs) ∧ GatePhysical (sunbuild acc Z bank cin w fs) := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have head := earlyPrefix_physical acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have rest := build_physical acc Z bank cin 163 tail (fun f hf' => hf f (by simp [hf']))
    simp only [sbuild,sunbuild,if_pos h,earlyBuild,earlyUnbuild,earlyTerm_src,gatePhysical_append]
    exact ⟨⟨head.1,rest.1⟩,⟨rest.2,head.2⟩⟩
  · simpa only [sbuild,sunbuild,if_neg h] using baseBuild_physical acc Z bank cin w hacc fs hf

theorem earlyPrefix_gateSlots (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=163) (hsrc : src.length≤130)
    (hf4 : FitsLen Z bank 163 (earlyTerm src false 4))
    (hf10 : FitsLen Z bank 163 (earlyTerm src false 10))
    (hf6 : FitsLen Z bank 163 (earlyTerm src true 6)) :
    Challenge.gateSlots (earlyPrefix acc Z bank cin src)≤3*(14*163) ∧
    Challenge.gateSlots (earlyPrefixClear acc Z bank cin src)≤3*(14*163) := by
  have narrow (f : MeasuredSquareFold) (hf : FitsLen Z bank 163 f)
      (hl : f.src.length+f.shift<141) : FitsLen Z bank 141 f := by
    refine ⟨hl,?_,?_⟩
    · have h := hf.zpad; omega
    · have h := hf.bankLen; omega
  have len : (acc.take 141).length=141 := by simp [List.length_take,hacc]
  have seed : Challenge.gateSlots (seedOp acc Z 163 (earlyTerm src false 4))≤163 := by
    have l := fits_lengths acc Z bank cin 163 (earlyTerm src false 4) hacc hf4
    have h : Challenge.gateSlots (seedOp acc Z 163 (earlyTerm src false 4))≤
        (tx Z 163 (earlyTerm src false 4)).length := by simp [seedOp,Baselines.copyRegister_gateSlots]
    rw [l.1,l.2.2] at h
    exact h.trans (by omega)
  have a (neg : Bool) : Challenge.gateSlots
      (op (acc.take 141) Z bank cin 141 neg (earlyTerm src false 10))≤14*141 := by
    have h := op_gateSlots (acc.take 141) Z bank cin 141 neg (earlyTerm src false 10)
    have l := fits_lengths (acc.take 141) Z bank cin 141 (earlyTerm src false 10) len
      (narrow _ hf10 (by simp only [earlyTerm]; omega))
    rw [l.1,l.2.2] at h
    exact h.trans (by omega)
  have b (neg : Bool) : Challenge.gateSlots
      (op (acc.take 141) Z bank cin 141 neg (earlyTerm src true 6))≤14*141 := by
    have h := op_gateSlots (acc.take 141) Z bank cin 141 neg (earlyTerm src true 6)
    have l := fits_lengths (acc.take 141) Z bank cin 141 (earlyTerm src true 6) len
      (narrow _ hf6 (by simp only [earlyTerm]; omega))
    rw [l.1,l.2.2] at h
    exact h.trans (by omega)
  have a0 := a false; have a1 := a true; have b0 := b false; have b1 := b true
  simp only [earlyPrefix,earlyPrefixClear,Challenge.gateSlots_append]
  omega

theorem sbuild_gateSlots (acc Z bank : List Wire) (cin : Wire) (w : Nat) (hacc : acc.length=w)
    (fs : List MeasuredSquareFold) (hf : ∀f∈fs,FitsLen Z bank w f) :
    Challenge.gateSlots (sbuild acc Z bank cin w fs)≤fs.length*(14*w) ∧
      Challenge.gateSlots (sunbuild acc Z bank cin w fs)≤fs.length*(14*w) := by
  by_cases h : EarlyH w fs
  · obtain ⟨src,tail,rfl,hlen,rfl⟩ := earlyH_info w fs h
    have head := earlyPrefix_gateSlots acc Z bank cin src hacc hlen
      (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
    have rest := build_gateSlots acc Z bank cin 163 hacc tail (fun f hf' => hf f (by simp [hf']))
    simp only [sbuild,sunbuild,if_pos h,earlyBuild,earlyUnbuild,earlyTerm_src,Challenge.gateSlots_append,
      List.length_cons]
    omega
  · simpa only [sbuild,sunbuild,if_neg h] using baseBuild_gateSlots acc Z bank cin w hacc fs hf

end ECDSAAdd.Entrant.Acc

end

section
-- ===== SquareFolds =====

/-! Sign-grouped fold schedule for the measured streamed square.
Each fold list is reordered so that all folds of one sign are applied
consecutively, and each branch starts in the orientation the previous branch
ended in. Modular addition is commutative, so the signed payload sum is
unchanged, while the number of 255-Toffoli output reflections drops from 20
to 4 (one per branch plus the final restoring reflection). -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Folds of sign `first`, then the folds of the other sign. -/
def sortedItems (first : Bool) (items : List MeasuredSquareFold) : List MeasuredSquareFold :=
  items.filter (fun f => f.negative == first) ++ items.filter (fun f => !(f.negative == first))

theorem sorted_perm (first : Bool) (items : List MeasuredSquareFold) :
    (sortedItems first items).Perm items :=
  List.filter_append_perm _ _

theorem signedSum_perm (base : BasisState) {a b : List MeasuredSquareFold} (h : a.Perm b) :
    measuredSignedSum base a=measuredSignedSum base b := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [measuredSignedSum, ih]
  | swap x y l => simp only [measuredSignedSum]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def fastAItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems false L.measuredAItems
def fastBItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems true L.measuredBItems
def fastCItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  sortedItems false L.measuredCItems

def fastBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L))
def fastBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L))
def fastMiddleC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.sum L.core.product (L.measuredFolds false (fastCItems L))
def fastBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++fastMiddleC L control++L.core.clearSum

def fastProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  fastBranchA L control++fastBranchB L control++fastBranchC L control++L.reflectOutput

theorem fast_orientations (L : CuccaroStreamedSquareWideLayout) :
    measuredFinalOrientation false (fastAItems L)=true ∧
    measuredFinalOrientation true (fastBItems L)=false ∧
    measuredFinalOrientation false (fastCItems L)=true := by
  simp [measuredFinalOrientation,fastAItems,fastBItems,fastCItems,sortedItems,measuredAItems,
    measuredBItems,measuredCItems,shiftedProductItems,nafMinusOneItems,List.filter_cons]

/-- The unique canonical value with a given orientation cast. -/
def ofCast (o : Bool) (z : ZMod SquareReduction.p) : Nat := if o then (-1-z).val else z.val

theorem ofCast_lt (o : Bool) (z : ZMod SquareReduction.p) : ofCast o z<SquareReduction.p := by
  haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
  cases o
  · simp only [ofCast,Bool.false_eq_true,if_false]
    exact ZMod.val_lt _
  · simp only [ofCast,if_true]
    exact ZMod.val_lt _

theorem cast_ofCast (o : Bool) (z : ZMod SquareReduction.p) :
    measuredOrientationCast o (ofCast o z)=z := by
  haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
  cases o
  · simp [measuredOrientationCast,ofCast,ZMod.natCast_zmod_val]
  · simp only [measuredOrientationCast,ofCast,if_true,ZMod.natCast_zmod_val]
    ring

def resA (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P))
def resB (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast true O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P))
def resC (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+(-(P : ZMod SquareReduction.p)*2^128))

theorem fastA_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastAItems L) : f∈L.measuredAItems := (sorted_perm _ _).subset hf
theorem fastB_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastBItems L) : f∈L.measuredBItems := (sorted_perm _ _).subset hf
theorem fastC_mem (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold)
    (hf : f∈fastCItems L) : f∈L.measuredCItems := (sorted_perm _ _).subset hf

theorem fastBranchA_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastBranchA L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchA L control) records s).basis=
      resA ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchA L control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := L.withMeasuredSquare_contribution hw control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) false (fastAItems L) s records hc dstZero
    O (M^2) (resA (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp f hf => L.measuredA_views hw t M mb hp f (fastA_mem L f hf))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredA_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).1]
      exact cast_ofCast _ _)
  exact result

theorem fastBranchB_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastBranchB L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchB L control) records s).basis=
      resB ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchB L control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := L.withMeasuredSquare_contribution hw control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) true (fastBItems L) s records hc dstZero
    O (M^2) (resB (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp f hf => L.measuredB_views hw t M mb hp f (fastB_mem L f hf))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredB_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).2.1]
      exact cast_ofCast _ _)
  exact result

theorem fastMiddleC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (fastMiddleC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastMiddleC L control) records s).basis=
      resC ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastMiddleC L control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := L.withMeasuredSquare_contribution hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) false (fastCItems L) s records hc hp0
    O (M^2) (resC (M^2) O) hO ho (by rw [hs])
    (fun _ hp _ => hp) (fun t hp f hf => L.measuredC_views hw t M hp f (fastC_mem L f hf))
    (-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)
    (fun t hp => (signedSum_perm t (sorted_perm _ _)).trans (L.measuredC_sum hw t (M^2) hp))
    (ofCast_lt _ _) (by
      rw [(fast_orientations L).2.2]
      exact cast_ofCast _ _)
  exact result

theorem fastBranchC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) :
    (run (fastBranchC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastBranchC L control) records s).basis=
      resC ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (fastBranchC L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := fastMiddleC L control
  let u := run L.core.prepareSum [] s
  let v := run middle (records.take (measurementCount middle)) u
  let out := run L.core.clearSum (records.drop (measurementCount middle)) v
  have prep := L.prepareSum_frame hw nd s.basis A B ha hb bound (PairClean.corePad L s.basis hc) hc.cin
    s [] (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have used := fastMiddleC_correct L hw control hn (A+B) O hO u
    (records.take (measurementCount middle)) prep.2.1 outU productU cleanU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have cleared := L.clearSum_frame hw nd restoreBase A B lowRestore sumRestore bound padRestore cinRestore
    v (records.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resC ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resC ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  have prepM := (L.core.sum_counts hw.core).1.2
  simpa [fastBranchC,middle,u,v,out,run_append,prepM] using final

theorem fast_complete_exact (enabled : Bool) (A B O : Nat) :
    SquareReduction.p-1-resC ((if enabled then A+B else 0)^2)
      (resB ((if enabled then B else 0)^2) (resA ((if enabled then A else 0)^2) O))=
      subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  have ea : measuredOrientationCast true OA=measuredOrientationCast false O+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast false OB=measuredOrientationCast true OA+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ec : measuredOrientationCast true OC=measuredOrientationCast false OB+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have lhsBound : SquareReduction.p-1-OC<SquareReduction.p := by
    have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
    omega
  have cast : ((SquareReduction.p-1-OC : Nat) : ZMod SquareReduction.p)=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [measuredReflection_zmod OC ocBound,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt lhsBound,ZMod.val_natCast_of_lt targetBound] using value

theorem fastProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (fastProgram L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastProgram L control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (fastProgram L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  let restA := records.drop (measurementCount (fastBranchA L control))
  let restB := restA.drop (measurementCount (fastBranchB L control))
  let restC := restB.drop (measurementCount (fastBranchC L control))
  let u := run (fastBranchA L control) (records.take (measurementCount (fastBranchA L control))) s
  let v := run (fastBranchB L control) (restA.take (measurementCount (fastBranchB L control))) u
  let w := run (fastBranchC L control) (restB.take (measurementCount (fastBranchC L control))) v
  let out := run L.reflectOutput restC w
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := fastBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (fastBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := fastBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (fastBranchB L control))) highU ea.2.1 productU cleanU
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A := regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have sumV : regValue L.core.sum v.basis=B :=
    (regValue_congr _ _ _ (fun q hq => sameV q (sumAway q hq))).trans sumB
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ec := fastBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    (restB.take (measurementCount (fastBranchC L control))) lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have cleanW : L.PairClean w.basis :=
    L.squareFrame_clean nd s.basis w.basis OC ⟨ec.2.1,sameW⟩ hc
  have er := L.reflectOutput_correct hw nd OC (ofCast_lt _ _) w restC ec.2.1 cleanW
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    exact er.2.1.trans exactResult
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨er.1.trans (ec.1.trans (eb.1.trans ea.1)),fullValue,?_⟩
    intro q hq
    exact (er.2.2 q hq).trans (sameW q hq)
  simpa [fastProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

theorem fast_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (measuredFoldsT false (fastAItems L)=6393 ∧ measuredFoldsM false (fastAItems L)=6393) ∧
    (measuredFoldsT true (fastBItems L)=30941 ∧ measuredFoldsM true (fastBItems L)=30933) ∧
    (measuredFoldsT false (fastCItems L)=6393 ∧ measuredFoldsM false (fastCItems L)=6393) := by
  norm_num [fastAItems,fastBItems,fastCItems,sortedItems,measuredAItems,measuredBItems,measuredCItems,
    nafMinusOneItems,shiftedProductItems,List.filter_cons,measuredFoldsT,measuredFoldsM]

theorem fastProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (fastProgram L control)=95822 ∧ measurementCount (fastProgram L control)=95302 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L)) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L)) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := L.measuredFolds_counts hw false (fastAItems L)
  have fb := L.measuredFolds_counts hw true (fastBItems L)
  have fc := L.measuredFolds_counts hw false (fastCItems L)
  have prices := fast_item_prices L
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

theorem fastProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (fastProgram L control)⊆(control::L.wires).toFinset := by
  have items := L.measured_items_support
  have a : ECDSAAdd.wires (L.measuredFolds false (fastAItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control false (fastAItems L) (fun f hf => items.1 f (fastA_mem L f hf))
  have b : ECDSAAdd.wires (L.measuredFolds true (fastBItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control true (fastBItems L) (fun f hf => items.2.1 f (fastB_mem L f hf))
  have c : ECDSAAdd.wires (L.measuredFolds false (fastCItems L))⊆(control::L.wires).toFinset :=
    L.measuredFolds_support control false (fastCItems L) (fun f hf => items.2.2 f (fastC_mem L f hf))
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa : ECDSAAdd.wires (fastBranchA L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (L.measuredFolds false (fastAItems L)) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb : ECDSAAdd.wires (fastBranchB L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (L.measuredFolds true (fastBItems L)) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc : ECDSAAdd.wires (fastMiddleC L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by omega) (by omega) (by rw [hw.core.product,sum])
    (by
      intro q hq
      simp only [CuccaroStreamedSquareLayout.sum,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl
      · exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq))
      · simp)
    (fun _ hq => hq) c
  have sumCert := L.sum_certified hw hn
  have embed : L.wires.toFinset⊆(control::L.wires).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons] at hq ⊢; exact Or.inr hq
  have prep := sumCert.1.2.trans embed
  have unprep := sumCert.2.2.trans embed
  have reflection : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
    (L.measured_small_support control).2.2.1
  simpa only [fastProgram,fastBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

theorem fastProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (fastProgram L control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hc := L.measuredItems_counts hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have a := L.withMeasuredSquare_physical control hn _ _ hl hp _
    (L.measuredFolds_physical hw nd false (fastAItems L) (fun f hf => hc.1 f (fastA_mem L f hf)))
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (L.measuredFolds_physical hw nd true (fastBItems L) (fun f hf => hc.2.1 f (fastB_mem L f hf)))
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (L.measuredFolds_physical hw nd false (fastCItems L) (fun f hf => hc.2.2 f (fastC_mem L f hf)))
  have prep := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

theorem fastProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (fastProgram L control) ≤ 5000000 := by
  have ha := Baselines.measuredFolds_gateSlots_le L hw false (fastAItems L)
  have hb := Baselines.measuredFolds_gateSlots_le L hw true (fastBItems L)
  have hc := Baselines.measuredFolds_gateSlots_le L hw false (fastCItems L)
  have la : (fastAItems L).length = 6 := (sorted_perm _ _).length_eq
  have lb : (fastBItems L).length = 26 := (sorted_perm _ _).length_eq
  have lc : (fastCItems L).length = 6 := (sorted_perm _ _).length_eq
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (L.measuredFolds false (fastAItems L)) hd
  have b := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (L.measuredFolds true (fastBItems L)) hd
  have c := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (L.measuredFolds false (fastCItems L)) (by rw [hw.core.product])
  have hp := Baselines.cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change Challenge.gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [fastProgram,fastBranchA,fastBranchB,fastBranchC,fastMiddleC,
    CuccaroStreamedSquareLayout.clearSum, Challenge.gateSlots_append, Baselines.reverse_gateSlots]
  omega

end ECDSAAdd.Entrant

end

section
-- ===== AccFold =====

/-! Accumulated correction fold in the streamed-square workspace, and a fold
schedule mixing ordinary folds with accumulated ones. The accumulator is the
low 163 bits of the fold work register; zero padding comes from the unused
work bits and fold pad; carries come from the fold pad. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- An accumulated fold. `terms` are summed into the 163-bit accumulator; they
may read the 33-bit temporary `wTemp`, which `pre` fills (from product slices)
before the accumulator is built and empties afterwards, on both sides of the
modular addition. `spec` is the original term list whose exact sum the
accumulator must equal; it fixes the payload. Plain items use `pre=[]` and
`spec=terms`. -/
structure AccItem where
  negative : Bool
  pre : List MeasuredSquareFold
  terms : List MeasuredSquareFold
  spec : List MeasuredSquareFold

def accReg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 163
def wTemp (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.core.work.drop 163).take 33
def accZ (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 196++L.foldPad.drop 160
def accBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 160

/-- Items with a temporary (branch B) also shift it out of the high product
half before their terms are summed: `hiReg ← hiReg − W` by the measured
in-place subtractor, restored by the measured adder afterwards. W stays in
`wTemp` meanwhile, so both steps are exact and reversible. -/
def hiReg (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.core.product.take 256).drop 128
def hiSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := wTemp L++(accZ L).take 95
def hiBank (L : CuccaroStreamedSquareWideLayout) : List Wire := (accBank L).take 127
def splitIn (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  if a.pre=[] then [] else subInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin
def splitOut (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  if a.pre=[] then [] else addInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin

def tempIn (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  Acc.sbuild (wTemp L) (accZ L) (accBank L) L.core.cin 33 a.pre
def tempOut (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  Acc.sunbuild (wTemp L) (accZ L) (accBank L) L.core.cin 33 a.pre

def fillIn (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++(splitIn L a++Acc.sbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++splitOut L a)++
    tempOut L a
def fillOut (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  tempIn L a++(splitIn L a++Acc.sunbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 a.terms++splitOut L a)++
    tempOut L a

def accFold (L : CuccaroStreamedSquareWideLayout) (a : AccItem) : Program :=
  fillIn L a++L.measuredCore.program SquareReduction.c SquareReduction.p++fillOut L a

def TermOK (f : MeasuredSquareFold) : Prop :=
  f.src.length+f.shift<163 ∧ 163-f.shift-f.src.length≤154 ∧ 163-f.shift-1≤160

def TermOK33 (f : MeasuredSquareFold) : Prop :=
  f.src.length+f.shift<33 ∧ 33-f.shift-f.src.length≤154 ∧ 33-f.shift-1≤160

def SrcOK (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Prop :=
  ∀q,f.src.count q≤(L.core.product++wTemp L).count q

structure AccView (L : CuccaroStreamedSquareWideLayout) (base : BasisState) (a : AccItem) : Prop where
  count : ∀f∈a.terms,SrcOK L f
  ok : ∀f∈a.terms,TermOK f
  preCount : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q
  preOk : ∀f∈a.pre,TermOK33 f
  preValid : Acc.Valid base 33 0 a.pre
  specValid : Acc.Valid base 163 0 a.spec
  hiLe : Acc.accVal base 0 a.pre≤regValue (hiReg L) base
  value : ∀t : BasisState,(∀q∈L.core.product,q∉hiReg L → t q=base q) →
    regValue (hiReg L) t+(if a.pre=[] then 0 else Acc.accVal base 0 a.pre)=regValue (hiReg L) base →
    regValue (wTemp L) t=Acc.accVal base 0 a.pre →
    Acc.Valid t 163 0 a.terms ∧ Acc.accVal t 0 a.terms=Acc.accVal base 0 a.spec

theorem acc_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (accReg L).length=163 ∧ (accZ L).length=154 ∧ (accBank L).length=160 ∧ (wTemp L).length=33 := by
  simp [accReg,accZ,accBank,wTemp,foldPad,hw.core.work,hw.core.pad,hw.overflowPad]

theorem fitsLen_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (ok : TermOK f) : Acc.FitsLen (accZ L) (accBank L) 163 f := by
  have l := acc_lengths L hw
  exact ⟨ok.1,by rw [l.2.1]; exact ok.2.1,by rw [l.2.2.1]; exact ok.2.2⟩

theorem fitsLen33_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (ok : TermOK33 f) : Acc.FitsLen (accZ L) (accBank L) 33 f := by
  have l := acc_lengths L hw
  exact ⟨ok.1,by rw [l.2.1]; exact ok.2.1,by rw [l.2.2.1]; exact ok.2.2⟩

theorem work_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.core.work.take 163).count q+(wTemp L).count q+(L.core.work.drop 196).count q=L.core.work.count q := by
  have h1 := congrArg (List.count q) (List.take_append_drop 163 L.core.work)
  have h2 := congrArg (List.count q) (List.take_append_drop 33 (L.core.work.drop 163))
  have dd : (L.core.work.drop 163).drop 33=L.core.work.drop 196 := by simp [List.drop_drop]
  rw [dd] at h2
  simp only [List.count_append] at h1 h2
  simp only [wTemp]
  omega

theorem pad_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.foldPad.take 160).count q+(L.foldPad.drop 160).count q=L.core.pad.count q+L.overflowPad.count q := by
  rw [←List.count_append,List.take_append_drop]
  simp [foldPad,List.count_append]

theorem fits_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (f : MeasuredSquareFold) (hs : SrcOK L f) (ok : TermOK f) :
    Acc.Fits (accReg L) (accZ L) (accBank L) L.core.cin 163 f := by
  refine ⟨fitsLen_of L hw f ok,?_⟩
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := hs q
  have e1 := work_split L q
  have e2 := pad_split L q
  simp only [accReg,accZ,accBank,List.count_cons,List.count_append] at b ⊢
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  split <;> split at h <;> omega

theorem fitsPre_of (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (f : MeasuredSquareFold) (hs : ∀q,f.src.count q≤L.core.product.count q) (ok : TermOK33 f) :
    Acc.Fits (wTemp L) (accZ L) (accBank L) L.core.cin 33 f := by
  refine ⟨fitsLen33_of L hw f ok,?_⟩
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := hs q
  have e1 := work_split L q
  have e2 := pad_split L q
  simp only [accZ,accBank,List.count_cons,List.count_append] at ⊢
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  split <;> split at h <;> omega

/-- Membership in two disjoint parts of the layout, by counting. -/
theorem layout_count_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 196) :
    q∉accReg L ∧ q∉wTemp L := by
  have h := List.nodup_iff_count_le_one.mp hn q
  have b := List.count_pos_iff.mpr hq
  have e1 := work_split L q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append,List.count_cons,List.count_nil] at h b
  constructor
  · intro bad; have a := List.count_pos_iff.mpr bad; simp only [accReg] at a; omega
  · intro bad; have a := List.count_pos_iff.mpr bad; omega

theorem accReg_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) :
    q∉accReg L := by
  intro bad
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := List.count_pos_iff.mpr bad
  have b := List.count_pos_iff.mpr hq
  have e1 : (L.core.work.take 163).count q+(L.core.work.drop 163).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg] at a
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append,List.count_cons,List.count_nil] at h b
  omega

theorem acc_temp_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈accReg L) : q∉wTemp L := by
  intro bad
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  have e1 := work_split L q
  simp only [accReg] at a
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  omega

theorem accReg_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accReg L) : q∈L.core.work :=
  List.mem_of_mem_take hq

theorem wTemp_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈wTemp L) : q∈L.core.work :=
  List.mem_of_mem_drop (List.mem_of_mem_take hq)

theorem accZ_mem (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accZ L) :
    q∈L.foldPad ∨ q∈L.core.work.drop 196 := by
  simp only [accZ,List.mem_append] at hq
  rcases hq with h|h
  · exact Or.inr h
  · exact Or.inl (List.mem_of_mem_drop h)

theorem accZ_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈accZ L) :
    q∉accReg L ∧ q∉wTemp L := by
  apply layout_count_away L hn q
  rcases accZ_mem L q hq with h|h <;> simp [h]

theorem accBank_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈accBank L) :
    q∉accReg L ∧ q∉wTemp L :=
  layout_count_away L hn q (by simp [List.mem_of_mem_take hq])

theorem cin_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    L.core.cin∉accReg L ∧ L.core.cin∉wTemp L :=
  layout_count_away L hn _ (by simp)

theorem product_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.core.product) : q∉accReg L ∧ q∉wTemp L :=
  layout_count_away L hn q (by simp [hq])

theorem hiReg_product (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈hiReg L) :
    q∈L.core.product :=
  List.mem_of_mem_take (List.mem_of_mem_drop hq)

theorem split_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (hiSrc L).length=128 ∧ (hiReg L).length=128 ∧ (hiBank L).length=127 := by
  have l := acc_lengths L hw
  refine ⟨?_,?_,?_⟩
  · simp only [hiSrc,List.length_append,List.length_take,l.2.1,l.2.2.2]
    omega
  · simp only [hiReg,List.length_drop,List.length_take,hw.core.product]
    omega
  · simp only [hiBank,List.length_take,l.2.2.1]
    omega

theorem split_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    (L.core.cin::(hiSrc L++hiReg L++hiBank L)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have e1 := work_split L q
  have e2 := pad_split L q
  have s1 := (List.take_sublist 95 (accZ L)).count_le q
  have s2 := (List.drop_sublist 128 (L.core.product.take 256)).count_le q
  have s3 := (List.take_sublist 256 L.core.product).count_le q
  have s4 := (List.take_sublist 127 (accBank L)).count_le q
  have zc : (accZ L).count q=(L.core.work.drop 196).count q+(L.foldPad.drop 160).count q := by
    simp [accZ,List.count_append]
  have bc : (accBank L).count q=(L.foldPad.take 160).count q := rfl
  simp only [hiSrc,hiReg,hiBank,List.count_cons,List.count_append]
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  split <;> split at h <;> omega

theorem aux_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉hiReg L :=
  fun bad => (L.pairAuxAway hn q hq).1 (hiReg_product L q bad)

theorem accZ_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈accZ L) : q∉hiReg L := by
  apply aux_not_hi L hn q
  rcases accZ_mem L q hq with h|h
  · simp [h]
  · simp [List.mem_of_mem_drop h]

theorem accBank_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈accBank L) : q∉hiReg L :=
  aux_not_hi L hn q (by simp [List.mem_of_mem_take hq])

theorem accReg_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈accReg L) : q∉hiReg L :=
  aux_not_hi L hn q (by simp [accReg_work L q hq])

theorem wTemp_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈wTemp L) : q∉hiReg L :=
  aux_not_hi L hn q (by simp [wTemp_work L q hq])

theorem cin_not_hi (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : L.core.cin∉hiReg L :=
  aux_not_hi L hn _ (by simp)

/-- Shift the temporary out of the high half, run a middle step on the
accumulator, and shift it back. -/
theorem split_mid (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t : BasisState) (W H : Nat) (hle : W≤H)
    (hH : regValue (hiReg L) t=H) (hWv : regValue (wTemp L) t=W)
    (tz : ∀q∈accZ L,t q=false) (tb : ∀q∈accBank L,t q=false) (tc : t L.core.cin=false)
    (Bp : Program) (V0 V1 : Nat)
    (hB : ∀u : BasisState,(∀q,q∉hiReg L → q∉accReg L → u q=t q) → regValue (hiReg L) u+W=H →
      Triple (SquareFrame (accReg L) u V0) Bp (SquareFrame (accReg L) u V1)) :
    Triple (SquareFrame (accReg L) t V0)
      (subInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin++Bp++addInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin)
      (SquareFrame (accReg L) t V1) := by
  have lens := split_lengths L hw
  have nd := split_nodup L hn
  have hx : (hiSrc L).length=(hiReg L).length := lens.1.trans lens.2.1.symm
  have hc : (hiBank L).length+1=(hiReg L).length := by rw [lens.2.2,lens.2.1]
  have Hlt : H<2^128 := by
    rw [←hH]; have := regValue_lt (hiReg L) t; rwa [lens.2.1] at this
  have srcOut (q : Wire) (hq : q∈hiSrc L) : q∉hiReg L ∧ q∉accReg L := by
    simp only [hiSrc,List.mem_append] at hq
    rcases hq with h|h
    · exact ⟨wTemp_not_hi L hn q h,fun b => acc_temp_disjoint L hn q b h⟩
    · have hz := List.mem_of_mem_take h
      exact ⟨accZ_not_hi L hn q hz,(accZ_away L hn q hz).1⟩
  have bankOut (q : Wire) (hq : q∈hiBank L) : q∉hiReg L ∧ q∉accReg L :=
    ⟨accBank_not_hi L hn q (List.mem_of_mem_take hq),(accBank_away L hn q (List.mem_of_mem_take hq)).1⟩
  have srcVal (u : BasisState) (hu : ∀q∈hiSrc L,u q=t q) : regValue (hiSrc L) u=W := by
    rw [regValue_congr _ _ _ hu,hiSrc,regValue_append,hWv]
    have z : regValue ((accZ L).take 95) t=0 :=
      (regValue_zero _ _).mpr (fun q hq => tz q (List.mem_of_mem_take hq))
    rw [z]; simp
  let P1 (u : BasisState) : Prop :=
    regValue (accReg L) u=V0 ∧ regValue (hiReg L) u+W=H ∧ ∀q,q∉hiReg L → q∉accReg L → u q=t q
  let P2 (u : BasisState) : Prop :=
    regValue (accReg L) u=V1 ∧ regValue (hiReg L) u+W=H ∧ ∀q,q∉hiReg L → q∉accReg L → u q=t q
  have t1 : Triple (SquareFrame (accReg L) t V0) (subInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin) P1 := by
    intro s m hs
    have xs : regValue (hiSrc L) s.basis=W := srcVal _ (fun q hq => hs.2 q (srcOut q hq).2)
    have ys : regValue (hiReg L) s.basis=H :=
      (regValue_congr _ _ _ (fun q hq => hs.2 q (fun b => accReg_not_hi L hn q b hq))).trans hH
    have cs : s.basis L.core.cin=false := (hs.2 _ (cin_away L hn).1).trans tc
    have ks : regValue (hiBank L) s.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (hs.2 q (bankOut q hq).2).trans (tb q (List.mem_of_mem_take hq)))
    have spec := subInPlace_spec (hiSrc L) (hiReg L) (hiBank L) L.core.cin nd hx hc W H s m ⟨⟨⟨xs,ys⟩,cs⟩,ks⟩
    have yv : regValue (hiReg L) (run (subInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin) m s).basis=
        (H+2^(hiReg L).length-W)%2^(hiReg L).length := spec.2.1.1.2
    have fr := subInPlace_frame (hiSrc L) (hiReg L) (hiBank L) L.core.cin nd hx hc s m cs ks
    refine ⟨spec.1,?_,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => fr q (accReg_not_hi L hn q hq))]; exact hs.1
    · rw [yv,lens.2.1,show H+2^128-W=(H-W)+2^128 by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
      omega
    · intro q h1 h2; rw [fr q h1]; exact hs.2 q h2
  have t2 : Triple P1 Bp P2 := by
    intro s m ⟨h1,h2,h3⟩
    obtain ⟨ph,hv,hf⟩ := hB s.basis h3 h2 s m ⟨h1,fun _ _ => rfl⟩
    refine ⟨ph,hv,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf q (fun b => accReg_not_hi L hn q b hq))]; exact h2
    · intro q q1 q2; rw [hf q q2]; exact h3 q q1 q2
  have t3 : Triple P2 (addInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin) (SquareFrame (accReg L) t V1) := by
    intro s m ⟨h1,h2,h3⟩
    have xs : regValue (hiSrc L) s.basis=W := srcVal _ (fun q hq => h3 q (srcOut q hq).1 (srcOut q hq).2)
    have kclean : ∀q∈hiBank L,s.basis q=false :=
      fun q hq => (h3 q (bankOut q hq).1 (bankOut q hq).2).trans (tb q (List.mem_of_mem_take hq))
    have cs : s.basis L.core.cin=false := (h3 _ (cin_not_hi L hn) (cin_away L hn).1).trans tc
    obtain ⟨ph,hf,hy⟩ := addInPlace_correct (hiSrc L) (hiReg L) (hiBank L) L.core.cin nd hx hc s m kclean
    refine ⟨ph,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf q (accReg_not_hi L hn q hq))]; exact h1
    · have hv : regValue (hiReg L) (run (addInPlace (hiSrc L) (hiReg L) (hiBank L) L.core.cin) m s).basis=
          regValue (hiReg L) t := by
        rw [hy,xs,cs,lens.2.1,hH]
        simp only [Bool.toNat_false,Nat.add_zero]
        rw [show W+regValue (hiReg L) s.basis=H by omega,Nat.mod_eq_of_lt Hlt]
      intro q hq
      by_cases hh : q∈hiReg L
      · exact (regValue_eq_iff _ _ _).mp hv q hh
      · rw [hf q hh]; exact h3 q hh hq
  exact (t1.seq t2).seq t3

theorem split_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    (toffoliCount (splitIn L a)=(if a.pre=[] then 0 else 127) ∧
      measurementCount (splitIn L a)=(if a.pre=[] then 0 else 127)) ∧
    (toffoliCount (splitOut L a)=(if a.pre=[] then 0 else 127) ∧
      measurementCount (splitOut L a)=(if a.pre=[] then 0 else 127)) := by
  have lens := split_lengths L hw
  have hx : (hiSrc L).length=(hiReg L).length := lens.1.trans lens.2.1.symm
  have hc : (hiBank L).length+1=(hiReg L).length := by rw [lens.2.2,lens.2.1]
  have sc := subInPlace_counts (hiSrc L) (hiReg L) (hiBank L) L.core.cin hx hc
  have ac := addInPlace_counts (hiSrc L) (hiReg L) (hiBank L) L.core.cin hx hc
  rw [lens.2.1] at sc ac
  by_cases hp : a.pre=[]
  · simp [splitIn,splitOut,hp,toffoliCount,measurementCount]
  · simp only [splitIn,splitOut,hp,if_false]
    exact ⟨sc,ac⟩

theorem split_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) (a : AccItem) :
    ECDSAAdd.wires (splitIn L a)⊆(control::L.wires).toFinset ∧
    ECDSAAdd.wires (splitOut L a)⊆(control::L.wires).toFinset := by
  have lens := split_lengths L hw
  have hx : (hiSrc L).length=(hiReg L).length := lens.1.trans lens.2.1.symm
  have hc : (hiBank L).length+1=(hiReg L).length := by rw [lens.2.2,lens.2.1]
  have inW (q : Wire) (hq : q∈L.core.work∨q∈L.foldPad∨q∈L.core.product∨q=L.core.cin) :
      q∈(control::L.wires).toFinset := by
    simp only [List.mem_toFinset,List.mem_cons,CuccaroStreamedSquareWideLayout.wires,
      CuccaroStreamedSquareLayout.wires,foldPad,List.mem_append] at hq ⊢
    tauto
  have sub : (L.core.cin::(hiSrc L++hiReg L++hiBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with h|((h|h)|h)
    · exact inW q (Or.inr (Or.inr (Or.inr h)))
    · simp only [hiSrc,List.mem_append] at h
      rcases h with h|h
      · exact inW q (Or.inl (wTemp_work L q h))
      · rcases accZ_mem L q (List.mem_of_mem_take h) with h'|h'
        · exact inW q (Or.inr (Or.inl h'))
        · exact inW q (Or.inl (List.mem_of_mem_drop h'))
    · exact inW q (Or.inr (Or.inr (Or.inl (hiReg_product L q h))))
    · exact inW q (Or.inr (Or.inl (List.mem_of_mem_take (List.mem_of_mem_take h))))
  by_cases hp : a.pre=[]
  · simp [splitIn,splitOut,hp,ECDSAAdd.wires]
  · simp only [splitIn,splitOut,hp,if_false]
    exact ⟨(subInPlace_wires _ _ _ _ hx hc).trans_subset sub,(addInPlace_wires _ _ _ _ hx hc).trans_subset sub⟩

theorem split_physical (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (a : AccItem) :
    GatePhysical (splitIn L a) ∧ GatePhysical (splitOut L a) := by
  have nd := split_nodup L hn
  by_cases hp : a.pre=[]
  · simp [splitIn,splitOut,hp,GatePhysical]
  · simp only [splitIn,splitOut,hp,if_false]
    exact ⟨subInPlace_physical _ _ _ _ nd,addInPlace_physical _ _ _ _ nd⟩

theorem split_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem) :
    Challenge.gateSlots (splitIn L a)≤1792 ∧ Challenge.gateSlots (splitOut L a)≤1536 := by
  have lens := split_lengths L hw
  have s := Baselines.subInPlace_gateSlots_le (hiSrc L) (hiReg L) (hiBank L) L.core.cin
  have t := Baselines.addInPlace_gateSlots_le (hiSrc L) (hiReg L) (hiBank L) L.core.cin
  rw [lens.1,lens.2.1] at s
  rw [lens.1] at t
  by_cases hp : a.pre=[]
  · simp [splitIn,splitOut,hp,Challenge.gateSlots]
  · simp only [splitIn,splitOut,hp,if_false]
    exact ⟨by omega,by omega⟩

/-- Temporary filled, middle step on the accumulator, temporary emptied. -/
theorem fill_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) (M : Program) (V0 V1 : Nat)
    (hM : ∀t : BasisState,(∀q∈L.core.product,t q=base q) →
      regValue (wTemp L) t=Acc.accVal base 0 a.pre →
      (∀q∈accZ L,t q=false) → (∀q∈accBank L,t q=false) → t L.core.cin=false →
      Triple (SquareFrame (accReg L) t V0) M (SquareFrame (accReg L) t V1)) :
    Triple (SquareFrame (accReg L) b V0) (tempIn L a++M++tempOut L a)
      (SquareFrame (accReg L) b V1) := by
  have lens := acc_lengths L hw
  have fitsP (f : MeasuredSquareFold) (hf : f∈a.pre) := fitsPre_of L hw hn f (hv.preCount f hf) (hv.preOk f hf)
  have memP (f : MeasuredSquareFold) (hf : f∈a.pre) (q : Wire) (hq : q∈f.src) : q∈L.core.product := by
    have pos := List.count_pos_iff.mpr hq
    have bound := hv.preCount f hf q
    exact List.count_pos_iff.mp (by omega)
  let Wv := Acc.accVal base 0 a.pre
  let Rest (t : BasisState) : Prop := ∀q,q∉accReg L → q∉wTemp L → t q=b q
  have restProd (t : BasisState) (h : Rest t) : ∀q∈L.core.product,t q=base q :=
    fun q hq => (h q (product_away L hn q hq).1 (product_away L hn q hq).2).trans (agree q hq)
  have restZ (t : BasisState) (h : Rest t) : ∀q∈accZ L,t q=false :=
    fun q hq => (h q (accZ_away L hn q hq).1 (accZ_away L hn q hq).2).trans (hz q hq)
  have restB (t : BasisState) (h : Rest t) : ∀q∈accBank L,t q=false :=
    fun q hq => (h q (accBank_away L hn q hq).1 (accBank_away L hn q hq).2).trans (hb q hq)
  have restC (t : BasisState) (h : Rest t) : t L.core.cin=false :=
    (h _ (cin_away L hn).1 (cin_away L hn).2).trans hi
  have preCongr (t : BasisState) (ht : ∀q∈L.core.product,t q=base q) :=
    Acc.valid_congr base t 33 a.pre (fun f hf => regValue_congr _ _ _
      (fun q hq => (ht q (memP f hf q hq)).symm)) 0
  -- step 1: fill the temporary
  have t1 : Triple (SquareFrame (accReg L) b V0) (tempIn L a)
      (fun t => regValue (accReg L) t=V0 ∧ regValue (wTemp L) t=Wv ∧ Rest t) := by
    unfold tempIn
    intro s m hs
    have rs : Rest s.basis := fun q hq _ => hs.2 q hq
    have hW1 : ∀q∈wTemp L,s.basis q=false :=
      fun q hq => (hs.2 q (fun h => acc_temp_disjoint L hn q h hq)).trans (hW q hq)
    have pc := preCongr s.basis (restProd _ rs)
    have h1 := Acc.sbuild_triple (wTemp L) (accZ L) (accBank L) L.core.cin 33 lens.2.2.2 s.basis
      (restZ _ rs) (restB _ rs) (restC _ rs) a.pre fitsP (pc.1.mp hv.preValid)
    obtain ⟨ph,hv1,hf1⟩ := h1 s m ⟨(regValue_zero _ _).mpr hW1,fun _ _ => rfl⟩
    refine ⟨ph,?_,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf1 q (acc_temp_disjoint L hn q hq))]; exact hs.1
    · rw [hv1]; exact pc.2.symm
    · intro q h1q h2q; rw [hf1 q h2q]; exact hs.2 q h1q
  -- step 2: the middle program on the accumulator
  have t2 : Triple (fun t => regValue (accReg L) t=V0 ∧ regValue (wTemp L) t=Wv ∧ Rest t) M
      (fun t => regValue (accReg L) t=V1 ∧ regValue (wTemp L) t=Wv ∧ Rest t) := by
    intro s m ⟨ha,hwv,hr⟩
    have h2 := hM s.basis (restProd _ hr) hwv (restZ _ hr) (restB _ hr) (restC _ hr)
    obtain ⟨ph,hv2,hf2⟩ := h2 s m ⟨ha,fun _ _ => rfl⟩
    refine ⟨ph,hv2,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf2 q (fun h => acc_temp_disjoint L hn q h hq))]; exact hwv
    · intro q h1q h2q; rw [hf2 q h1q]; exact hr q h1q h2q
  -- step 3: empty the temporary
  have t3 : Triple (fun t => regValue (accReg L) t=V1 ∧ regValue (wTemp L) t=Wv ∧ Rest t) (tempOut L a)
      (SquareFrame (accReg L) b V1) := by
    unfold tempOut
    intro s m ⟨ha,hwv,hr⟩
    have pc := preCongr s.basis (restProd _ hr)
    have h3 := Acc.sunbuild_triple (wTemp L) (accZ L) (accBank L) L.core.cin 33 lens.2.2.2 s.basis
      (restZ _ hr) (restB _ hr) (restC _ hr) a.pre fitsP (pc.1.mp hv.preValid)
    obtain ⟨ph,hv3,hf3⟩ := h3 s m ⟨by rw [hwv]; exact pc.2,fun _ _ => rfl⟩
    refine ⟨ph,?_,?_⟩
    · rw [regValue_congr _ _ _ (fun q hq => hf3 q (acc_temp_disjoint L hn q hq))]; exact ha
    · intro q hq
      by_cases hwq : q∈wTemp L
      · rw [(regValue_zero _ _).mp hv3 q hwq]; exact (hW q hwq).symm
      · rw [hf3 q hwq]; exact hr q hq hwq
  exact (t1.seq t2).seq t3

theorem fillIn_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b 0) (fillIn L a)
      (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  by_cases hp : a.pre=[]
  · simp only [splitIn,splitOut,if_pos hp,List.nil_append,List.append_nil]
    have val := hv.value t (fun q hq _ => ht q hq)
      (by rw [if_pos hp,Nat.add_zero]; exact regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))) hwv
    have tr := Acc.sbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
    rwa [val.2] at tr
  · simp only [splitIn,splitOut,hp,if_false]
    have hH : regValue (hiReg L) t=regValue (hiReg L) base :=
      regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))
    apply split_mid L hw hn t (Acc.accVal base 0 a.pre) (regValue (hiReg L) base) hv.hiLe hH hwv tz tb tc
    intro u hu hval
    have uprod : ∀q∈L.core.product,q∉hiReg L → u q=base q :=
      fun q hq hh => (hu q hh (product_away L hn q hq).1).trans (ht q hq)
    have val := hv.value u uprod (by simpa only [hp,if_false] using hval)
      ((regValue_congr _ _ _ (fun q hq => hu q (wTemp_not_hi L hn q hq)
        (fun b => acc_temp_disjoint L hn q b hq))).trans hwv)
    have uz : ∀q∈accZ L,u q=false := fun q hq => (hu q (accZ_not_hi L hn q hq) (accZ_away L hn q hq).1).trans (tz q hq)
    have ub : ∀q∈accBank L,u q=false :=
      fun q hq => (hu q (accBank_not_hi L hn q hq) (accBank_away L hn q hq).1).trans (tb q hq)
    have uc : u L.core.cin=false := (hu _ (cin_not_hi L hn) (cin_away L hn).1).trans tc
    have tr := Acc.sbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 u uz ub uc a.terms fits val.1
    rwa [val.2] at tr

theorem fillOut_triple (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (a : AccItem) (hv : AccView L base a)
    (b : BasisState) (agree : ∀q∈L.core.product,b q=base q)
    (hz : ∀q∈accZ L,b q=false) (hb : ∀q∈accBank L,b q=false) (hi : b L.core.cin=false)
    (hW : ∀q∈wTemp L,b q=false) :
    Triple (SquareFrame (accReg L) b (Acc.accVal base 0 a.spec)) (fillOut L a)
      (SquareFrame (accReg L) b 0) := by
  have lens := acc_lengths L hw
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (hv.count f hf) (hv.ok f hf)
  apply fill_core L hw hn base a hv b agree hz hb hi hW
  intro t ht hwv tz tb tc
  by_cases hp : a.pre=[]
  · simp only [splitIn,splitOut,if_pos hp,List.nil_append,List.append_nil]
    have val := hv.value t (fun q hq _ => ht q hq)
      (by rw [if_pos hp,Nat.add_zero]; exact regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))) hwv
    have tr := Acc.sunbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 t tz tb tc a.terms fits val.1
    rwa [val.2] at tr
  · simp only [splitIn,splitOut,hp,if_false]
    have hH : regValue (hiReg L) t=regValue (hiReg L) base :=
      regValue_congr _ _ _ (fun q hq => ht q (hiReg_product L q hq))
    apply split_mid L hw hn t (Acc.accVal base 0 a.pre) (regValue (hiReg L) base) hv.hiLe hH hwv tz tb tc
    intro u hu hval
    have uprod : ∀q∈L.core.product,q∉hiReg L → u q=base q :=
      fun q hq hh => (hu q hh (product_away L hn q hq).1).trans (ht q hq)
    have val := hv.value u uprod (by simpa only [hp,if_false] using hval)
      ((regValue_congr _ _ _ (fun q hq => hu q (wTemp_not_hi L hn q hq)
        (fun b => acc_temp_disjoint L hn q b hq))).trans hwv)
    have uz : ∀q∈accZ L,u q=false := fun q hq => (hu q (accZ_not_hi L hn q hq) (accZ_away L hn q hq).1).trans (tz q hq)
    have ub : ∀q∈accBank L,u q=false :=
      fun q hq => (hu q (accBank_not_hi L hn q hq) (accBank_away L hn q hq).1).trans (tb q hq)
    have uc : u L.core.cin=false := (hu _ (cin_not_hi L hn) (cin_away L hn).1).trans tc
    have tr := Acc.sunbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 lens.1 u uz ub uc a.terms fits val.1
    rwa [val.2] at tr

theorem accFold_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFold L a)
      (SquareFrame L.core.out base ((Acc.accVal base 0 a.spec+O)%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFold,List.append_assoc,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let mk := measurementCount (L.measuredCore.program SquareReduction.c SquareReduction.p)
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u.basis q=b0 q :=
    eu.2.2 q (accReg_away L hn q hq)
  have workNd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
      List.count_append,List.count_cons,List.count_nil] at h
    omega
  have workU : regValue L.core.work u.basis=A := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using eu.2.1
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A<SquareReduction.p := lt_of_lt_of_le hA (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := L.measuredCore.program_correct 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A O hAp hO u ((m.drop mb).take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (L.measuredCore.program SquareReduction.c SquareReduction.p) ((m.drop mb).take mk) u
  change v.phase=u.phase ∧ regValue L.core.out v.basis=(A+O)%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u.basis q at ek
  let base2 : BasisState := fun q => if q∈L.core.out then v.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have frame2 : SquareFrame (accReg L) base2 A v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans eu.2.1
    · intro q hq
      by_cases ho : q∈L.core.out
      · simp [base2,ho]
      · rw [b2off q ho,ek.2.2 q ho]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v ((m.drop mb).drop mk) frame2
  refine ⟨eo.1.trans (ek.1.trans eu.1),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) ((m.drop mb).drop mk) v).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq

def accPrice (a : AccItem) : Nat := 4*Acc.sbuildT 33 a.pre+2*Acc.sbuildT 163 a.terms+1023+
  (if a.pre=[] then 0 else 4*127)

theorem accFold_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    toffoliCount (accFold L a)=accPrice a ∧ measurementCount (accFold L a)=accPrice a := by
  have b := Acc.sbuild_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_counts (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := L.measuredCore.secp_program_counts (L.measuredCore_widths hw) SquareReduction.c SquareReduction.p
  have sp := split_counts L hw a
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,accPrice,toffoliCount_append,measurementCount_append,
    sp.1.1,sp.1.2,sp.2.1,sp.2.2]
  split <;> omega

theorem accFold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFold L a)⊆(control::L.wires).toFinset := by
  have fits (f : MeasuredSquareFold) (hf : f∈a.terms) := fits_of L hw hn f (cnt f hf) (ok f hf)
  have fitsP (f : MeasuredSquareFold) (hf : f∈a.pre) := fitsPre_of L hw hn f (cntP f hf) (okP f hf)
  have inW (q : Wire) (hq : q∈L.core.work∨q∈L.foldPad∨q∈L.core.product∨q=L.core.cin) :
      q∈(control::L.wires).toFinset := by
    simp only [List.mem_toFinset,List.mem_cons,CuccaroStreamedSquareWideLayout.wires,
      CuccaroStreamedSquareLayout.wires,foldPad,List.mem_append] at hq ⊢
    tauto
  have srcIn (f : MeasuredSquareFold) (h : SrcOK L f) (q : Wire) (hq : q∈f.src) :
      q∈L.core.product ∨ q∈wTemp L := by
    have pos := List.count_pos_iff.mpr hq
    have bound := h q
    have mem : q∈L.core.product++wTemp L := List.count_pos_iff.mp (by omega)
    simpa using mem
  have zIn (q : Wire) (hq : q∈accZ L) : q∈(control::L.wires).toFinset := by
    rcases accZ_mem L q hq with h|h
    · exact inW q (Or.inr (Or.inl h))
    · exact inW q (Or.inl (List.mem_of_mem_drop h))
  have b := Acc.sbuild_support (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms fits
    (control::L.wires).toFinset (by
      intro f hf q hq
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      rcases hq with h|(((h|h)|h)|h)
      · exact inW q (Or.inr (Or.inr (Or.inr h)))
      · rcases srcIn f (cnt f hf) q h with h'|h'
        · exact inW q (Or.inr (Or.inr (Or.inl h')))
        · exact inW q (Or.inl (wTemp_work L q h'))
      · exact inW q (Or.inl (accReg_work L q h))
      · exact zIn q h
      · exact inW q (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have w := Acc.sbuild_support (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre fitsP
    (control::L.wires).toFinset (by
      intro f hf q hq
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      rcases hq with h|(((h|h)|h)|h)
      · exact inW q (Or.inr (Or.inr (Or.inr h)))
      · have pos := List.count_pos_iff.mpr h
        have bound := cntP f hf q
        exact inW q (Or.inr (Or.inr (Or.inl (List.count_pos_iff.mp (by omega)))))
      · exact inW q (Or.inl (wTemp_work L q h))
      · exact zIn q h
      · exact inW q (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have k : ECDSAAdd.wires (L.measuredCore.program SquareReduction.c SquareReduction.p)⊆
      (control::L.wires).toFinset := (L.measured_small_support control).2.2.2
  have sp := split_support L hw control a
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨w.1,⟨⟨sp.1,b.1⟩,sp.2⟩⟩,w.2⟩,k⟩,⟨⟨w.1,⟨⟨sp.1,b.2⟩,sp.2⟩⟩,w.2⟩⟩

theorem accFold_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFold L a) := by
  have b := Acc.sbuild_physical (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fits_of L hw hn f (cnt f hf) (ok f hf))
  have w := Acc.sbuild_physical (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsPre_of L hw hn f (cntP f hf) (okP f hf))
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have sp := split_physical L hn a
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,gatePhysical_append]
  exact ⟨⟨⟨⟨w.1,⟨⟨sp.1,b.1⟩,sp.2⟩⟩,w.2⟩,L.measuredCore.physical _ _ coreNd⟩,⟨⟨w.1,⟨⟨sp.1,b.2⟩,sp.2⟩⟩,w.2⟩⟩

theorem accFold_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFold L a)≤2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(66*256+37)+7000 := by
  have b := Acc.sbuild_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1 a.terms
    (fun f hf => fitsLen_of L hw f (ok f hf))
  have w := Acc.sbuild_gateSlots (wTemp L) (accZ L) (accBank L) L.core.cin 33 (acc_lengths L hw).2.2.2 a.pre
    (fun f hf => fitsLen33_of L hw f (okP f hf))
  have k := Baselines.canonicalMod_gateSlots_le L.measuredCore 256 SquareReduction.c SquareReduction.p
    (L.measuredCore_widths hw)
  have sp := split_gateSlots L hw a
  simp only [accFold,fillIn,fillOut,tempIn,tempOut,Challenge.gateSlots_append]
  omega

/-! Mixed fold schedules. -/

abbrev MixItem := MeasuredSquareFold ⊕ AccItem

def mixNeg : MixItem → Bool
  | .inl f => f.negative
  | .inr a => a.negative

def mixProg (L : CuccaroStreamedSquareWideLayout) : MixItem → Program
  | .inl f => L.measuredFold f
  | .inr a => accFold L a

def mixPayload (base : BasisState) : MixItem → Nat
  | .inl f => measuredFoldPayload base f
  | .inr a => Acc.accVal base 0 a.spec

def MixView (L : CuccaroStreamedSquareWideLayout) (base : BasisState) : MixItem → Prop
  | .inl f => L.MeasuredFoldView base f
  | .inr a => AccView L base a

def mixFolds (L : CuccaroStreamedSquareWideLayout) : Bool → List MixItem → Program
  | _,[] => []
  | o,i::is => (if o=mixNeg i then [] else L.reflectOutput)++mixProg L i++mixFolds L (mixNeg i) is

def mixValue (base : BasisState) : Bool → Nat → List MixItem → Nat
  | _,O,[] => O
  | o,O,i::is => mixValue base (mixNeg i)
      ((mixPayload base i+(if o=mixNeg i then O else SquareReduction.p-1-O))%SquareReduction.p) is

theorem mixValue_lt (base : BasisState) (o : Bool) (O : Nat) (items : List MixItem) (hO : O<SquareReduction.p) :
    mixValue base o O items<SquareReduction.p := by
  induction items generalizing o O with
  | nil => exact hO
  | cons i is ih =>
    apply ih
    exact Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])

theorem mixProg_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (i : MixItem) (hv : MixView L base i) (hc : L.PairClean base)
    (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (mixProg L i)
      (SquareFrame L.core.out base ((mixPayload base i+O)%SquareReduction.p)) := by
  cases i with
  | inl f => exact L.measuredFold_frame hw hn base f hv hc O hO
  | inr a => exact accFold_frame L hw hn base a hv hc O hO

theorem mixFolds_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (base : BasisState) (hc : L.PairClean base)
    (o : Bool) (O : Nat) (hO : O<SquareReduction.p) (items : List MixItem)
    (views : ∀i∈items,MixView L base i) :
    Triple (SquareFrame L.core.out base O) (mixFolds L o items)
      (SquareFrame L.core.out base (mixValue base o O items)) := by
  induction items generalizing o O with
  | nil => intro s m hf;exact ⟨rfl,hf⟩
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    have rb : R<SquareReduction.p := by
      dsimp [R]
      split
      · exact hO
      · omega
    have prep : Triple (SquareFrame L.core.out base O)
        (if o=mixNeg i then [] else L.reflectOutput) (SquareFrame L.core.out base R) := by
      by_cases same : o=mixNeg i
      · simp only [same,if_true,R]
        intro s m hf;exact ⟨rfl,hf⟩
      · simpa only [same,if_false,R] using L.measuredReflection_frame hw hn base hc O hO
    have fold := mixProg_frame L hw hn base i (views i (by simp)) hc R rb
    have ob : (mixPayload base i+R)%SquareReduction.p<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have tail := ih (mixNeg i) _ ob (by intro j hj;exact views j (by simp [hj]))
    exact (prep.seq fold).seq tail

def mixFinal : Bool → List MixItem → Bool
  | o,[] => o
  | _,i::is => mixFinal (mixNeg i) is

def mixSignedPayload (base : BasisState) (i : MixItem) : ZMod SquareReduction.p :=
  if mixNeg i then -(mixPayload base i : ZMod SquareReduction.p) else mixPayload base i

def mixSignedSum (base : BasisState) : List MixItem → ZMod SquareReduction.p
  | [] => 0
  | i::is => mixSignedPayload base i+mixSignedSum base is

theorem mixValue_cast (base : BasisState) (o : Bool) (O : Nat)
    (items : List MixItem) (hO : O<SquareReduction.p) :
    measuredOrientationCast (mixFinal o items) (mixValue base o O items)=
        measuredOrientationCast o O+mixSignedSum base items := by
  induction items generalizing o O with
  | nil => simp [mixFinal,mixValue,mixSignedSum]
  | cons i is ih =>
    let R := if o=mixNeg i then O else SquareReduction.p-1-O
    let V := (mixPayload base i+R)%SquareReduction.p
    have vb : V<SquareReduction.p :=
      Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
    have same : measuredOrientationCast (mixNeg i) R=measuredOrientationCast o O := by
      cases o <;> cases h : mixNeg i <;>
        simp [R,measuredOrientationCast,h,measuredReflection_zmod O hO]
    have step : measuredOrientationCast (mixNeg i) V=
        measuredOrientationCast (mixNeg i) R+mixSignedPayload base i := by
      cases h : mixNeg i <;>
        simp [V,measuredOrientationCast,mixSignedPayload,h,ZMod.natCast_mod,Nat.cast_add] <;> ring
    have tail := ih (mixNeg i) V vb
    rw [step,same] at tail
    simpa only [mixFinal,mixValue,mixSignedSum,R,V,add_assoc] using tail

/-- Producer/fold/cleanup contract with a mixed fold schedule. -/
theorem withMixed_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta) :
    (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (L.withMeasuredSquare control src dst (mixFolds L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  apply L.withMeasuredSquare_correct hw control hn src dst hs hd hs2 hsmax hlen
    (mixFolds L orientation items) s records hc hzero V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := mixFolds_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩

def mixFoldsT : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then 0 else 255)+
      (match i with
        | .inl f => 1023+(if f.canonical then 0 else 1022)
        | .inr a => accPrice a)+mixFoldsT (mixNeg i) is

def mixFoldsM : Bool → List MixItem → Nat
  | _,[] => 0
  | o,i::is => (if o=mixNeg i then 0 else 255)+
      (match i with
        | .inl f => 1023+(if f.canonical then 0 else 1020)
        | .inr a => accPrice a)+mixFoldsM (mixNeg i) is

def MixStatic (L : CuccaroStreamedSquareWideLayout) : MixItem → Prop
  | .inl f => ∀q,f.src.count q≤L.core.product.count q
  | .inr a => (∀f∈a.terms,SrcOK L f) ∧ (∀f∈a.terms,TermOK f) ∧
      (∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) ∧ (∀f∈a.pre,TermOK33 f)

theorem mixFolds_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    toffoliCount (mixFolds L o items)=mixFoldsT o items ∧
    measurementCount (mixFolds L o items)=mixFoldsM o items := by
  induction items generalizing o with
  | nil => simp [mixFolds,mixFoldsT,mixFoldsM,toffoliCount,measurementCount]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect := (L.measured_small_operation_counts hw).2.2
    have hi := hst i (by simp)
    cases i with
    | inl f =>
      have op := L.measuredFold_counts hw f
      by_cases same : o=mixNeg (.inl f) <;>
        simp only [mixFolds,mixFoldsT,mixFoldsM,same,if_true,if_false,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2] <;>
        simp [toffoliCount,measurementCount] <;> omega
    | inr a =>
      have op := accFold_counts L hw a hi.2.1 hi.2.2.2
      by_cases same : o=mixNeg (.inr a) <;>
        simp only [mixFolds,mixFoldsT,mixFoldsM,same,if_true,if_false,mixProg,toffoliCount_append,
          measurementCount_append,op.1,op.2,reflect.1,reflect.2,t.1,t.2] <;>
        simp [toffoliCount,measurementCount] <;> omega

theorem mixFolds_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    ECDSAAdd.wires (mixFolds L o items)⊆(control::L.wires).toFinset := by
  induction items generalizing o with
  | nil => simp [mixFolds,ECDSAAdd.wires]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have reflect : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
      (L.measured_small_support control).2.2.1
    have hi := hst i (by simp)
    have mem (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) :
        ∀q∈f.src,q∈L.core.product := by
      intro q hq
      have pos := List.count_pos_iff.mpr hq
      have b := h q
      exact List.count_pos_iff.mp (by omega)
    have hprog : ECDSAAdd.wires (mixProg L i)⊆(control::L.wires).toFinset := by
      cases i with
      | inl f => exact L.measuredFold_support control f (mem f hi)
      | inr a => exact accFold_support L hw hn control a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    by_cases same : o=mixNeg i <;>
      simp only [mixFolds,same,if_false,if_true,wires_append,ECDSAAdd.wires,Finset.union_subset_iff,
        Finset.empty_subset] <;> tauto

theorem mixFolds_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) :
    GatePhysical (mixFolds L o items) := by
  induction items generalizing o with
  | nil => simp [mixFolds,GatePhysical]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj]))
    have hi := hst i (by simp)
    have hprog : GatePhysical (mixProg L i) := by
      cases i with
      | inl f => exact L.measuredFold_physical hw hn f hi
      | inr a => exact accFold_physical L hw hn a hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    have hr := L.reflectOutput_physical hn
    simp only [mixFolds,gatePhysical_append]
    refine ⟨⟨?_,hprog⟩,t⟩
    split
    · simp [GatePhysical]
    · exact hr

theorem mixFolds_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (o : Bool) (items : List MixItem) (hst : ∀i∈items,MixStatic L i) (B : Nat)
    (hB : ∀i∈items,∀a,i=.inr a → a.terms.length≤B ∧ a.pre.length≤4) :
    Challenge.gateSlots (mixFolds L o items)≤ items.length*(41000+2*(B*(14*163))+(66*256+37)) := by
  induction items generalizing o with
  | nil => simp [mixFolds,Challenge.gateSlots]
  | cons i is ih =>
    have t := ih (mixNeg i) (fun j hj => hst j (by simp [hj])) (fun j hj a e => hB j (by simp [hj]) a e)
    have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
    have hi := hst i (by simp)
    have hprog : Challenge.gateSlots (mixProg L i)≤36000+2*(B*(14*163))+(66*256+37) := by
      cases i with
      | inl f => have := Baselines.measuredFold_gateSlots_le L hw f; simp only [mixProg]; omega
      | inr a =>
        have h1 := accFold_gateSlots L hw a hi.2.1 hi.2.2.2
        have h2 := hB (.inr a) (by simp) a rfl
        have h3 : a.terms.length*(14*163)≤B*(14*163) := Nat.mul_le_mul_right _ h2.1
        have h4 : a.pre.length*(14*33)≤4*(14*33) := Nat.mul_le_mul_right _ h2.2
        simp only [mixProg]; omega
    simp only [mixFolds,Challenge.gateSlots_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · simp only [Baselines.gateSlots_nil]; omega
    · omega

end ECDSAAdd.Entrant

end

section
-- ===== RotCert =====

set_option maxRecDepth 100000

/-! Rotated 128-bit squares stay canonical.

For a square `P < 2^256` and `N2 = 2^(256-j)`, the left rotation by `j` of `P` is
`P / N2 + 2^j * (P % N2)`.  It can reach `p` only when the top part `h = P / N2`
and the low part force `P` into the interval `[rotLo h, rotHi h]`.  For each
`h < 2^j` a certificate `r` with `r*r < rotLo h` and `rotHi h < (r+1)*(r+1)`
shows that interval contains no square.  `certOK` checks the whole certificate
list by kernel evaluation of natural-number arithmetic. -/
namespace ECDSAAdd.Entrant
open Arithmetic

def rotLo (B N2 h : Nat) : Nat := h*N2 + (SquareReduction.p - h + B - 1)/B
def rotHi (N2 h : Nat) : Nat := h*N2 + N2 - 1

def certOK (B N2 : Nat) : Nat → List Nat → Bool
  | h, [] => h == B
  | h, r :: rs =>
      (decide (r*r < rotLo B N2 h) && decide (rotHi N2 h < (r+1)*(r+1))) && certOK B N2 (h+1) rs

theorem certOK_spec (B N2 : Nat) : ∀ (h0 : Nat) (rs : List Nat), certOK B N2 h0 rs = true →
    ∀ h, h0 ≤ h → h < B → ∃ r, r*r < rotLo B N2 h ∧ rotHi N2 h < (r+1)*(r+1) := by
  intro h0 rs
  induction rs generalizing h0 with
  | nil =>
    intro hc h hh hb
    simp only [certOK, beq_iff_eq] at hc
    omega
  | cons r rs ih =>
    intro hc h hh hb
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases e : h = h0
    · subst e; exact ⟨r, hc.1.1, hc.1.2⟩
    · exact ih (h0+1) hc.2 h (by omega) hb

/-- A square below `2^256` rotated with a valid certificate list stays below `p`. -/
theorem rot_lt_p (B N2 : Nat) (hB : 0 < B) (hN : 0 < N2) (hBN : B*N2 = 2^256)
    (cert : List Nat) (hc : certOK B N2 0 cert = true) (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / N2 + B * ((Y*Y) % N2) < SquareReduction.p := by
  by_contra hge
  push_neg at hge
  have hdiv : N2 * ((Y*Y) / N2) + (Y*Y) % N2 = Y*Y := Nat.div_add_mod (Y*Y) N2
  have hhB : (Y*Y) / N2 < B := by
    rw [Nat.div_lt_iff_lt_mul hN]; rw [hBN]; exact hb
  obtain ⟨r, hr1, hr2⟩ := certOK_spec B N2 0 cert hc ((Y*Y) / N2) (Nat.zero_le _) hhB
  generalize hh : (Y*Y) / N2 = h at hdiv hhB hr1 hr2 hge
  generalize hL : (Y*Y) % N2 = L at hdiv hge
  have hLlt : L < N2 := by rw [← hL]; exact Nat.mod_lt _ hN
  have hlo : rotLo B N2 h ≤ Y*Y := by
    unfold rotLo
    have hq : (SquareReduction.p - h + B - 1)/B ≤ L := by
      apply Nat.lt_succ_iff.mp
      rw [Nat.div_lt_iff_lt_mul hB, Nat.succ_mul]
      have e : B * L = L * B := Nat.mul_comm B L
      omega
    have e2 : h * N2 = N2 * h := Nat.mul_comm h N2
    omega
  have hhi : Y*Y ≤ rotHi N2 h := by
    unfold rotHi
    have e2 : h * N2 = N2 * h := Nat.mul_comm h N2
    omega
  have a := Nat.mul_self_lt_mul_self_iff.mp (lt_of_lt_of_le hr1 hlo)
  have b := Nat.mul_self_lt_mul_self_iff.mp (lt_of_le_of_lt hhi hr2)
  omega

/-- Certificates for the rotation by 4: `r_h = isqrt (rotHi h)` for `h < 2^4`. -/
def rotCert4 : List Nat := [
  85070591730234615865843651857942052863, 120307984584002255772516886238812528463, 147346587106715120692043727842883538658, 170141183460469231731687303715884105727,
  190223625994936052448711836799948219418, 208379541855705147060497221923602346553, 225075629603308753018814965684675446837, 240615969168004511545033772477625056927,
  255211775190703847597530955573826158591, 269016831765825801719526439316123156306, 282147233462699194961827797147224560430, 294693174213430241384087455685767077316,
  306726380517423719006373237817322128119, 318305007944662521603433860153578694457, 329476985023209069078162071863942203380, 340282366920938463463374607431768211455]

theorem rotCert4_ok : certOK (2^4) (2^252) 0 rotCert4 = true := by decide +kernel

theorem rot4_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^252 + 2^4 * ((Y*Y) % 2^252) < SquareReduction.p :=
  rot_lt_p (2^4) (2^252) (by positivity) (by positivity) (by norm_num) rotCert4 rotCert4_ok Y hb

/-- Certificates for the rotation by 6: `r_h = isqrt (rotHi h)` for `h < 2^6`. -/
def rotCert6 : List Nat := [
  42535295865117307932921825928971026431, 60153992292001127886258443119406264231, 73673293553357560346021863921441769329, 85070591730234615865843651857942052863,
  95111812997468026224355918399974109709, 104189770927852573530248610961801173276, 112537814801654376509407482842337723418, 120307984584002255772516886238812528463,
  127605887595351923798765477786913079295, 134508415882912900859763219658061578153, 141073616731349597480913898573612280215, 147346587106715120692043727842883538658,
  153363190258711859503186618908661064059, 159152503972331260801716930076789347228, 164738492511604534539081035931971101690, 170141183460469231731687303715884105727,
  175377517668776787853951800790642601648, 180461976876003383658775329358218792695, 185407056209649813630662448518363628108, 190223625994936052448711836799948219418,
  194921213009242215272059206077382237867, 199508222074498579239763080511020768050, 203992112763362759702255349553060103316, 208379541855705147060497221923602346553,
  212676479325586539664609129644855132159, 216888303632675647313601872656300690638, 221019880660072681038065591764325307987, 225075629603308753018814965684675446837,
  229059578353883514371252488813878024045, 232975410354809691028999546292736078212, 236826504480231334090187096672132418653, 240615969168004511545033772477625056927,
  244346671786196349790200515401475186231, 248021264022511240847206814133050500226, 251642203935781198228857763314028473402, 255211775190703847597530955573826158591,
  258732103903484357453253474976449672980, 262205173451357536391972035370709648437, 265632837538941251634075828277143597658, 269016831765825801719526439316123156306,
  272358783900309864218087857043330409306, 275660223031885311660837236230928240409, 278922587748503829917427540838876006752, 282147233462699194961827797147224560430,
  285335438992404078673067755199922329127, 288488412487089358763283015427614820925, 291607296777110982179066369266086494232, 294693174213430241384087455685767077316,
  297747071055821155530452781502797185023, 300769961460005639431292215597031321158, 303762771107629881702280654470904942690, 306726380517423719006373237817322128119,
  309661628071113251284217280308471805592, 312569312783557720590745832885403519830, 315450196843049386996416775608544988928, 318305007944662521603433860153578694457,
  321134441436892185223825193844146861358, 323939162299524695956483584526126981093, 326719806968679001232275300715203276489, 329476985023209069078162071863942203380,
  332211280745126111021694046270932974510, 334923254565355709814280786110416129476, 337613444404963129528222448527013170255, 340282366920938463463374607431768211455]

theorem rotCert6_ok : certOK (2^6) (2^250) 0 rotCert6 = true := by decide +kernel

theorem rot6_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^250 + 2^6 * ((Y*Y) % 2^250) < SquareReduction.p :=
  rot_lt_p (2^6) (2^250) (by positivity) (by positivity) (by norm_num) rotCert6 rotCert6_ok Y hb

/-- Certificates for the rotation by 10: `r_h = isqrt (rotHi h)` for `h < 2^10`. -/
def rotCert10 : List Nat := [
  10633823966279326983230456482242756607, 15038498073000281971564610779851566057, 18418323388339390086505465980360442332, 21267647932558653966460912964485513215,
  23777953249367006556088979599993527427, 26047442731963143382562152740450293319, 28134453700413594127351870710584430854, 30076996146000563943129221559703132115,
  31901471898837980949691369446728269823, 33627103970728225214940804914515394538, 35268404182837399370228474643403070053, 36836646776678780173010931960720884664,
  38340797564677964875796654727165266014, 39788125993082815200429232519197336807, 41184623127901133634770258982992775422, 42535295865117307932921825928971026431,
  43844379417194196963487950197660650412, 45115494219000845914693832339554698173, 46351764052412453407665612129590907027, 47555906498734013112177959199987054854,
  48730303252310553818014801519345559466, 49877055518624644809940770127755192012, 50998028190840689925563837388265025829, 52094885463926286765124305480900586638,
  53169119831396634916152282411213783039, 54222075908168911828400468164075172659, 55254970165018170259516397941081326996, 56268907400827188254703741421168861709,
  57264894588470878592813122203469506011, 58243852588702422757249886573184019553, 59206626120057833522546774168033104663, 60153992292001127886258443119406264231,
  61086667946549087447550128850368796557, 62005316005627810211801703533262625056, 62910550983945299557214440828507118350, 63802943797675961899382738893456539647,
  64683025975871089363313368744112418245, 65551293362839384097993008842677412109, 66408209384735312908518957069285899414, 67254207941456450429881609829030789076,
  68089695975077466054521964260832602326, 68915055757971327915209309057732060102, 69730646937125957479356885209719001688, 70536808365674798740456949286806140107,
  71333859748101019668266938799980582281, 72122103121772339690820753856903705231, 72901824194277745544766592316521623558, 73673293553357560346021863921441769329,
  74436767763955288882613195375699296255, 75192490365001409857823053899257830289, 75940692776907470425570163617726235672, 76681595129355929751593309454330532029,
  77415407017778312821054320077117951398, 78142328195889430147686458221350879957, 78862549210762346749104193902136247232, 79576251986165630400858465038394673614,
  80283610359223046305956298461036715339, 80984790574881173989120896131531745273, 81679951742169750308068825178800819122, 82369246255802267269540517965985550845,
  83052820186281527755423511567733243627, 83730813641338927453570196527604032369, 84403361101240782382055612131753292563, 85070591730234615865843651857942052863,
  85732629666178319151235667203935475380, 86389594290191543925699642002929328613, 87041600477988179082073860895186456611, 87688758834388393926975900395321300824,
  88331175912365987246451476950740602474, 88968954417859501989461455287242856883, 89602193401461877347437606131173517257, 90230988438001691829387664679109396347,
  90855431794937894003754770589036446577, 91475612590408096074420234834267234969, 92091616941696950432527329901802211661, 92703528104824906815331224259181814054,
  93311426605897940135831683800530642542, 93915390364804929416771759117077744496, 94515494811800626632459302190721262802, 95111812997468026224355918399974109709,
  95704415696513942849074108340184809471, 96293371505815294937613268783965082473, 96878746937100593150684230783613621955, 97460606504621107636029603038691118933,
  98039012808138836098454154115084970993, 98614026611533449491522177570809842251, 99185706917307616410304814283328547768, 99754111037249289619881540255510384025,
  100319294659490489966858998267591051868, 100881311912184675644822414743546183615, 101440215424008787617956412390675090648, 101996056381681379851127674776530051658,
  102548884584674754665468704570670082983, 103098748497286620199690180208776580996, 103645695298225370744670471111804453001, 104189770927852573530248610961801173276,
  104731020133216547973592075349842287743, 105269486511001973800952275458960962405, 105805212548512198110685423930209210161, 106338239662793269832304564822427566079,
  106868608238001660177802843644280841454, 107396357661111081572589580048653690706, 107921526356047751649856654500879263045, 108444151816337823656800936328150345319,
  108964270636345484119997243339852359991, 109481918541175370160314093953336572724, 109997130415308452668289210942862264587, 110509940330036340519032795882162653993,
  111020381569755060372888895709465855331, 111528486657175733777944718709129052661, 112034287377506187614015090569593809066, 112537814801654376509407482842337723418,
  113039099308501549434559813334360681802, 113538170606290341393787483530978863730, 114035057753170400478106559148369887933, 114529789176941757185626244406939012022,
  115022392694033894627389964181495798044, 115512895527756373773189013518293919470, 116001324325854896914473924118812815030, 116487705177404845514499773146368039106,
  116972063629072596815535021304670322687, 117454424700773298902317934109332799149, 117934812900752258930658599587897845119, 118413252240115667045093548336066209326,
  118889766246835032780444897999967637136, 119364377979248445601287697557592010421, 119837110039080581254528544016317791164, 120307984584002255772516886238812528463,
  120777023339749274618277909377214560099, 121244247611819331303241716078434769919, 121709678296764773838104457293229142782, 122173335893098174895100257700737593115,
  122635240511826809126994597088091329274, 123095411886631355511665657422101680279, 123553869383703400904310776948978326267, 124010632011255620423603407066525250113,
  124465718428717848307384363577127638186, 124919146955631627059185454609077069589, 125370935580255230844680553925818150011, 125821101967890599114428881657014236701,
  126269663468943086393808061284496995255, 126716637126724432290583619053040885394, 127162039685008880343249185307917680376, 127605887595351923798765477786913079295,
  128048197024180729299719437429595255261, 128488983859664884407259330412768868952, 128928263718375730605538261862523096326, 129366051951742178726626737488224836490,
  129802363652310557479594040856350627018, 130237213659815716912810763702251466596, 130670616567070296200043421448225912051, 131102586725678768195986017685354824218,
  131533138251582590890463850592981951236, 131962285030442527391239976987954583436, 132390040722863940621719105743186974597, 132816418769470625817037914138571798829,
  133241432395832512468680145077534976981, 133665094617252346973046846784762584290, 134087418243416257290404984359872233197, 134508415882912900859763219658061578153,
  134928099947625706317969462287557034034, 135346482657002537744081497018664094521, 135763576042206936728123359168803558127, 136179391950154932109043928521665204653,
  136593942047441249327693278923280732090, 137007237824158600608285946571145645724, 137419290597613593249696883352861744490, 137830111515942655830418618115464120204,
  138239711561631250781995934269155835903, 138648101554939516257450976930543233054, 139055292157237360222996836388772721081, 139461293874251914958713770419438003376,
  139866117059230150407471665245893249237, 140269771916019339816089704927116173812, 140672268502067970636759353552922154273, 141073616731349597480913898573612280215,
  141473826377212041834617060485007628099, 141872907075154255057890521250674255714, 142270868325533076714392689771781663904, 142667719496202039336533877599961164563,
  143063469825084293157776103670948134087, 143458128422681649980566008983331351047, 143851704274521674045367689242075150054, 144244206243544679381641507713807410462,
  144635643072432427520717648595969320706, 145026023385880256505606587198529767136, 145415355692814311722655540610392645118, 145803648388555491089533184633043247116,
  146190909756931661454044404558036678400, 146577147972339649584967373713505100983, 146962371101758459770873744661281035206, 147346587106715120692043727842883538658,
  147729803845204516805055969314155218447, 148112029073564513894730603091853074022, 148493270448307644623287670146908451855, 148873535527910577765226390751398592511,
  149252831774562554285617082827417880885, 149631166555873934429822310383265576037, 150008547146545962478048526964414245861, 150384980730002819715646107798515660579,
  150760474399987001419781745130253503955, 151135035162119020207889895868414091270, 151508669935422405878739267750029449377, 151881385553814940851140327235452471345,
  152253188767567040418798001367545769278, 152624086244728158245397527922330370843, 152994084572522069776691512164795077487, 153363190258711859503186618908661064059,
  153731409732935412227022094338387510395, 154098749348012183630663472987059069213, 154465215381222001475745315995122939981, 154830814035556625642108640154235902796,
  155195551440944772915710769210258249202, 155559433655451290917074915686132123294, 155922466666451144798175027604503451164, 156284656391778860295372916442701759915,
  156646008680854047380800798496888326984, 157006529315783610077218121091526916869, 157366224012441229965855676778993695220, 157725098421524693498208387804272494464,
  158083158129591616397339977260678597465, 158440408660074102179229652459741451948, 158796855474272856118208637948402379872, 159152503972331260801716930076789347228,
  159507359494189904748456847233641349119, 159861427320522041381372243222448754666, 160214712673650441934387486750896987835, 160567220718446092611912596922073430679,
  160918956563209173495906333934164636517, 161269925260532744290632082712656673156, 161620131808149549994653126145600496811, 161969581149762347978241792263063490546,
  162318278175858146707975932838304305087, 162666227724506735485201404492225517978, 163013434582143874038140023266547641340, 163359903484339500616137650357601638244,
  163705639116551307366801363642574286123, 164050646114864022220976331694954710308, 164394929066714727255532510186441302089, 164738492511604534539081035931971101690,
  165081340941796931780755232359436415351, 165423478803003101687210718578367226637, 165764910495054510778549193823243980990, 166105640372563055510847023135466487255,
  166445672745569045892622857199954691990, 166785011880177299356497202105288763286, 167123661999181610447394627848342152402, 167461627282677854907140393055208064738,
  167798911868665979964729461872834748616, 168135519853641126074704024572576972691, 168471455293174118976045606701009670572, 168806722202481564764111224263506585127,
  169141324556985774672012145136831997849, 169475266292864740439281352063224509948, 169808551307592375498764917165894767142, 170141183460469231731687303715884105727,
  170473166573143896220277130060632893550, 170804504430125267261897446203023907131, 171135200779285903893197364907035423989, 171465259332356638302471334407870950760,
  171794683765412635778439366610408518034, 172123477719351082249479404134277321767, 172451644800360675004550415995933420682, 172779188580383087851399284005858657226,
  173106112597566577755056132167968603481, 173432420356711895906147996930703269668, 173758115329710662190396882846780948878, 174083200955976358164147721790372913222,
  174407680642868089882356868641908474071, 174731557766107268271749659719552058659, 175054835670187351189533342962056088341, 175377517668776787853951800790642601648,
  175699607045115302974024248587369552565, 176021107052403654639061444925175345579, 176342020914186996851142373217015350269, 176662351824731974492902953901481204949,
  176982102949397675516072104900894219042, 177301277425000562210616653522122601413, 177619878360173500567640322504099313989, 177937908835719003978922910574485713766,
  178255371904956804819864877068926108790, 178572270594065864838379165833633658937, 178888607902420932717781028185394352110, 179204386802923754694875212262347034515,
  179519610242329041693205499849301990627, 179834281141565294073858879462976907436, 180148402396050582810415227411166149800, 180461976876003383658775329358218792695,
  180775007426748558714917760198126862335, 181087496869018577632418953276365366954, 181399447999250068705167091403963766956, 181710863589875788007509541178072893154,
  182021746389612092822547729710178859200, 182332099123742003677935069183152053234, 182641924494393937445893560097330630017, 182951225180816192148840469668534469938,
  183260003839647262342650386551106389673, 183568263105182062224855784903013184980, 183876005589634131933738639342754331830, 184183233883393900865054659803604423322,
  184489950555283080234867383993516756557, 184796158152805255558496318868441406989, 185101859202392748195782519429384141369, 185407056209649813630662448518363628108,
  185711751659592242707366537550895861432, 186015948016883430635405110599787875170, 186319647726066977199885350562139132596, 186622853211795880271663367601061285084,
  186925566879058383402449213246101815028, 187227791113400537012352350565439315521, 187529528281145531430610606590410107749, 187830780729609858833543518234155488993,
  188131550787316359936293420512261256141, 188431840764204210135871601597528025399, 188731652951835898671643322485521355052, 189030989623601253264918604381442525604,
  189329853034918561621041964653587477329, 189628245423432840124591936816009773028, 189926169009211299030329395380320858152, 190223625994936052448711836799948219418,
  190520618566094120444477853450631571996, 190817148891164769609380044560698103806, 191113219121804237535001840071236674701, 191408831393027885698148216680369618943,
  191703987823389824378983273635826330074, 191998690515160052360346936501454397142, 192292941554499153304982576244453063910, 192586743011630589875226537567930164947,
  192880096941010635846543998503935458890, 193173005381495985671652351559434670314, 193465470356509080175376644752794525193, 193757493874201186301368461567227243911,
  194049077927613268089940106232337254735, 194340224494834685341083072846699845463, 194630935539159755707828912811322673478, 194921213009242215272059206077382237867,
  195211058839247611977278475398813455214, 195500474949003665630339940138070358753, 195789463244148627536280311081574976168, 196078025616277672196908308230169941987,
  196366163943087352884244444614426889125, 196653880088518152293979026528032236328, 196941175902895158891463094974091015982, 197228053223066898983044355141619684503,
  197514513872542353978487265211959055724, 197800559661626191755462435876167666086, 198086192387552240494352912252222954458, 198371413834615232820609628566657095536,
  198656225774300847572309225209019709781, 198940629965414076002146162595986684035, 199224628154205938725556871207857698244, 199508222074498579239763080511020768050,
  199791413447808759361978115084130249823, 200074203983469781468594372246347999629, 200356595378751861960619629910966598511, 200638589318980979933717996535182103736,
  200920187477656224593708228043454800206, 201201391516565664530053936271358893493, 201482203085900761540528973032487822945, 201762623824369351289644829487092367230,
  202042655359307212681378673162612375551, 202322299306788247433039518135803848506, 202601557271733290951560125783964865655, 202880430848017575235912824781350181296,
  203158921618576864159532755009841625182, 203437031155512281124411147832973042986, 203714761020193848723717914999721759080, 203992112763362759702255349553060103316,
  204269087925232398163565892782497806980, 204545688035588129638953742809756352816, 204821914613885878306873805195077862788, 205097769169349509330937409141340165966,
  205373253201067033971031577777625658685, 205648368198085654814600528058781930700, 205923115639505668173851294914963877112, 206197496994573240399380360417553161992,
  206471513722772074571338880821220324780, 206745167273913983745627927173196180307, 207018459088228386654612804277381788304, 207291390596450741489340942223608906003,
  207563963219909933123118167607690695555, 207836178370614628874423523517729885661, 208108037451338617650406362142637271817, 208379541855705147060497221923602346553,
  208650692968270272842864880474754220720, 208921492164605234704457543712744270625, 209191940811377872438070655629157005064, 209462040266433095947184150699684575487,
  209731791878872422581107504595979192823, 210001196989132594959163506878062337269, 210270256929063292243135509534303736950, 210538973022003947601904550917921924811,
  210807346582859684401021032347297911446, 211075378918176383442801553733640325664, 211343071326214893379328258545780467980, 211610425097024396221370847860418420323,
  211877441512514939670667580682287086417, 212144121846529147811110343814615809770, 212410467364913121506101435979716613664, 212676479325586539664609129644855132159,
  212942158978611972357170238263189138549, 213207507566263416585197492920295926731, 213472526323094065332375919152612068673, 213737216476003320355605687288561682908,
  214001579244303059004800816399941746845, 214265615839783165195816971642881610432, 214529327466776334498792295309869468772, 214792715322222163145179160097307381412,
  215055780595730530600659815536469083023, 215318524469644285197914443720676308350, 215580948119101242172786881826962047120, 215843052712095503299713309001758526090,
  216104839409538107177285970697959825657, 216366309365317019072462261570711115694, 216627463726356469092145212972658530630, 216888303632675647313601872656300690638,
  217148830217446764370399666359406347112, 217409044607052485858177211232486982236, 217668947921142748794575971654548432762, 217928541272690968239994486679704719982,
  218187825768049642060440620806514383058, 218446802507005361690603422331275755881, 218705472582833236634299776949564870674, 218963837082350740320628187906673145449,
  219221897085970984817439750988303252060, 219479653667755431789072735540647040229, 219737107895466046972651079863985664941, 219994260830616905336578421885724529174,
  220251113528525253976128765555582357638, 220507667038362039694204150123599608696, 220763922403201908110361211005882787847, 221019880660072681038065591764325307987,
  221275542840004318768779887996807578267, 221530909968077373801892063995158006525, 221785983063470942461612738357133905486, 222040763139510120745777791418931710663,
  222295251203712970656954543052511550007, 222549448257837003173333135689062887166, 222803355297925183925558282916779478329, 223056973314351467555889437418258105323,
  223310303291865866647839586127097888767, 223563346209639061027704836266938691852, 223816103041306553154129887177037185813, 224068574755012375228030181139187618132,
  224320762313452353572782386636243987764, 224572666673916935753573873424380263623, 224824288788333585825142549459171463978, 225075629603308753018814965684675446837,
  225326690060169419102737625059391808049, 225577471095004229573469161697773490869, 225827973638704213762635212563541860171, 226078198617003098869119626668721363605,
  226328146950517222855251883248047550676, 226577819554785051074628446497907516705, 226827217340306301429552972095434252851, 227076341212580682787574967061957727461,
  227325192072146251319227311424225635707, 227573770814617389352789043539206929208, 227822078330722411276710490853178707018, 228070115506340800956213118296739775866,
  228317883222540085067496705897694394685, 228565382355612346690932398903117173701, 228812613777110383443572936877822383272, 229059578353883514371252488813878024045,
  229306276948113039761459903209089679766, 229552710417347357980033098823453020272, 229798879614536743377521408059511783813, 230044785388067789254779928362991596089,
  230290428581797519821978670583941461218, 230535810035087175030713187184913020688, 230780930582835672105276417735176923797, 231025791055512747546378027036587838941,
  231270392279191783328662170608183570185, 231514735075582320962262349609183047260, 231758820262062267038328060647954535135, 232002648651709793828947848237625630060,
  232246221053334938463162960231353854194, 232489538271510904152801202755316589403, 232732601106605066894648180155822897876, 232975410354809691028999546292736078212,
  233217966808172356988890109053373632663, 233460271254626104529260801284625216669, 233702324478019294680990092027612559542, 233944127258145193631070042609340645375,
  234185680370771281687236835102521780700, 234426984587668290443059374664052639873, 234668040676638971217835882407386938195, 234908849401546597804635868218665598298,
  235149411522343206519442341248810497512, 235389727795097576504585634401607761768, 235629798972022953200505054786649334374, 235869625801504517861317199175795690238,
  236109209028126605951699869489373382489, 236348549392699677225207964553033056424, 236587647632287040247312581706408741696, 236826504480231334090187096672132418653,
  237065120666180769890544650203437668425, 237303496916115134926650885712198992228, 237541633952371561835984762279151499254, 237779532493670065560889795999935274272,
  238017193255138850575939314582643301265, 238254616948339390917623568178547347519, 238491804281291285504345310422552145025, 238728755958496891202575395115184020843,
  238965472680965736063362830785222387747, 239201955146238715122206556513020114370, 239438204048412071124571057744685750319, 239674220078161162509057088032635582328,
  239910003922764020950414604062224348448, 240145556266124700735200101064641494228, 240380877788796422213927536687545598901, 240615969168004511545033772477625056927,
  240850831077669138917868895383110146018, 241085464188427857414221989623407313082, 241319869167657944640597122202517574277, 241554046679498549236555818754429120198,
  241787997384872644337934598434403232474, 242021721941508790047622785493064468255, 242255221003962706940840516990091610477, 242488495223638662606483432156869539838,
  242721545248810673201092883546845490312, 242954371724643521967362688394595235819, 243186975293213596644799584121410578479, 243419356593529547676208914586458285564,
  243651516261552769090074007596727797334, 243883454930217703915631665580191080896, 244115173229451975964511736497096565299, 244346671786196349790200515401475186231,
  244577951224424520614300499091583401983, 244809012165162735986587621755167555333, 245039855226509250924206475536402457367, 245270481023653618253989194176182658548,
  245500890168895815860829766706848029395, 245731083271665212524287755020238019072, 245961060938539374005129002671191350511, 246190823773262711023331314844203360559,
  246420372376764970749185715298526243384, 246649707347179573409504279996519110050, 246878829279861795591599322503821490376, 247107738767406801808621553897956652535,
  247336436399667525871032526380080848475, 247564922763772403590435035904359616327, 247793198444142958323690118639371946403, 248021264022511240847206814133050500226,
  248249120077937125033497039923899925316, 248476767186825460784538852013889250601, 248704205922943085659183244488997746277, 248931436857435696614768727154255276372,
  249158460558844583266270534703199730882, 249385277593123224049703850638775960062, 249611888523653746660119322271657690993, 249838293911263254118370909218154139179,
  250064494314240017804897316522415192637, 250290490288349538783035543359940683230, 250516282386850478718875115553099293197, 250741871160510461689361107851636300022,
  250967257157621748155259898734446027679, 251192440924016782360710589582812097107, 251417423003083614406394068220107664894, 251642203935781198228857763314028473402,
  251866784260654566704234231860644343162, 252091164513849885080482908376542308605, 252315345229129383928363732628662223430, 252539326937886172787616122568993990511,
  252763110169158935671264078269627784912, 252986695449646509577595345659574977653, 253210083303722347146166836395259877691, 253433274253448864581167238106081770789,
  253656268818591675952618347771594583439, 253879067516633714973216553887987356175, 254101670862789245336102556900763081382, 254324079370017760686498370615835360753,
  254546293549037775287963449646638655584, 254768313908340506431994039545570271667, 254990140954203449627819186941325129145, 255211775190703847597530955573826158591,
  255433217119732054090122987666859236425, 255654467241004793516598383257476622985, 255875526052078317397042734451716309496, 256096394048361458599438874859190510523,
  256317071723128584339024350000205857656, 256537559567532448896158680525999049838, 256757858070616946999973109185469923489, 256977967719329768814518660825537737905,
  257197888998534957453707001611806426141, 257417622391025369941050790862963508850, 257637168377535042520054040062439575522, 257856527436751461211076523725046192652,
  258075700045327738500597651600725085181, 258294686677894697039032567155506353673, 258513487807072861213604769024266816643, 258732103903484357453253474976449672980,
  258950535435764724113148505305823780454, 259168782870574631777098926008787985839, 259386846672611514806972360844698226647, 259604727304621114959188081712701254037,
  259822425227408937879407071735523610273, 260039940899851623277714604212135592898, 260257274778908229577873898126556519873, 260474427319631433825621527404502933192,
  260691398975178647632474931662825545459, 260908190196823049923128080279083987301, 261124801433964537246221582685559369833, 261341233134140592400086842896451824103,
  261557485743037072116978775599928801699, 261773559704498914541326707635330350778, 261989455460540767229646977639594347427, 262205173451357536391972035370709648437,
  262420714115334858086958169580731366701, 262636077889059492075236019421518545676, 262851265207329639028063430186542954135, 263066276503165181780927701185963902472,
  263281112207817851314422563332615245256, 263495772750781318137493058000418624129, 263710258559801209740997627786168362537, 263924570060885054782479953975909166873,
  264138707678312154656072183610661003640, 264352671834643383094564998372653332900, 264566462950730914443877323555357286122, 264780081445727881243438211486373949194,
  264993527737097961739354430852221807424, 265206802240624897950678439604651782563, 265419905370421944902611619660153613168, 265632837538941251634075828277143597658,
  265845599156983174580761412056068915199, 266058190633705523928510789335701199090, 266270612376632743525722505595358691420, 266482864791665024937360290155069953963,
  266694948283087356217124092166729047629, 266906863253578505968384365861728570649, 267118610104219943258596040345479940739, 267330189234504693946093693569525168580,
  267541601042346133972423513470128845682, 267752845924086720167689745742695147512, 267963924274506659110782585296871553389, 268174836486832514580809968719744466394,
  268385582952745754130576583090156862104, 268596164062391235307538750455003108013, 268806580204385632042312818393520551772, 269016831765825801719526439316123156306,
  269226919132297093440575820981803530714, 269436842687881597982686857032176425375, 269646602815166339953573190136599845062, 269856199895251412635938924575114068068,
  270065634307758056011087104460955311518, 270274906430836678445966434590790579282, 270484016641174822523117280751280746452, 270692965314005075488162994037328189043,
  270901752823112924784733319190899535080, 271110379540844559142002340820375863297, 271318845838114615675373374935077103393, 271527152084413873456246718337607116255,
  271735298647816894002262527182444674430, 271943285894989609134919620706242846216, 272151114191196856647031019023199395431, 272358783900309864218087857043330409306,
  272566295384813682011264311767109339731, 272773649005814564381506688705731795737, 272980845123047301119909195603888845279, 273187884094882498655386557846561464180,
  273394766278333811630508878825172580792, 273601492029065125264266407956665079603, 273808061701397688910480545608480596042, 274014475648317201216571893142291291449,
  274220734221480847283435861414895734398, 274426837771224288223260704502801704907, 274632786646568603508251277524278290978, 274838581195227186499393766705723488980,
  275044221763612593540611552747348163121, 275249708696843346999919699413097743991, 275455042338750692635484770162390451077, 275660223031885311660837236230928240409,
  275865251117523987879865127023215223724, 276070126935676230258639272546694157880, 276274850825090851297581989705406634984, 276479423123262501563991868538311671807,
  276683844166438160741476926931056122854, 276888114289623585549426335876827931943, 277092233826589714882266691760965608546, 277296203109879032514901953861086466108,
  277500022470811887717426207368612421461, 277703692239492774118924894338906602795, 277907212744816567156942623066978977288, 278110584314474720445993672777545442162,
  278313807274961421395324413741414527560, 278516881951579706403004627634381357650, 278719808668447535950326709816406952601, 278922587748503829917427540838876006752,
  279125219513514463438017011341288414635, 279327704284078223608099360786057190822, 279530042379632727360608240078898067411, 279732234118460300814943330491786498474,
  279934279817693820407495051401591927626, 280136179793322516106373977549771373468, 280337934360197737010722678518061843015, 280539543832038679632179409854232347625,
  280741008521438079153285052894859843718, 280942328739867863954876550037052339471, 281143504797684773701791450243781847916, 281344537004135941273518707105844308546,
  281545425667364438823770204873271465843, 281746171094414788250315277351233233490, 281946773591238436353816385994457897849, 282147233462699194961827797147224560430,
  282347551012578646291570208963831335770, 282547726543581513822572495423177564900, 282747760357340998947776731784931922487, 282947652754424083669234120970015256198,
  283147404034336799602077036148276805084, 283347014495529463548035817997986841082, 283546484435401879897377906572163788406, 283745814150308510115781042501348511429,
  283945003935563609570311339484412244341, 284144054085446331946360712779266430091, 284342964893205801505106153763693721473, 284541736651066153428785379543563327808,
  284740369650231542498839173825878111072, 284938864180891120349749989409571831711, 285137220532223981539208825962352514423, 285335438992404078673067755199922329127,
  285533519848605106821383468732001275513, 285731463387005357459727604817179755100, 285929269892792542167832105715410437667, 286126939650168586315552207341896268174,
  286324472942354392964065611017347530057, 286521870051594577208183680144953226511, 286719131259162171183628892803030200723, 286916256845363299961132017966662702095,
  287113247089541828547222325020554428415, 287310102270083980209624343227646759124, 287506822664422926343235022827125798395, 287703408549043348090735378484150300109,
  287899860199485969929990587970314894118, 288096177890352065438511846278812750931, 288292361895307935443391812880949427958, 288488412487089358763283015427614820925,
  288684329937506015747164867672672734024, 288880114517445884812839806351895247421, 289075766496879612186312237582580729800, 289271286144864855041435297191938641412,
  289466673729550598237459663079412401366, 289661929518181444850385605779844294686, 289857053777101880692303922961314832411, 290052046771760513011213174397059534273,
  290246908766714283562119518284839297365, 290441640025632656238561252459574406280, 290636240811301779452052692350840865867, 290830711385628623445311081220785290236,
  291025052009645092723515639440496221678, 291219262943512113786249432865920097766, 291413344446523698341192292648430579320, 291607296777110982179066369266086494232,
  291801120192846239887784873678595989396, 291994814950446875582218972032579053771, 292188381305779389824477483234468619868, 292381819513863322908088809116073356801,
  292575129828875174677984235150989266136, 292768312504152301056706208176089650321, 292961367792196787445804260868012734329, 293154295944679299169934747427010201966,
  293347097212442909129748319678569379940, 293539771845506902828230948279310129756, 293732320093070560933760122556063018650, 293924742203516919541747489322562070413,
  294117038424416508295362462345254912981, 294309209002531066524468098411880741218, 294501254183817237560550643516235203893, 294693174213430241384087455685767077316,
  294884969335727525759474363449133542331, 295076639794272396011322776675390203528, 295268185831837623594638887100353268865, 295459607690409033610111938628310436894,
  295650905611189071414465673528509651801, 295842079834600348474566532712429526755, 296033130600289167612733870840165523316, 296224058147129027789461206183706148044,
  296414862713224108568533228731231731847, 296605544535912734408310807325972842270, 296796103851770818921755438666256768031, 296986540896615289246575340293816903711,
  297176855905507490665697580360768082811, 297367049112756571617104134618389497755, 297557120751922849230914442849985643304, 297747071055821155530452781502797185023,
  297936900256524164432905456657641113483, 298126608585365699684050333257697629919, 298316196272944023860429435678873846160, 298505663549125108571234165654835761770,
  298695010643045885991081972054804028594, 298884237783117481853782960211032936121, 299073345197028430036124834921529646727, 299262333111747868859644620766531152075,
  299451201753528719237305687149824352449, 299639951347910844790958615986747460388, 299828582119724194064434280974289124593, 300017094293091924956097053928828491723,
  300205488091433511493675212049805616059, 300393763737467833073184287684901649135, 300581921453216246282767177975664090850, 300769961460005639431292215597031321158,
  300957883978471469900576994802773155604, 301145689228560784439141451456568645291, 301333377429535222514438415127262763206, 301520948799974002839563490260507007911,
  301708403557776893189508587638069017388, 301895741920167163621094623643319936318, 302082964103694523209798741207171758402, 302270070324238040415779791736828182540,
  302457060797009047190502661923237053845, 302643935736554026934467244230638550845, 302830695356757486415661347283404761700, 303017339870844811757478535500058898755,
  303203869491385108603971690415531081503, 303390284430294026569450914415821822312, 303576584898836568078580167308738393976, 303762771107629881702280654470904942690,
  303948843266646040093910390409155885340, 304134801585214802629358462569323478416, 304320646272026362853869237172025271945, 304506377535134080837596002735091538556,
  304691995581957200541075259652670927586, 304877500619283552291011958542215995727, 305062892853272240465972389734820310944, 305248172489456316490795055844660741687,
  305433339732745437237750644251843982788, 305618394787428508931710082870302333089, 305803337857176316655814537896445445964, 305988169145044139553383024329590154974,
  306172888853474351821041977732314013584, 306357497184299009587316608583921829654, 306541994338742423770186059104533431574, 306726380517423719006373237817322128119,
  306910655920359378744415651383624552884, 307094820746965776592845519176619807181, 307278875196061694014095877206047123087, 307462819465870824454044188676775020790,
  307646653754024263996406113712010248949, 307830378257562988630499486388522379928, 308013993172940318220212139735131308841, 308197498696024367261326945974118138426,
  308380895022100482513683237985039941631, 308564182345873667593985587389270536132, 308747360861470994614408674131081478618, 308930430762444002951490631990245879962,
  309113392241771085229156734799915856554, 309296245491859860599070540626329742989, 309478990704549535400870577816428739401, 309661628071113251284217280308471805592,
  309844157782260420873947103244038846969, 310026580028139051059008517666313125283, 310208894998338053985237839514412264385, 310391102881889545831421538420516498404,
  310573203867271133447485741790270916979, 310755198142408188933053045705470101962, 310937085894676112234011413335413359005, 311118867310902581834149831372264246588,
  311300542577369793618330453690430923290, 311482111879816687983087137718907771390, 311663575403441165269965522224493275579, 311844933332902289596350055209006902329,
  312026185852322481157958607854784808824, 312207333145289697076625455886341627246, 312388375394859600866438424868770828906, 312569312783557720590745832885403519830,
  312750145493381595782003475305713606529, 312930873705802913195891235067382977740, 313111497601769631470592921666127519648, 313292017361708094761601596993776653969,
  313472433165525135421885890911633197587, 313652745192610165796730599110684736739, 313832953621837259202047146001107286189, 314013058631567220154436242183053833738,
  314193060399649643920776226049526863230, 314372959103424965454606109303232761517, 314552754919726497786072204142535591753, 314732448024882459931711353557987390441,
  314912038594717994389852174007095734683, 315091526804557174286928310577891167661, 315270912829225000239514457933199481482, 315450196843049386996416775608544988928,
  315629379019863139924674283812822012495, 315808459533005921402856826376882887216, 315987438555326207184578191959603703709, 316166316259183232794679954521357194931,
  316345092816448930020082491292675638667, 316523768398509853556844423291821901462, 316702343176269097874520362573820237420, 316880817320148204358459304919482903897,
  317059191000089058790242240085071327368, 317237464385555779226017527910472562484, 317415637645536594332056271790627630484, 317593710948545712236417275896804759745,
  317771684462625179955182164112984021892, 317949558355346733451295832321931608619, 318127332793813638383625567196950110194, 318305007944662521603433860153578694457,
  318482583974065193455045141074535543158, 318660061047730460937075319679662240348, 318837439330905931780185120159982264567, 319014718988379809496913694467282698239,
  319191900184482679458747869326509445021, 319368983083089286055184589834960440950, 319545967847620300989149636981646089436, 319722854641044082762744486444897509332,
  319899643625878427406905210815895041033, 320076334964192310508172576482941575693, 320252928817607620585390919648079502489, 320429425347300883868774973501793975671,
  320605824714004980533408530932842524362, 320782127078010852438866635086918277610, 320958332599169202426283864702982677025, 321134441436892185223825193844146861358,
  321310453750155090011152828093285550832, 321486369697498014693122323488948106593, 321662189437027531932584152712489696757, 321837913126418346991812667868329273034,
  322013540922914947431733093475947847571, 322189072983333244717768740145961072118, 322364509464062207780785032252602899436, 322539850521065488581264165425313346312,
  322715096309883039724504225818571445046, 322890246985632724174299387105963554473, 323065302703011917112223327471549576064, 323240263616299099989306252291200993622,
  323415129879355446816566843720562091226, 323589901645626402740534061303022610799, 323764579068143254949569963502637789135, 323939162299524695956483584526126981093,
  324113651491978379302607359945710471396, 324288046797302467728191624736538180672, 324462348366887173853659284907136349190, 324636556351716293415951865676608610175,
  324810670902368731103889742123183760987, 324984692169020019036163439614293656790, 325158620301443827925269428579529583156, 325332455449013470970402808984451035957,
  325506197760703400522020662111673333530, 325679847385090697560493619086248401105, 325853404470356554030969335346820951760, 326026869164287748076280046533095282680,
  326200241614278112209437192821006551426, 326373521967329994466969214590975320217, 326546710370055712584074021674770231221, 326719806968679001232275300715203276489,
  326892811909036452359991730019557079973, 327065725336578948676150298526445474880, 327238547396373090316699255173346953773, 327411278233102614733602727285148572247,
  327583917991069809845627722037515668592, 327756466814196920489965044213387060546, 327928924846027548213458607190655991692, 328101292229728044441952663389909420616,
  328273569108088897066003616478131629456, 328445755623526110480942281860009718173, 328617851918082579119013715970632252847, 328789858133429454511065020372882604179,
  328961774410867505914996825601828621255, 329133600891328474547941454208244772488, 329305337715376421458880034832663844198, 329476985023209069078162071863942203380,
  329648542954659136480144150949525454847, 329820011649195668394919562147206473044, 329991391245925358004867632828586793761, 330162681883593863561510464718872830702,
  330333883700587118857925547008197082113, 330504996834932637591725353782632086059, 330676021424300811653379512747102254175, 330846957606006203374421437156734453274,
  331017805517008831769849428005917034351, 331188565293915452808802162970688873560, 331359237072980833747360176640719543611, 331529820990109021557098387646487961981,
  331700317180854605482789926971832579683, 331870725780423973762438452778797144656, 332041046923676564542594785346429497073, 332211280745126111021694046270932974510,
  332381427378941880853931524069992596162, 332551486958949909845979199101953677689, 332721459618634229978630229716105484643, 332891345491138091785245714399909383981,
  333061144709265181118666687128397565994, 333230857405480830338044561033945401398, 333400483711913223946835094921506024964, 333570023760354598712994404210577526573,
  333739477682262438302210558879667558425, 333908845608760662454800892343048147188, 334078127670640810736703273455172981417, 334247323998363220894789255696684304805,
  334416434722058201846528199856921670440, 334585459971527201333834156127387157984, 334754399876243968270731475520177100241, 334923254565355709814280786110416129476,
  335092024167684243188014104080371819071, 335260708811727142286936440344725912389, 335429308625658879092961298211079824338, 335597823737331959929458923745669497233,
  335766254274278056583409056057539964723, 335934600363709132323464217487517641510, 336102862132518562842045271708781427198, 336271039707282252149408049145153945383,
  336439133214259743447438282135616280880, 336607142779395325010751895274738852330, 336775068528319131102498847804835214161, 336942910586348237952091213402019341145,
  337110669078487754821899996868390173567, 337278344129431910189790315906636032807, 337445935863565133074191008207632413414, 337613444404963129528222448527013170255,
  337780869877393954329235366367777255883, 337948212404319077889943731529859176829, 338115472108894448417166311442841789056, 338282649113971549344024290273663995699,
  338449743542098452061276364805709047626, 338616755515520863973307985625853813150, 338783685156183171904127883936066202782, 338950532585729480878562704126449019897,
  339117297925504648303679440003082045408, 339283981296555313575305438246810257146, 339450582819630923134356976371853708885, 339617102615184750997529834331789534285,
  339783540803374914786748849252570169619, 339949897504065387281618161915820656447, 340116172836827003518959722018333391818, 340282366920938463463374607431768211455]

theorem rotCert10_ok : certOK (2^10) (2^246) 0 rotCert10 = true := by decide +kernel

theorem rot10_canonical (Y : Nat) (hb : Y*Y < 2^256) :
    (Y*Y) / 2^246 + 2^10 * ((Y*Y) % 2^246) < SquareReduction.p :=
  rot_lt_p (2^10) (2^246) (by positivity) (by positivity) (by norm_num) rotCert10 rotCert10_ok Y hb

end ECDSAAdd.Entrant

end

section
-- ===== SquareAcc =====

/-! Streamed square with accumulated (c−1)-corrections. All small
(c−1)·slice corrections of a branch are summed exactly in a 163-bit
accumulator and then folded with a single modular addition. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def rot128F (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=false,canonical:=true,src:=L.rotated128}
def negP (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=true,canonical:=true,src:=L.core.product.take 256}
def negRot (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=true,canonical:=true,src:=L.rotated128}
def topSlice (L : CuccaroStreamedSquareWideLayout) (j : Nat) : List Wire :=
  (L.core.product.take 256).drop (256-j)
def rotF (L : CuccaroStreamedSquareWideLayout) (neg : Bool) (j : Nat) : MeasuredSquareFold :=
  {negative:=neg,canonical:=false,src:=rotateFull (L.core.product.take 256) j}
/-- Same rotated source, folded without source normalization (proved canonical). -/
def rotC (L : CuccaroStreamedSquareWideLayout) (neg : Bool) (j : Nat) : MeasuredSquareFold :=
  {negative:=neg,canonical:=true,src:=rotateFull (L.core.product.take 256) j}
def posTop (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=false,canonical:=true,src:=L.core.product.drop 256,shift:=128}

/-- Branch B's small correction W = top32 + top10 + top4 - top6, built in the 33-bit temporary. -/
def preW (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=topSlice L 32},
   {negative:=false,canonical:=true,src:=topSlice L 10},
   {negative:=false,canonical:=true,src:=topSlice L 4},
   {negative:=true,canonical:=true,src:=topSlice L 6}]

/-- The two small H updates precede the full-width shift. -/
def earlyHTerms (src : List Wire) : List MeasuredSquareFold :=
  [Acc.earlyTerm src false 4,Acc.earlyTerm src false 10,
   Acc.earlyTerm src true 6,Acc.earlyTerm src false 32]

theorem earlyH_mem (src : List Wire) (f : MeasuredSquareFold) :
    f∈earlyHTerms src ↔ f∈nafMinusOneItems false src := by
  simp only [earlyHTerms,Acc.earlyTerm,nafMinusOneItems,Bool.not_false,
    List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- Branch B's accumulator terms: d*H - d*W instead of five d-multiples. -/
def termsB (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  earlyHTerms (hiReg L)

def accARaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)
def accBRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++nafMinusOneItems true (topSlice L 4)++
    nafMinusOneItems false (topSlice L 6)++nafMinusOneItems true (topSlice L 10)++
    nafMinusOneItems true (topSlice L 32)
def accCRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++[posTop L]

def accAMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inr ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩,.inl (negP L)]
def accBMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rotC L true 4),.inl (rotC L true 10),.inl (rotC L true 32),
    .inl (rotC L false 6),.inl (rot128F L),.inr ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩]
def accCMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negRot L),.inr ⟨true,[],earlyHTerms (L.core.product.drop 128)++[posTop L],earlyHTerms (L.core.product.drop 128)++[posTop L]⟩]

def accBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256) (mixFolds L false (accAMix L))
def accBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256) (mixFolds L true (accBMix L))
def accMiddleC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.sum L.core.product (mixFolds L true (accCMix L))
def accBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++accMiddleC L control++L.core.clearSum

/-- Branch C (all negative folds) runs between A and B, so it needs no
orientation switch; the square then ends in the unreflected orientation. -/
def resC2 (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast true O+(-(P : ZMod SquareReduction.p)*2^128))

def accProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchC L control++accBranchB L control++L.reflectOutput

/-- The accumulated square without its final output reflection. -/
def accPrefix (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchC L control++accBranchB L control

theorem accProgram_split (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    accProgram L control=accPrefix L control++L.reflectOutput := by
  simp only [accProgram,accPrefix,List.append_assoc]

theorem acc_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal false (accAMix L)=true ∧ mixFinal true (accBMix L)=false ∧
    mixFinal true (accCMix L)=true := by
  simp [mixFinal,mixNeg,accAMix,accBMix,accCMix,rot128F,negP,negRot,rotF,rotC]

theorem naf_facts (neg : Bool) (src : List Wire) (f : MeasuredSquareFold)
    (hf : f∈nafMinusOneItems neg src) :
    f.src=src ∧ (f.shift=4 ∨ f.shift=6 ∨ f.shift=10 ∨ f.shift=32) := by
  simp only [nafMinusOneItems,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> simp

theorem topSlice_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (j : Nat) (hj : j≤256) :
    (topSlice L j).length=j := by
  simp [topSlice,hw.core.product]; omega

theorem topSlice_count (L : CuccaroStreamedSquareWideLayout) (j : Nat) (q : Wire) :
    (topSlice L j).count q≤L.core.product.count q :=
  ((List.drop_sublist _ _).count_le q).trans ((List.take_sublist _ _).count_le q)

/-- Every accumulated term is a short slice at a small shift. -/
theorem raw_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (f : MeasuredSquareFold)
    (hf : f∈accARaw L ∨ f∈accCRaw L) :
    (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
  have dl : (L.core.product.drop 128).length=130 := by simp [hw.core.product]
  have naf (neg : Bool) (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q)
      (hl : src.length=130) (hf : f∈nafMinusOneItems neg src) :
      (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
    obtain ⟨e,sh⟩ := naf_facts neg src f hf
    rw [e]
    refine ⟨hs,?_⟩
    simp only [TermOK,e]
    omega
  have dc := L.productDrop_count 128
  rcases hf with hf|hf
  · exact naf false _ dc (by omega) hf
  · simp only [accCRaw,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with hf|rfl
    · exact naf false _ dc (by omega) hf
    · refine ⟨L.productDrop_count 256,?_⟩
      simp [TermOK,posTop,hw.core.product]

theorem sorted_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (raw : List MeasuredSquareFold)
    (hr : ∀f∈raw,(∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f) :
    (∀f∈sortedItems false raw,∀q,f.src.count q≤L.core.product.count q) ∧
      (∀f∈sortedItems false raw,TermOK f) :=
  ⟨fun f hf => (hr f ((sorted_perm _ _).subset hf)).1,fun f hf => (hr f ((sorted_perm _ _).subset hf)).2⟩

theorem validA (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    Acc.Valid t 163 0 (earlyHTerms (L.core.product.drop 128)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  simp [Acc.Valid,Acc.step,earlyHTerms,Acc.earlyTerm]
  generalize regValue (L.core.product.drop 128) t=T at hT ⊢
  omega

theorem validC (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    Acc.Valid t 163 0 (earlyHTerms (L.core.product.drop 128)++[posTop L]) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  have hU := regValue_lt (L.core.product.drop 256) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  rw [show (L.core.product.drop 256).length=2 by simp [hw.core.product]] at hU
  simp [Acc.Valid,Acc.step,earlyHTerms,Acc.earlyTerm,posTop]
  generalize regValue (L.core.product.drop 128) t=T at hT ⊢
  generalize regValue (L.core.product.drop 256) t=U at hU ⊢
  omega

theorem top_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) (j : Nat) (hj : j≤128) :
    regValue (topSlice L j) t*2^(128-j)≤regValue (L.core.product.drop 128) t := by
  rw [topSlice,L.productTakeDrop_value hw t P hP j (by omega),L.product_drop_value hw t P hP 128 (by omega),
    Nat.mod_eq_of_lt hb]
  have e : 256-j=128+(128-j) := by omega
  rw [e,pow_add,←Nat.div_div_eq_div_mul]
  exact Nat.div_mul_le_self _ _

theorem top_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) (j : Nat) (hj : j≤128) :
    regValue (topSlice L j) t=regValue (L.core.product.drop 128) t/2^(128-j) := by
  rw [topSlice,L.productTakeDrop_value hw t P hP j (by omega),L.product_drop_value hw t P hP 128 (by omega),
    Nat.mod_eq_of_lt hb]
  have e : 256-j=128+(128-j) := by omega
  rw [e,pow_add,←Nat.div_div_eq_div_mul]

theorem plain_view (L : CuccaroStreamedSquareWideLayout) (t : BasisState) (neg : Bool)
    (xs : List MeasuredSquareFold) (hc : ∀f∈xs,∀q,f.src.count q≤L.core.product.count q)
    (ho : ∀f∈xs,TermOK f) (hv : Acc.Valid t 163 0 xs) : AccView L t ⟨neg,[],xs,xs⟩ := by
  refine ⟨fun f hf q => ?_,ho,by simp,by simp,by simp [Acc.Valid],hv,by simp [Acc.accVal],?_⟩
  · have h := hc f hf q; simp only [List.count_append]; omega
  · intro t' ht' hh _
    have hh' : regValue (hiReg L) t'=regValue (hiReg L) t := by simpa using hh
    have agree : ∀q∈L.core.product,t' q=t q := by
      intro q hq
      by_cases hq' : q∈hiReg L
      · exact (regValue_eq_iff _ _ _).mp hh' q hq'
      · exact ht' q hq hq'
    have vc := Acc.valid_congr t t' 163 xs (fun f hf => regValue_congr _ _ _ (fun q hq => by
      have pos := List.count_pos_iff.mpr hq
      have b := hc f hf q
      exact (agree q (List.count_pos_iff.mp (by omega))).symm)) 0
    exact ⟨vc.1.mp hv,vc.2.symm⟩

theorem validB (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    Acc.Valid t 163 0 (sortedItems false (accBRaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  have l (j : Nat) (hj : j≤32) := topSlice_length L hw j (by omega)
  have b4 := regValue_lt (topSlice L 4) t
  have b6 := regValue_lt (topSlice L 6) t
  have b10 := regValue_lt (topSlice L 10) t
  have b32 := regValue_lt (topSlice L 32) t
  rw [l 4 (by omega)] at b4
  rw [l 6 (by omega)] at b6
  rw [l 10 (by omega)] at b10
  rw [l 32 (by omega)] at b32
  have r4 := top_rel L hw t P hP hb 4 (by omega)
  have r6 := top_rel L hw t P hP hb 6 (by omega)
  have r10 := top_rel L hw t P hP hb 10 (by omega)
  have r32 := top_rel L hw t P hP hb 32 (by omega)
  simp [Acc.Valid,Acc.step,sortedItems,accBRaw,nafMinusOneItems,List.filter_cons]
  norm_num at r4 r6 r10 r32 b4 b6 b10 b32 hT
  generalize regValue (L.core.product.drop 128) t=D at *
  generalize regValue (topSlice L 4) t=a at *
  generalize regValue (topSlice L 6) t=b at *
  generalize regValue (topSlice L 10) t=c at *
  generalize regValue (topSlice L 32) t=d at *
  omega

theorem hiReg_top (L : CuccaroStreamedSquareWideLayout) : hiReg L=topSlice L 128 := rfl

theorem termsB_facts (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) (hf : f∈termsB L) :
    f.src=hiReg L ∧ 4≤f.shift ∧ f.shift≤32 := by
  obtain ⟨e,sh⟩ := naf_facts false _ f ((earlyH_mem _ _).mp hf)
  exact ⟨e,by omega,by omega⟩

theorem accB_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    AccView L t ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩ := by
  have hl := (split_lengths L hw).2.1
  have l (j : Nat) (hj : j≤32) := topSlice_length L hw j (by omega)
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  have hH : regValue (L.core.product.drop 128) t<2^128 := by
    rw [L.product_drop_value hw t P hP 128 (by omega)]
    exact Nat.div_lt_of_lt_mul (by have e : (2:ℕ)^128*2^128=2^256 := by norm_num
                                   rw [e]; exact hb)
  have hiv : regValue (hiReg L) t=regValue (L.core.product.drop 128) t := by
    rw [hiReg_top,top_eq L hw t P hP hb 128 (by omega)]; simp
  have r4 := top_rel L hw t P hP hb 4 (by omega)
  have r6 := top_rel L hw t P hP hb 6 (by omega)
  have r10 := top_rel L hw t P hP hb 10 (by omega)
  have r32 := top_rel L hw t P hP hb 32 (by omega)
  have m610 : regValue (topSlice L 6) t≤regValue (topSlice L 10) t := by
    rw [top_eq L hw t P hP hb 6 (by omega),top_eq L hw t P hP hb 10 (by omega)]
    exact Nat.div_le_div_left (by norm_num) (by norm_num)
  have m46 : regValue (topSlice L 4) t≤regValue (topSlice L 6) t := by
    rw [top_eq L hw t P hP hb 4 (by omega),top_eq L hw t P hP hb 6 (by omega)]
    exact Nat.div_le_div_left (by norm_num) (by norm_num)
  have m1032 : regValue (topSlice L 10) t≤regValue (topSlice L 32) t := by
    rw [top_eq L hw t P hP hb 10 (by omega),top_eq L hw t P hP hb 32 (by omega)]
    exact Nat.div_le_div_left (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_,?_,validB L hw t P hP hb,?_,?_⟩
  · intro f hf q
    have dc := (List.drop_sublist 128 (L.core.product.take 256)).count_le q
    have tc := (List.take_sublist 256 L.core.product).count_le q
    simp only [SrcOK,List.count_append]
    rw [(termsB_facts L f hf).1]
    simp only [hiReg]
    omega
  · intro f hf
    obtain ⟨e,s1,s2⟩ := termsB_facts L f hf
    simp only [TermOK]
    rw [e,hl]
    omega
  · intro f hf q
    simp only [preW,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl <;> exact topSlice_count L _ q
  · intro f hf
    simp only [preW,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl <;> simp only [TermOK33,l 32 (by omega),l 10 (by omega),l 4 (by omega),
      l 6 (by omega)] <;> omega
  · have b4 := regValue_lt (topSlice L 4) t
    have b10 := regValue_lt (topSlice L 10) t
    have b32 := regValue_lt (topSlice L 32) t
    rw [l 4 (by omega)] at b4
    rw [l 10 (by omega)] at b10
    rw [l 32 (by omega)] at b32
    simp [Acc.Valid,Acc.step,preW]
    norm_num at b4 b10 b32 ⊢
    omega
  · simp [Acc.accVal,Acc.step,preW]
    rw [hiv]
    norm_num at r4 r6 r10 r32 hH ⊢
    generalize regValue (L.core.product.drop 128) t=D at *
    generalize regValue (topSlice L 4) t=a at *
    generalize regValue (topSlice L 6) t=b at *
    generalize regValue (topSlice L 10) t=c at *
    generalize regValue (topSlice L 32) t=d at *
    omega
  · intro t' _ hval _
    have pre_ne : preW L≠[] := by simp [preW]
    simp only [pre_ne,if_false] at hval
    rw [hiv] at hval
    simp [Acc.Valid,Acc.accVal,Acc.step,termsB,earlyHTerms,Acc.earlyTerm,sortedItems,accBRaw,preW,nafMinusOneItems,
      List.filter_cons] at hval ⊢
    have hU := regValue_lt (hiReg L) t'
    rw [hl] at hU
    norm_num at r4 r6 r10 r32 hH hU ⊢
    generalize regValue (hiReg L) t'=U at *
    generalize regValue (L.core.product.drop 128) t=D at *
    generalize regValue (topSlice L 4) t=a at *
    generalize regValue (topSlice L 6) t=b at *
    generalize regValue (topSlice L 10) t=c at *
    generalize regValue (topSlice L 32) t=d at *
    omega

theorem accA_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    mixSignedSum t (accAMix L)=measuredSignedSum t L.measuredAItems := by
  have cast := Acc.accVal_cast t 163 (earlyHTerms (L.core.product.drop 128)) 0 (validA L hw t)
  simp only [accAMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredAItems,accARaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,rot128F,negP,nafMinusOneItems,earlyHTerms,Acc.earlyTerm]
  ring

theorem accB_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) :
    mixSignedSum t (accBMix L)=measuredSignedSum t L.measuredBItems := by
  have cast := Acc.accVal_cast t 163 (sortedItems false (accBRaw L)) 0 (validB L hw t P hP hb)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accBMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredBItems,accBRaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,measuredSignedSum_append,
    rot128F,negP,rotF,rotC,topSlice,nafMinusOneItems,shiftedProductItems]
  ring

theorem accC_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    mixSignedSum t (accCMix L)=measuredSignedSum t L.measuredCItems := by
  have cast := Acc.accVal_cast t 163 (earlyHTerms (L.core.product.drop 128)++[posTop L]) 0 (validC L hw t)
  simp only [accCMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredCItems,accCRaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,measuredSignedSum_append,
    negRot,posTop,nafMinusOneItems,earlyHTerms,Acc.earlyTerm]
  ring

theorem accA_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    ∀i∈accAMix L,MixView L t i := by
  intro i hi
  simp only [accAMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,rot128F])
  · have st := sorted_static L hw (accARaw L) (fun f hf => raw_static L hw f (Or.inl hf))
    have member (f : MeasuredSquareFold) (hf : f∈earlyHTerms (L.core.product.drop 128)) :
        f∈sortedItems false (accARaw L) := by
      apply (sorted_perm _ _).symm.subset
      exact (earlyH_mem _ _).mp hf
    exact plain_view L t false _ (fun f hf => st.1 f (member f hf))
      (fun f hf => st.2 f (member f hf)) (validA L hw t)
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,negP])

theorem square_mod8 (M : Nat) : M^2%8≠5 ∧ M^2%8≠6 ∧ M^2%8≠7 := by
  have h : M^2%8=(M%8)^2%8 := Nat.pow_mod M 2 8
  have lt := Nat.mod_lt M (show 8>0 by norm_num)
  rw [h]
  interval_cases (M%8) <;> decide

/-- A square below 2^256 rotated by 32 is already below p: the low 224 bits
cannot be among the three largest residues, which are 5, 6, 7 mod 8. -/
theorem rot32_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 32) t*2^0<SquareReduction.p := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  rw [L.rotateFull_value hw t (M^2) hp 32 (by omega),Nat.mod_eq_of_lt hb]
  have m8 := square_mod8 M
  have e : M^2%2^(256-32)%8=M^2%8 := Nat.mod_mod_of_dvd _ (by norm_num)
  have hH : M^2/2^(256-32)<2^32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc M^2<2^256 := hb
      _ = 2^32*2^(256-32) := by norm_num
  have hL := Nat.mod_lt (M^2) (show 2^(256-32)>0 by positivity)
  generalize M^2/2^(256-32)=H at hH ⊢
  generalize hX : M^2%2^(256-32)=X at hL e ⊢
  rw [←e] at m8
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at hH hL ⊢
  omega

theorem accB_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    ∀i∈accBMix L,MixView L t i := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have hbm : M*M<2^256 := by simpa [sq] using hb
  have rc (neg : Bool) (j : Nat) (hj : j≤256)
      (hcan : (M*M)/2^(256-j)+2^j*((M*M)%2^(256-j))<SquareReduction.p)
      (hmem : rotF L neg j∈L.measuredBItems) : MixView L t (.inl (rotC L neg j)) := by
    have base := L.measuredB_views hw t M hM hp (rotF L neg j) hmem
    refine ⟨base.count,base.span,fun _ => ?_⟩
    have hv := L.rotateFull_value hw t (M^2) hp j hj
    change regValue (rotateFull (L.core.product.take 256) j) t*2^0<SquareReduction.p
    rw [hv, pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hb, sq]
    exact hcan
  intro i hi
  simp only [accBMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact L.measuredB_views hw t M hM hp _ (by simp [measuredBItems,shiftedProductItems,negP])
  · exact rc true 4 (by omega) (rot4_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · exact rc true 10 (by omega) (rot10_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · have v := L.measuredB_views hw t M hM hp (rotF L true 32)
      (by simp [measuredBItems,shiftedProductItems,rotF])
    exact ⟨v.count,v.span,fun _ => rot32_canonical L hw t M hM hp⟩
  · exact rc false 6 (by omega) (rot6_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · exact L.measuredB_views hw t M hM hp _ (by simp [measuredBItems,rot128F])
  · exact accB_view L hw t (M^2) hp hb

theorem accC_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hp : regValue L.core.product t=M^2) :
    ∀i∈accCMix L,MixView L t i := by
  intro i hi
  simp only [accCMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · exact L.measuredC_views hw t M hp _ (by simp [measuredCItems,negRot])
  · have st := sorted_static L hw (accCRaw L) (fun f hf => raw_static L hw f (Or.inr hf))
    have member (f : MeasuredSquareFold)
        (hf : f∈earlyHTerms (L.core.product.drop 128)++[posTop L]) :
        f∈sortedItems false (accCRaw L) := by
      apply (sorted_perm _ _).symm.subset
      simp only [List.mem_append,List.mem_singleton] at hf
      rcases hf with hf|rfl
      · exact List.mem_append_left _ ((earlyH_mem _ _).mp hf)
      · simp [accCRaw]
    exact plain_view L t true _ (fun f hf => st.1 f (member f hf))
      (fun f hf => st.2 f (member f hf)) (validC L hw t)

theorem acc_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMix L,MixStatic L i) ∧ (∀i∈accBMix L,MixStatic L i) ∧ (∀i∈accCMix L,MixStatic L i) := by
  let z : BasisState := fun _ => false
  have hz : regValue L.core.product z=0^2 := by
    simpa using (regValue_zero L.core.product z).mpr (fun _ _ => rfl)
  have conv (i : MixItem) (h : MixView L z i) : MixStatic L i := by
    cases i with
    | inl f => exact h.count
    | inr a => exact ⟨h.count,h.ok,h.preCount,h.preOk⟩
  exact ⟨fun i hi => conv i (accA_views L hw z 0 (by decide) hz i hi),
    fun i hi => conv i (accB_views L hw z 0 (by decide) hz i hi),
    fun i hi => conv i (accC_views L hw z 0 hz i hi)⟩

theorem accBranchA_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accBranchA L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchA L control) records s).basis=
      resA ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchA L control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixed_contribution L hw control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) false (accAMix L) s records hc dstZero
    O (M^2) (resA (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => accA_views L hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).1]
      exact cast_ofCast _ _)
  exact result

theorem accBranchB_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accBranchB L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchB L control) records s).basis=
      resB ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchB L control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixed_contribution L hw control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) true (accBMix L) s records hc dstZero
    O (M^2) (resB (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp => accB_views L hw t M mb hp)
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).2.1]
      exact cast_ofCast _ _)
  exact result

theorem accMiddleC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) :
    (run (accMiddleC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleC L control) records s).basis=
      resC2 ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleC L control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := withMixed_contribution L hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) true (accCMix L) s records hc hp0
    O (M^2) (resC2 (M^2) O) hO ho (by rw [hs])
    (fun _ hp _ => hp) (fun t hp => accC_views L hw t M hp)
    (-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)
    (fun t hp => (accC_mixSum L hw t).trans (L.measuredC_sum hw t (M^2) hp))
    (ofCast_lt _ _) (by
      rw [(acc_orientations L).2.2]
      exact cast_ofCast _ _)
  exact result

theorem accBranchC_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) :
    (run (accBranchC L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchC L control) records s).basis=
      resC2 ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchC L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := accMiddleC L control
  let u := run L.core.prepareSum [] s
  let v := run middle (records.take (measurementCount middle)) u
  let out := run L.core.clearSum (records.drop (measurementCount middle)) v
  have prep := L.prepareSum_frame hw nd s.basis A B ha hb bound (PairClean.corePad L s.basis hc) hc.cin
    s [] (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have used := accMiddleC_correct L hw control hn (A+B) O hO u
    (records.take (measurementCount middle)) prep.2.1 outU productU cleanU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have cleared := L.clearSum_frame hw nd restoreBase A B lowRestore sumRestore bound padRestore cinRestore
    v (records.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resC2 ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resC2 ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  have prepM := (L.core.sum_counts hw.core).1.2
  simpa [accBranchC,middle,u,v,out,run_append,prepM] using final

theorem acb_complete_exact (enabled : Bool) (A B O : Nat) :
    resB ((if enabled then B else 0)^2)
      (resC2 ((if enabled then A+B else 0)^2) (resA ((if enabled then A else 0)^2) O))=
      subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OC := resC2 PC OA
  let OB := resB PB OC
  have ea : measuredOrientationCast true OA=measuredOrientationCast false O+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have ec : measuredOrientationCast true OC=measuredOrientationCast true OA+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast false OB=measuredOrientationCast true OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have obBound : OB<SquareReduction.p := ofCast_lt _ _
  have cast : (OB : ZMod SquareReduction.p)=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [subModValue_cast]
    linear_combination eb+ec+ea+identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt obBound,ZMod.val_natCast_of_lt targetBound] using value

theorem accPrefix_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (accPrefix L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefix L control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefix L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := resA PA O
  let OC := resC2 PC OA
  let OB := resB PB OC
  let restA := records.drop (measurementCount (accBranchA L control))
  let restC := restA.drop (measurementCount (accBranchC L control))
  let u := run (accBranchA L control) (records.take (measurementCount (accBranchA L control))) s
  let v := run (accBranchC L control) (restA.take (measurementCount (accBranchC L control))) u
  let w := run (accBranchB L control) restC v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := accBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (accBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowU : regValue L.core.low u.basis=A := regValue_congr _ _ _ (fun q hq => ea.2.2 q (lowAway q hq))
  have sumU : regValue L.core.sum u.basis=B :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (sumAway q hq))).trans sumB
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have ec := accBranchC_correct L hw control hn A B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (accBranchC L control))) lowU sumU sumBound ea.2.1 productU cleanU
  rw [ctrlU] at ec
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (ec.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OC ⟨ec.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highV : regValue L.core.high v.basis=B :=
    regValue_congr _ _ _ (fun q hq => sameV q (highAway q hq))
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have eb := accBranchB_correct L hw control hn B OC (ofCast_lt _ _) v restC highV ec.2.1 productV cleanV
  rw [ctrlV] at eb
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (eb.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := acb_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    rw [eb.2.1]
    exact exactResult
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨eb.1.trans (ec.1.trans ea.1),fullValue,sameW⟩
  simpa [accPrefix,u,v,w,restA,restC,enabled,run_append,Nat.add_assoc] using final

theorem acc_item_prices (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (mixFoldsT false (accAMix L)=4112 ∧ mixFoldsM false (accAMix L)=4112) ∧
    (mixFoldsT true (accBMix L)=9096 ∧ mixFoldsM true (accBMix L)=9096) ∧
    (mixFoldsT true (accCMix L)=2902 ∧ mixFoldsM true (accCMix L)=2902) := by
  norm_num [mixFoldsT,mixFoldsM,mixNeg,accAMix,accBMix,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildT,preW,termsB,accPrice,earlyHTerms,Acc.earlyTerm,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,hw.core.product,hiReg]
  all_goals (try rw [if_neg (List.cons_ne_nil _ _)])
  all_goals norm_num

theorem accProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accProgram L control)=68205 ∧ measurementCount (accProgram L control)=67693 := by
  have st := acc_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := L.withMeasuredSquare_counts hw control L.core.low (L.core.product.take 256)
    (mixFolds L false (accAMix L)) (by omega) (by omega) (by omega)
  have b := L.withMeasuredSquare_counts hw control L.core.high (L.core.product.take 256)
    (mixFolds L true (accBMix L)) (by omega) (by omega) (by omega)
  have c := L.withMeasuredSquare_counts hw control L.core.sum L.core.product
    (mixFolds L true (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := mixFolds_counts L hw false (accAMix L) st.1
  have fb := mixFolds_counts L hw true (accBMix L) st.2.1
  have fc := mixFolds_counts L hw true (accCMix L) st.2.2
  have prices := acc_item_prices L hw
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  rw [prices.2.2.1,prices.2.2.2] at fc
  have reflection := (L.measured_small_operation_counts hw).2.2
  have sum := L.core.sum_counts hw.core
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    reflection.1,reflection.2,sum.1.1,sum.1.2,sum.2.1,sum.2.2,lo,hi,su,p256,hw.core.product]
  norm_num [signedSquareRowsCount]

theorem accProgram_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (accProgram L control)⊆(control::L.wires).toFinset := by
  have st := acc_static L hw
  have a := mixFolds_support L hw hn control false (accAMix L) st.1
  have b := mixFolds_support L hw hn control true (accBMix L) st.2.1
  have c := mixFolds_support L hw hn control true (accCMix L) st.2.2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sa : ECDSAAdd.wires (accBranchA L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.low (L.core.product.take 256)
    (mixFolds L false (accAMix L)) (by omega) (by omega) (by omega)
    (by intro q hq; simp [CuccaroStreamedSquareLayout.low] at hq; exact List.mem_append_left _ (List.mem_of_mem_take hq))
    (fun _ hq => List.mem_of_mem_take hq) a
  have sb : ECDSAAdd.wires (accBranchB L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.high (L.core.product.take 256)
    (mixFolds L true (accBMix L)) (by omega) (by omega) (by omega)
    (by intro q hq; exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
    (fun _ hq => List.mem_of_mem_take hq) b
  have sc : ECDSAAdd.wires (accMiddleC L control)⊆(control::L.wires).toFinset :=
    L.withMeasuredSquare_support hw control L.core.sum L.core.product
    (mixFolds L true (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,sum])
    (by
      intro q hq
      simp only [CuccaroStreamedSquareLayout.sum,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl
      · exact List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq))
      · simp)
    (fun _ hq => hq) c
  have sumCert := L.sum_certified hw hn
  have embed : L.wires.toFinset⊆(control::L.wires).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons] at hq ⊢; exact Or.inr hq
  have prep := sumCert.1.2.trans embed
  have unprep := sumCert.2.2.trans embed
  have reflection : ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
    (L.measured_small_support control).2.2.1
  simpa only [accProgram,accBranchC,
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa
      (And.intro (And.intro prep sc) unprep)) sb) reflection

theorem accProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (accProgram L control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have a := L.withMeasuredSquare_physical control hn _ _ hl hp _
    (mixFolds_physical L hw nd false (accAMix L) st.1)
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (mixFolds_physical L hw nd true (accBMix L) st.2.1)
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (mixFolds_physical L hw nd true (accCMix L) st.2.2)
  have prep := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,gatePhysical_append]
  exact ⟨⟨⟨a,⟨prep,c⟩,clear⟩,b⟩,L.reflectOutput_physical nd⟩

theorem accProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (accProgram L control) ≤ 5000000 := by
  have st := acc_static L hw
  have bd (items : List MixItem) (h : items=accAMix L ∨ items=accBMix L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMix,accBMix,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,earlyHTerms,Acc.earlyTerm,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFolds_gateSlots L hw false (accAMix L) st.1 20 (bd _ (Or.inl rfl))
  have hb := mixFolds_gateSlots L hw true (accBMix L) st.2.1 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := mixFolds_gateSlots L hw true (accCMix L) st.2.2 20 (bd _ (Or.inr (Or.inr rfl)))
  have la : (accAMix L).length = 3 := rfl
  have lb : (accBMix L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  rw [lc] at hc
  have hd : (L.core.product.take 256).length ≤ 258 := by
    simp only [List.length_take]; omega
  have a := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.low _
    (mixFolds L false (accAMix L)) hd
  have b := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.high _
    (mixFolds L true (accBMix L)) hd
  have c := Baselines.withMeasuredSquare_gateSlots_le L hw control L.core.sum L.core.product
    (mixFolds L true (accCMix L)) (by rw [hw.core.product])
  have hp := Baselines.cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change Challenge.gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,
    CuccaroStreamedSquareLayout.clearSum, Challenge.gateSlots_append, Baselines.reverse_gateSlots]
  omega

theorem accPrefix_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accPrefix L control)=67950 ∧ measurementCount (accPrefix L control)=67438 := by
  have full := accProgram_counts L hw control
  have r := (L.measured_small_operation_counts hw).2.2
  rw [accProgram_split,toffoliCount_append,measurementCount_append] at full
  omega

theorem accPrefix_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) :
    ECDSAAdd.wires (accPrefix L control)⊆(control::L.wires).toFinset := by
  have full := accProgram_support L hw hn control
  rw [accProgram_split,wires_append] at full
  exact Finset.union_subset_left full

theorem accPrefix_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (accPrefix L control) := by
  have full := accProgram_physical L hw control hn
  rw [accProgram_split,gatePhysical_append] at full
  exact full.1

theorem accPrefix_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (accPrefix L control) ≤ 5000000 := by
  have full := accProgram_gateSlots_le L hw control
  rw [accProgram_split,Challenge.gateSlots_append] at full
  omega

end ECDSAAdd.Entrant

end
