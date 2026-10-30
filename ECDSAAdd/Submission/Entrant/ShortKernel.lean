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
