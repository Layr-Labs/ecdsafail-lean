import ECDSAAdd.Submission.Entrant.AccFold
import ECDSAAdd.Submission.Entrant.RotCert

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
/-- The rotation by 32 of a 128-bit square is already canonical (`rot32_canonical`),
so its fold needs no normalize/restore pair. -/
def rotC (L : CuccaroStreamedSquareWideLayout) (neg : Bool) (j : Nat) : MeasuredSquareFold :=
  {negative:=neg,canonical:=true,src:=rotateFull (L.core.product.take 256) j}
def posTop (L : CuccaroStreamedSquareWideLayout) : MeasuredSquareFold :=
  {negative:=false,canonical:=true,src:=L.core.product.drop 256,shift:=128}

def accARaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)
def accBRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++nafMinusOneItems true (topSlice L 4)++
    nafMinusOneItems false (topSlice L 6)++nafMinusOneItems true (topSlice L 10)++
    nafMinusOneItems true (topSlice L 32)
def accCRaw (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  nafMinusOneItems false (L.core.product.drop 128)++[posTop L]

def accAMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inr ⟨false,sortedItems false (accARaw L)⟩,.inl (negP L)]
def accBMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rotC L true 4),.inl (rotC L true 10),.inl (rotC L true 32),
    .inl (rotC L false 6),.inl (rot128F L),.inr ⟨false,sortedItems false (accBRaw L)⟩]
def accCMix (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negRot L),.inr ⟨true,sortedItems false (accCRaw L)⟩]

def accBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256) (mixFolds L false (accAMix L))
def accBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256) (mixFolds L true (accBMix L))
def accMiddleC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.sum L.core.product (mixFolds L false (accCMix L))
def accBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++accMiddleC L control++L.core.clearSum

def accProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchB L control++accBranchC L control++L.reflectOutput

/-- The accumulated square without its final output reflection. -/
def accPrefix (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  accBranchA L control++accBranchB L control++accBranchC L control

theorem accProgram_split (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    accProgram L control=accPrefix L control++L.reflectOutput := by
  simp only [accProgram,accPrefix,List.append_assoc]

theorem acc_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal false (accAMix L)=true ∧ mixFinal true (accBMix L)=false ∧
    mixFinal false (accCMix L)=true := by
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
    (hf : f∈accARaw L ∨ f∈accBRaw L ∨ f∈accCRaw L) :
    (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
  have dl : (L.core.product.drop 128).length=130 := by simp [hw.core.product]
  have naf (neg : Bool) (src : List Wire) (hs : ∀q,src.count q≤L.core.product.count q)
      (hl : src.length≤130) (hf : f∈nafMinusOneItems neg src) :
      (∀q,f.src.count q≤L.core.product.count q) ∧ TermOK f := by
    obtain ⟨e,sh⟩ := naf_facts neg src f hf
    rw [e]
    refine ⟨hs,?_⟩
    simp only [TermOK,e]
    omega
  have dc := L.productDrop_count 128
  have t (j : Nat) (hj : j≤32) (neg : Bool) (h : f∈nafMinusOneItems neg (topSlice L j)) :=
    naf neg (topSlice L j) (topSlice_count L j) (by rw [topSlice_length L hw j (by omega)]; omega) h
  rcases hf with hf|hf|hf
  · exact naf false _ dc (by omega) hf
  · simp only [accBRaw,List.mem_append] at hf
    rcases hf with (((hf|hf)|hf)|hf)|hf
    · exact naf false _ dc (by omega) hf
    · exact t 4 (by omega) true hf
    · exact t 6 (by omega) false hf
    · exact t 10 (by omega) true hf
    · exact t 32 (by omega) true hf
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
    Acc.Valid t 163 0 (sortedItems false (accARaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  simp [Acc.Valid,Acc.step,sortedItems,accARaw,nafMinusOneItems,List.filter_cons]
  generalize regValue (L.core.product.drop 128) t=T at hT ⊢
  omega

theorem validC (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    Acc.Valid t 163 0 (sortedItems false (accCRaw L)) := by
  have hT := regValue_lt (L.core.product.drop 128) t
  have hU := regValue_lt (L.core.product.drop 256) t
  rw [show (L.core.product.drop 128).length=130 by simp [hw.core.product]] at hT
  rw [show (L.core.product.drop 256).length=2 by simp [hw.core.product]] at hU
  simp [Acc.Valid,Acc.step,sortedItems,accCRaw,posTop,nafMinusOneItems,List.filter_cons]
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

theorem accA_mixSum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    mixSignedSum t (accAMix L)=measuredSignedSum t L.measuredAItems := by
  have cast := Acc.accVal_cast t 163 (sortedItems false (accARaw L)) 0 (validA L hw t)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accAMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredAItems,accARaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,rot128F,negP,nafMinusOneItems]
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
  have cast := Acc.accVal_cast t 163 (sortedItems false (accCRaw L)) 0 (validC L hw t)
  rw [signedSum_perm t (sorted_perm _ _)] at cast
  simp only [accCMix,mixSignedSum,mixSignedPayload,mixNeg,mixPayload,cast]
  simp [measuredCItems,accCRaw,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,measuredSignedSum_append,
    negRot,posTop,nafMinusOneItems]
  ring

theorem accA_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    ∀i∈accAMix L,MixView L t i := by
  intro i hi
  simp only [accAMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,rot128F])
  · have st := sorted_static L hw (accARaw L) (fun f hf => raw_static L hw f (Or.inl hf))
    exact ⟨st.1,st.2,validA L hw t⟩
  · exact L.measuredA_views hw t M hM hp _ (by simp [measuredAItems,negP])

/-- No integer square is 6 or 7 modulo 8. -/
theorem square_mod8_ne67 (Y : Nat) : Y^2%8≠6 ∧ Y^2%8≠7 := by
  have bound := Nat.mod_lt Y (by decide : 0<8)
  rw [Nat.pow_mod]
  interval_cases h : Y%8 <;> norm_num

/-- Rotating a 256-bit square left by 32 stays below p: reaching p would need
the square's low 224 bits to be `2^224-1` or `2^224-2`, i.e. 7 or 6 mod 8. -/
theorem rot32_canonical (Y : Nat) (hb : Y^2<2^256) :
    (Y^2%2^256)/2^224+2^32*((Y^2%2^256)%2^224)<SquareReduction.p := by
  rw [Nat.mod_eq_of_lt hb]
  have hH : Y^2/2^224<2^32 := by
    apply Nat.div_lt_of_lt_mul; norm_num at hb ⊢; omega
  have hLo : Y^2%2^224<2^224 := Nat.mod_lt _ (by positivity)
  have h8 : (Y^2%2^224)%8=Y^2%8 := Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 2^224)
  have n67 := square_mod8_ne67 Y
  have hne1 : Y^2%2^224≠2^224-1 := by
    intro e; rw [e] at h8; norm_num at h8; omega
  have hne2 : Y^2%2^224≠2^224-2 := by
    intro e; rw [e] at h8; norm_num at h8; omega
  have hle : Y^2%2^224≤2^224-3 := by omega
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at hH hle ⊢
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
  · have base := L.measuredB_views hw t M hM hp (rotF L true 32)
      (by simp [measuredBItems,shiftedProductItems,rotF])
    refine ⟨base.count,base.span,fun _ => ?_⟩
    have hv := L.rotateFull_value hw t (M^2) hp 32 (by omega)
    change regValue (rotateFull (L.core.product.take 256) 32) t*2^0<SquareReduction.p
    rw [hv, pow_zero, Nat.mul_one]
    simpa using rot32_canonical M hb
  · exact rc false 6 (by omega) (rot6_canonical M hbm)
      (by simp [measuredBItems,shiftedProductItems,rotF])
  · exact L.measuredB_views hw t M hM hp _ (by simp [measuredBItems,rot128F])
  · have st := sorted_static L hw (accBRaw L) (fun f hf => raw_static L hw f (Or.inr (Or.inl hf)))
    exact ⟨st.1,st.2,validB L hw t (M^2) hp hb⟩

theorem accC_views (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hp : regValue L.core.product t=M^2) :
    ∀i∈accCMix L,MixView L t i := by
  intro i hi
  simp only [accCMix,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · exact L.measuredC_views hw t M hp _ (by simp [measuredCItems,negRot])
  · have st := sorted_static L hw (accCRaw L) (fun f hf => raw_static L hw f (Or.inr (Or.inr hf)))
    exact ⟨st.1,st.2,validC L hw t⟩

theorem acc_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMix L,MixStatic L i) ∧ (∀i∈accBMix L,MixStatic L i) ∧ (∀i∈accCMix L,MixStatic L i) := by
  let z : BasisState := fun _ => false
  have hz : regValue L.core.product z=0^2 := by
    simpa using (regValue_zero L.core.product z).mpr (fun _ _ => rfl)
  have conv (i : MixItem) (h : MixView L z i) : MixStatic L i := by
    cases i with
    | inl f => exact h.count
    | inr a => exact ⟨h.count,h.ok⟩
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
      resC ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleC L control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have result := withMixed_contribution L hw control hn L.core.sum L.core.product srcCount
    (fun _ => le_rfl) (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) false (accCMix L) s records hc hp0
    O (M^2) (resC (M^2) O) hO ho (by rw [hs])
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
      resC ((if s.basis control then A+B else 0)^2) O ∧
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
  simpa [accBranchC,middle,u,v,out,run_append,prepM] using final

theorem accProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (accProgram L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accProgram L control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accProgram L control) records s).basis q=s.basis q := by
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
  let restA := records.drop (measurementCount (accBranchA L control))
  let restB := restA.drop (measurementCount (accBranchB L control))
  let restC := restB.drop (measurementCount (accBranchC L control))
  let u := run (accBranchA L control) (records.take (measurementCount (accBranchA L control))) s
  let v := run (accBranchB L control) (restA.take (measurementCount (accBranchB L control))) u
  let w := run (accBranchC L control) (restB.take (measurementCount (accBranchC L control))) v
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
  have ea := accBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (accBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := accBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (accBranchB L control))) highU ea.2.1 productU cleanU
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
  have ec := accBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    (restB.take (measurementCount (accBranchC L control))) lowV sumV sumBound eb.2.1 productV cleanV
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
  simpa [accProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

theorem accPrefix_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (accPrefix L control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefix L control) records s).basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
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
  let OB := resB PB OA
  let OC := resC PC OB
  let restA := records.drop (measurementCount (accBranchA L control))
  let restB := restA.drop (measurementCount (accBranchB L control))
  let u := run (accBranchA L control) (records.take (measurementCount (accBranchA L control))) s
  let v := run (accBranchB L control) (restA.take (measurementCount (accBranchB L control))) u
  let w := run (accBranchC L control) restB v
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
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := accBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (accBranchB L control))) highU ea.2.1 productU cleanU
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
  have ec := accBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    restB lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have fullValue : regValue L.core.out w.basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    change SquareReduction.p-1-OC=_ at exactResult
    rw [ec.2.1]
    change OC=_
    omega
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      SquareReduction.p-1-(O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ec.1.trans (eb.1.trans ea.1),fullValue,sameW⟩
  simpa [accPrefix,u,v,w,restA,restB,enabled,run_append,Nat.add_assoc] using final

theorem acc_item_prices (L : CuccaroStreamedSquareWideLayout) :
    (mixFoldsT false (accAMix L)=4200 ∧ mixFoldsM false (accAMix L)=4200) ∧
    (mixFoldsT true (accBMix L)=13060 ∧ mixFoldsM true (accBMix L)=13060) ∧
    (mixFoldsT false (accCMix L)=3245 ∧ mixFoldsM false (accCMix L)=3245) := by
  norm_num [mixFoldsT,mixFoldsM,mixNeg,accAMix,accBMix,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildT]

theorem accProgram_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accProgram L control)=72600 ∧ measurementCount (accProgram L control)=72088 := by
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
    (mixFolds L false (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,su])
  have fa := mixFolds_counts L hw false (accAMix L) st.1
  have fb := mixFolds_counts L hw true (accBMix L) st.2.1
  have fc := mixFolds_counts L hw false (accCMix L) st.2.2
  have prices := acc_item_prices L
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
  have c := mixFolds_support L hw hn control false (accCMix L) st.2.2
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
    (mixFolds L false (accCMix L)) (by omega) (by omega) (by rw [hw.core.product,sum])
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
    wires_append,Finset.union_subset_iff] using And.intro (And.intro (And.intro sa sb)
      (And.intro (And.intro prep sc) unprep)) reflection

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
    (mixFolds_physical L hw nd false (accCMix L) st.2.2)
  have prep := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

theorem accProgram_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) : Challenge.gateSlots (accProgram L control) ≤ 5000000 := by
  have st := acc_static L hw
  have bd (items : List MixItem) (h : items=accAMix L ∨ items=accBMix L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMix,accBMix,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFolds_gateSlots L hw false (accAMix L) st.1 20 (bd _ (Or.inl rfl))
  have hb := mixFolds_gateSlots L hw true (accBMix L) st.2.1 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := mixFolds_gateSlots L hw false (accCMix L) st.2.2 20 (bd _ (Or.inr (Or.inr rfl)))
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
    (mixFolds L false (accCMix L)) (by rw [hw.core.product])
  have hp := Baselines.cuccaroAdd_gateSlots_le (L.core.low++[L.core.pad.getD 0 0]) L.core.sum L.core.cin
  have hl := L.core.low_length hw.core
  simp only [List.length_append, List.length_cons, List.length_nil, hl] at hp
  change Challenge.gateSlots L.core.prepareSum ≤ _ at hp
  have hr := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [accProgram,accBranchA,accBranchB,accBranchC,accMiddleC,
    CuccaroStreamedSquareLayout.clearSum, Challenge.gateSlots_append, Baselines.reverse_gateSlots]
  omega

theorem accPrefix_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    toffoliCount (accPrefix L control)=72345 ∧ measurementCount (accPrefix L control)=71833 := by
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
