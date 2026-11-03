import ECDSAAdd.Submission.Entrant.MainPart04
import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
import ECDSAAdd.Arithmetic.NativeFirstDirectValues
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ComparePhysical
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Baselines.SlotNativeFirst

set_option Elab.async false


/-! Exit-side merged tick.  On the image of the direct first tick it performs the last
reverse integer tick followed by the controlled constant negation
`x ↦ g ? (k - x mod p) : x` as one circuit: the threshold compare of the negation is read
from the tick word `H`, `H` is erased against `K` by a known-output adder, and one mapped
addition takes the complemented `K` word straight to `y/2`. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 1024

namespace ECDSAAdd.Entrant.ExitMerge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum E1Merge

/-! ### Arithmetic -/

/-- For `G`, `x > k` iff `¬ H < thrX`, where `H` is the tick word of `x`. -/
def thrX (k : Nat) (G par : Bool) : Nat :=
  if G then (if par then (k+1)/2+hConstant else (k+2)/2) else 0

/-- Constant added to the (complemented) `K` word to reach `y/2`. -/
def tkX (k : Nat) (G f par : Bool) : Nat :=
  if G then (kConstant false par+1+(k+(if f then p else 0)-par.toNat)/2)%2^258
  else (2^258-kConstant false par)%2^258

/-- Addend that takes the tick word `H` back to the low bits of `K`. -/
def dInv (par : Bool) : Nat := if par then 2^257-p else p

theorem pfacts : p%2=1 ∧ 2^255<p ∧ p<2^256 ∧ 2*hConstant=p+1 ∧ kConstant false false=p ∧
    kConstant false true+(p-1)/2=2^258 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · norm_num [p_val]
  · norm_num [p_val]
  · norm_num [p_val]
  · norm_num [hC_val,p_val]
  · norm_num [kC_val,p_val]
  · norm_num [kC_val,p_val]

theorem ymod (k X : Nat) (hk : k<p) (hX : X<p) : (k+p-X)%p=if k<X then k+p-X else k-X := by
  by_cases h : k<X
  · rw [if_pos h]; exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg h,Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega

set_option maxHeartbeats 1000000 in
theorem archX (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let f := G && decide (k<X)
    let Y := if G then (k+p-X)%p else X
    H<2^256 ∧ (dInv par+H)%2^257=K%2^257 ∧ f=(decide (H<thrX k G par) ^^ G) ∧
    ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 ∧ Y<p ∧
    decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) ∧
    f=decide ((if G then k else 2^256-1)<Y) := by
  intro par H K f Y
  obtain ⟨po,pg,pl,hc2,k0,k1⟩ := pfacts
  simp only [par,H,K,f,Y,thrX,tkX,dInv]
  simp only [ymod k X hk hX]
  rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;>
  rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
  cases G <;>
  by_cases hkx : k<X <;>
  simp only [hx,h2,hkx,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
    Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
    Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor,Bool.true_and,Bool.false_and,
    Bool.and_true,Bool.and_false,k0] <;>
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
  first
    | exact True.intro
    | omega
    | (simp only [decide_eq_true_iff,decide_eq_false_iff_not]; omega)
    | (apply Eq.symm; simp only [Bool.not_eq_eq_eq_not,Bool.not_true,Bool.not_false,
        decide_eq_true_iff,decide_eq_false_iff_not]; omega)

/-! ### Circuit -/

def thrXA (k : Nat) : Nat := (k+2)/2
def thrXB (k : Nat) : Nat := (k+2)/2 ^^^ ((k+1)/2+hConstant)

def loadTX (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrXA k)++maskedConstant (w 721) (tR w) (thrXB k)

def fPart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CCX g (w 1028) (w 721)]++loadTX w g k++
  compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)++[.CX g (w 514)]++loadTX w g k++
  [.CCX (w 514) (w 1028) (w 722)]

def dBitsX (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := p.testBit j
  let b := (2^257-p).testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def desiredX (w : Nat → Wire) : List MappedBit := mappedRead (wireBlock w 770 257) false

def knownH (w : Nat → Wire) : Program :=
  KnownOutputAdder.program (dBitsX w) (hpR w) (desiredX w) (hC2 w) (w 1797)

def eraseH (w : Nat → Wire) : Program :=
  [.CX (w 1028) (w 0),.X (w 0)]++knownH w++copyRegister none (wireBlock w 770 257) (hpR w)

def c1X (k : Nat) : Nat := tkX k false false false
def cgX (k : Nat) : Nat := tkX k true false false ^^^ tkX k false false false
def cfX (k : Nat) : Nat := tkX k true true false ^^^ tkX k true false false
def cpX (k : Nat) : Nat := tkX k false false true ^^^ tkX k false false false
def cgpX (k : Nat) : Nat :=
  tkX k true false true ^^^ tkX k true false false ^^^ tkX k false false true ^^^ tkX k false false false
def cfpX (k : Nat) : Nat :=
  tkX k true true true ^^^ tkX k true true false ^^^ tkX k true false true ^^^ tkX k true false false

def loadKX (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1X k)++maskedConstant g (hR w) (cgX k)++maskedConstant (w 514) (hR w) (cfX k)++
  maskedConstant (w 1028) (hR w) (cpX k)++maskedConstant (w 721) (hR w) (cgpX k)++
  maskedConstant (w 722) (hR w) (cfpX k)

def addPart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  FastConst.maskedNot g (kR w)++loadKX w g k++kAddM w++loadKX w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]]

def parBack (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]++
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]

def eraseF (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (2^256-1-k)++notRegister (tR w)++
  eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514)++
  notRegister (tR w)++maskedConstant g (tR w) (2^256-1-k)

/-- Last reverse tick and controlled negation `x ↦ g ? (k - x mod p) : x`, merged. -/
def program (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  fPart w g k++eraseH w++addPart w g k++rotateLeft (kR w)++parBack w g k++eraseF w g k

/-! ### Mapped constants -/

theorem selX (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

theorem dX_list (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := p.testBit j
      let b := (2^257-p).testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then (2^257-p).testBit j else p.testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selX]

def dXScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then (2^257-p).testBit j else p.testBit j).toNat+2*acc) 0

theorem dXScalar_value (par : Bool) : dXScalar par=dInv par := by
  cases par <;> decide

theorem dBitsX_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBitsX w) s=dInv (s (w 1028)) := by
  rw [dBitsX,dX_list]
  exact dXScalar_value (s (w 1028))

theorem dBitsX_length (w : Nat → Wire) : (dBitsX w).length=257 := by simp [dBitsX]

theorem dBitsX_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBitsX w)) : q=w 1028 := by
  simp only [dBitsX,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

theorem desiredX_value (w : Nat → Wire) (s : BasisState) :
    mappedValue (desiredX w) s=regValue (wireBlock w 770 257) s := by
  rw [desiredX,mappedRead_value]

theorem desiredX_length (w : Nat → Wire) : (desiredX w).length=257 := by
  simp [desiredX,mappedRead_length,wireBlock_length]

theorem tkX_lt (k : Nat) (G f par : Bool) : tkX k G f par<2^258 := by
  unfold tkX
  split_ifs <;> exact Nat.mod_lt _ (by norm_num)

theorem c1X_lt (k : Nat) : c1X k<2^258 := tkX_lt k _ _ _
theorem cgX_lt (k : Nat) : cgX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cfX_lt (k : Nat) : cfX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cpX_lt (k : Nat) : cpX k<2^258 := xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)
theorem cgpX_lt (k : Nat) : cgpX k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)
theorem cfpX_lt (k : Nat) : cfpX k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tkX_lt k _ _ _) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)) (tkX_lt k _ _ _)

def lkvX (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1X k ^^^ (if G then cgX k else 0) ^^^ (if f then cfX k else 0) ^^^ (if par then cpX k else 0) ^^^
    (if gp then cgpX k else 0) ^^^ (if fp then cfpX k else 0)

theorem lkvX_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkvX k G f par (G && par) (f && par)=tkX k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkvX,c1X,cgX,cfX,cpX,cgpX,cfpX,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltvX (k : Nat) (G gp : Bool) : Nat := (if G then thrXA k else 0) ^^^ (if gp then thrXB k else 0)

theorem ltvX_eq (k : Nat) (G par : Bool) : ltvX k G (G && par)=thrX k G par := by
  cases G <;> cases par <;> simp [ltvX,thrX,thrXA,thrXB,Nat.xor_assoc,Nat.xor_self]

/-! ### Steps -/

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCmpH (b0 : BasisState) (H b X T : Nat) (par gp fp : Bool) (hH : H<2^256) (hb : b<2)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*H+b) X T par false gp fp) (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514))
      (MF w b0 (2*H+b) X T par (decide (H<T)) gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC2 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 256 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC2 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have hpv0 : regValue (hpR w) s.basis=H := by
    cases hb0 : s.basis (w 0) <;> simp [hb0] at sp <;> omega
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    show regValue (wireBlock w 1 256) s.basis=H
    omega
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514) nd (by simp)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC2,tR,wireBlock_length]) s m c17 cl
  refine ⟨hp,?_⟩
  have := stepBit w hn b0 (2*H+b) X T par false gp fp s _ 514 (by omega) h he
  rw [hv,h.2.2.2.2.1,hpv,h.2.2.1] at this
  simpa [controlValue] using this

theorem stepFlagCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 514) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 514)] (MF w b0 H X T par (f ^^ cv) gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514)
    (s.basis (w 514) ^^ s.basis c)⟩ 514 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.2.1,hcv s.basis h] using this

theorem stepW0Back (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=
      ⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 _ X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,h.2.2.2.1]
    cases hb : s.basis (w 0) <;> cases par <;> simp [hb,writeBit] at sp ⊢ <;> omega

theorem stepKnownH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (hH : H<2^257)
    (hsum : (dInv par+H)%2^257=X%2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*H) X T par f gp fp) (knownH w) (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  unfold knownH
  intro s m h
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBitsX w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBitsX_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have dw : ∀q∈mappedWires (desiredX w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [desiredX,mappedRead_wires] at hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn i 1 257 (by omega) (by omega) (by omega),
      nb w hn i 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have b0' : s.basis (w 0)=false := by
    cases hb : s.basis (w 0)
    · rfl
    · simp [hb] at sp; omega
  have e0 : regValue (hpR w) s.basis=H := by rw [b0'] at sp; simp at sp; omega
  have kl := kR_low w hn s.basis
  rw [h.2.1] at kl
  have ll := regValue_lt (wireBlock w 770 257) s.basis
  simp only [wireBlock_length] at ll
  have klow : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
  have lhp : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  obtain ⟨hp,he,hval⟩ := KnownOutputAdder.program_correct (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
    nd srcw dw (by rw [dBitsX_length,lhp]) (by rw [desiredX_length,lhp]) (by simp [hC2,hpR,wireBlock_length])
    s m cl (by rw [desiredX_value,dBitsX_value,h.2.2.2.1,e0,c17,klow,lhp]; simpa using hsum.symm)
  refine ⟨hp,stepH w hn b0 (2*H) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp2 := hR_split w hn (run (KnownOutputAdder.program (dBitsX w) (hpR w) (desiredX w) (hC2 w) (w 1797)) m s).basis
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,desiredX_value,klow]
    simp

theorem stepCopyBack (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*(X%2^257)) X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 0 X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 _ X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=X%2^257 := by rw [b0'] at sp; simp at sp; omega
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [e0,this,b0',Nat.xor_self]; simp

theorem stepNegK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (hX : X<2^258)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (FastConst.maskedNot g (kR w))
      (MF w b0 H (if b0 g then 2^258-1-X else X) T par f gp fp) := by
  intro s m h
  have gk : g∉kR w := g_out w hn g hg 770 258 (by omega)
  have gv : s.basis g=b0 g := h.2.2.2.2.2.2.2 g (g_mut w g hn hg)
  rw [FastConst.maskedNot_run g (kR w) gk s m,gv]
  cases hb : b0 g
  · simp only [Bool.false_eq_true,if_false]
    exact ⟨by trivial,h⟩
  · simp only [if_true,eq_self_iff_true]
    rw [notRegister_correct (kR w) (kR_nd w hn)]
    refine ⟨rfl,stepK w hn b0 H X T par f gp fp s _ h ?_ _ ?_⟩
    · intro q hq
      show (if q∈kR w then _ else _)=_
      simp [hq]
    · change regValue (kR w) (fun q => if q∈kR w then !s.basis q else s.basis q)=_
      rw [regValue_congr (kR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
        regValue_complement,h.2.1]
      simp [kR,wireBlock_length]

theorem stepNotT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 H X T par f gp fp) (notRegister (tR w)) (MF w b0 H X (2^256-1-T) par f gp fp) := by
  intro s m h
  rw [notRegister_correct (tR w) (tR_nd w hn)]
  refine ⟨rfl,stepT w hn b0 H X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    show (if q∈tR w then _ else _)=_
    simp [hq]
  · change regValue (tR w) (fun q => if q∈tR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (tR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.2.2.1]
    simp [tR,wireBlock_length]

theorem stepRotL (b0 : BasisState) (H V T : Nat) (par f gp fp : Bool) (hV : 2*V<2^258) :
    Triple (MF w b0 H V T par f gp fp) (rotateLeft (kR w)) (MF w b0 H (2*V) T par f gp fp) := by
  intro s m h
  have r := rotateLeft_spec (kR w) (kR_nd w hn) V (by simpa [kR,wireBlock_length] using hV) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 H V T par f gp fp s _ h fr.2.2.2 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  exact this

theorem stepEraseF (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hX : X<2^256) (hf : f=decide (T<X)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(tR w++xR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1029 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (tR w++xR w).Nodup := List.nodup_append'.mpr ⟨tR_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (tR w++xR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1029 256 (by omega) (by omega) (by omega),
        nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1029 256 (by omega) (by omega) (by omega),nb w hn 1797 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have kx := kR_x w hn s.basis
  rw [h.2.1] at kx
  have xl := regValue_lt (xR w) s.basis
  simp only [xR,wireBlock_length] at xl
  have hxv : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      simp only [xR] at kx; omega
    simp only [xR] at kx ⊢; omega
  have r := eraseLtChain_correct (tR w) (xR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hxv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepLoadKX (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadKX w g k)
      (MF w b0 (H^^^lkvX k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1X k) (c1X_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cgX k) (cgX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cfX k) (cfX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cpX k) (cpX_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgpX k) (cgpX_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfpX k) (cfpX_lt k))))))
  unfold loadKX
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1X k^^^(if b0 g then cgX k else 0)^^^(if f then cfX k else 0)^^^(if par then cpX k else 0)^^^
      (if gp then cgpX k else 0)^^^(if fp then cfpX k else 0)=H^^^lkvX k (b0 g) f par gp fp := by
    simp only [lkvX,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadTX (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadTX w g k)
      (MF w b0 H X (T^^^ltvX k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrXA k<2^256 := by unfold thrXA; omega
  have lb' : (k+1)/2+hConstant<2^256 := by rw [hC_val]; omega
  have lb : thrXB k<2^256 := Nat.xor_lt_two_pow la lb'
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrXA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrXB k) lb)
  unfold loadTX
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltvX,Nat.xor_assoc] using h

theorem stepParBack (b0 : BasisState) (k V : Nat) (par f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 (2*V) 0 par f false false) (parBack w g k)
      (MF w b0 0 (2*V+(par ^^ (b0 g && decide (k%2=1)) ^^ f).toNat) 0 false f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have lb (b par' : Bool) : ∀s : BasisState,MF w b0 0 (2*V+b.toNat) 0 par' f false false s → s (w 770)=b := by
    intro s h; have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; cases b <;> simp <;> omega
  apply Triple.conseq (fun s h => by rw [show 2*V=2*V+(false).toNat by simp] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parBack,if_pos hk,if_pos hk]
    have t := (stepLowCX w hn b0 0 V 0 false par f false false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f false false (w 770) _ e1 (lb _ par)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      (stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : (((par ^^ (((false ^^ par) ^^ b0 g) ^^ f)) ^^ b0 g) ^^ f)=false := by
      cases par <;> cases b0 g <;> cases f <;> rfl
    rw [e] at h
    have e' : (((false ^^ par) ^^ b0 g) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h
  · rw [parBack,if_neg hk,if_neg hk]
    try simp only [List.nil_append,List.append_nil]
    have t := (stepLowCX w hn b0 0 V 0 false par f false false (w 1028) par e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 V 0 _ par f false false (w 514) f e4 (fun s h => h.2.2.2.2.1)).seq
      ((stepParCX w hn b0 0 _ 0 par f false false (w 770) _ e1 (lb _ par)).seq
      (stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    have e : ((par ^^ ((false ^^ par) ^^ f)) ^^ f)=false := by
      cases par <;> cases f <;> rfl
    rw [e] at h
    have e' : ((false ^^ par) ^^ f)=(par ^^ (b0 g && decide (k%2=1)) ^^ f) := by
      simp [hk]
    rw [e'] at h
    exact h

end Steps

/-! ### Composition -/

section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem program_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let par := decide (X%2=1)
    let H := X/2+(if par then hConstant else 0)
    let K := (X/2+kConstant false par)%2^258
    let Y := if G then (k+p-X)%p else X
    Triple (MF w b0 (2*H+(!par).toNat) K 0 par false false false) (program w g k)
      (MF w b0 0 Y 0 false false false false) := by
  intro G par H K Y
  obtain ⟨a1,a2,a3,a5,a6,a7,a8⟩ := archX k X hk hX G
  let f := G && decide (k<X)
  change H<2^256 at a1
  change (dInv par+H)%2^257=K%2^257 at a2
  change f=(decide (H<thrX k G par) ^^ G) at a3
  change ((if G then 2^258-1-K else K)+tkX k G f par)%2^258=Y/2 at a5
  change Y<p at a6
  change decide (Y%2=1)=(par ^^ (G && decide (k%2=1)) ^^ f) at a7
  change f=decide ((if G then k else 2^256-1)<Y) at a8
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hfg : f=true → G=true := by
    intro hf; simp only [f,Bool.and_eq_true] at hf; exact hf.1
  have hKlt : K<2^258 := Nat.mod_lt _ (by norm_num)
  have hpb : (!par).toNat<2 := Bool.toNat_lt _
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  -- threshold compare
  have s1 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par false false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s1
  have s2 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K 0 hk par false (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltvX_eq] at s2
  have s3 := stepCmpH w hn b0 H (!par).toNat K (thrX k G par) par (G && par) false a1 hpb hac h1797
  have s4 := stepFlagCX w hn b0 (2*H+(!par).toNat) K (thrX k G par) par (decide (H<thrX k G par))
    (G && par) false g G (g_ne w hn g hg 514 (by omega)) (fun s h => h.2.2.2.2.2.2.2 g gm)
  rw [←a3] at s4
  have s5 := stepLoadTX w g hn b0 k (2*H+(!par).toNat) K (thrX k G par) hk par f (G && par) false hg
  rw [show b0 g=G from rfl,ltvX_eq,Nat.xor_self] at s5
  have s6 := stepCCX w hn b0 (2*H+(!par).toNat) K 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s6
  -- erase the tick word
  have s7 := stepW0Back w hn b0 H K 0 par f (G && par) (f && par)
  have s8 := stepKnownH w hn b0 H K 0 par f (G && par) (f && par) (by omega) a2 hac h1797
  have s9 := stepCopyBack w hn b0 K 0 par f (G && par) (f && par)
  -- one mapped addition to `y/2`
  have s10 := stepNegK w g hn b0 0 K 0 par f (G && par) (f && par) hKlt hg
  have s11 := stepLoadKX w g hn b0 k 0 (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkvX_eq k G f par hfg] at s11
  have s12 := stepKAdd w hn b0 (tkX k G f par) (if G then 2^258-1-K else K) 0 par f (G && par) (f && par) hac h1797
  rw [show (tkX k G f par+(if G then 2^258-1-K else K))%2^258=Y/2 by rw [Nat.add_comm]; exact a5] at s12
  have s13 := stepLoadKX w g hn b0 k (tkX k G f par) (Y/2) 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkvX_eq k G f par hfg,Nat.xor_self] at s13
  have s14 := stepMeasFp w hn b0 0 (Y/2) 0 par f (G && par)
  have s15 := stepMeasGp w g hn b0 0 (Y/2) 0 par f false gm (g_ne w hn g hg 721 (by omega))
  -- rotate and parity
  have s16 := stepRotL w hn b0 0 (Y/2) 0 par f false false (by rw [p_val] at a6; omega)
  have s17 := stepParBack w g hn b0 k (Y/2) par f hg
  rw [show b0 g=G from rfl,←a7,show 2*(Y/2)+(decide (Y%2=1)).toNat=Y by
    rcases Nat.mod_two_eq_zero_or_one Y with hy|hy <;> simp [hy] <;> omega] at s17
  -- erase the flag
  have s18 := stepMaskT w hn b0 0 Y 0 false f false false g G gT (fun s h => h.2.2.2.2.2.2.2 g gm)
    (2^256-1-k) (by omega)
  have s19 := stepNotT w hn b0 0 Y (0^^^(if G then 2^256-1-k else 0)) false f false false
  have hT (G' : Bool) : 2^256-1-(0^^^(if G' then 2^256-1-k else 0))=(if G' then k else 2^256-1) := by
    rw [p_val] at hk; cases G' <;> simp <;> omega
  rw [hT G] at s19
  have s20 := stepEraseF w hn b0 0 Y (if G then k else 2^256-1) false f false false hac h1797
    (by rw [p_val] at a6; omega) a8
  have s21 := stepNotT w hn b0 0 Y (if G then k else 2^256-1) false false false false
  have s22 := stepMaskT w hn b0 0 Y (2^256-1-(if G then k else 2^256-1)) false false false false g G gT
    (fun s h => h.2.2.2.2.2.2.2 g gm) (2^256-1-k) (by omega)
  have hT2 (G' : Bool) : (2^256-1-(if G' then k else 2^256-1))^^^(if G' then 2^256-1-k else 0)=0 := by
    cases G' <;> simp [Nat.xor_self]
  rw [hT2 G] at s22
  have t := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq
    (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18.seq (s19.seq (s20.seq (s21.seq
    s22))))))))))))))))))))
  unfold program fPart eraseH addPart eraseF
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main

/-! ### Run on the image of the direct first tick -/

theorem mutL_pool (w : Nat → Wire) : ∀ q∈mutL w,q∈skywalkPoolWires w := by
  intro q hq
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h|h
  · exact blk_sub w 0 258 0 1798 (by omega) (by omega) q h
  · exact blk_sub w 770 258 0 1798 (by omega) (by omega) q h
  · exact blk_sub w 1029 256 0 1798 (by omega) (by omega) q h
  all_goals (subst h; exact List.mem_map.mpr ⟨_,by simp only [List.mem_range'_1]; omega,rfl⟩)

section Run
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- On the forward image of a clean seed holding `X`, the merged exit circuit restores the seed
except that the `K` block holds `g ? (k - X mod p) : X`; wires outside the pool are untouched. -/
theorem program_run (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (initial field : State) (mF m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 X initial.basis)
    (ht : regValue (tR w) initial.basis=0) (h514 : initial.basis (w 514)=false)
    (h721 : initial.basis (w 721)=false) (h722 : initial.basis (w 722)=false)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    (run (program w g k) m field).phase=initial.phase ∧
    regValue (kR w) (run (program w g k) m field).basis=(if field.basis g then (k+p-X)%p else X) ∧
    (∀q∈skywalkPoolWires w,q∉kR w → (run (program w g k) m field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w → (run (program w g k) m field).basis q=field.basis q) := by
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn X hX initial mF hin
  have e770 : initial.basis (w 770)=decide (X%2=1) := by
    have sp := kR_split w hn initial.basis
    have hb : regValue (kR w) initial.basis=X := hin.b
    rw [hb] at sp
    cases h : initial.basis (w 770) <;> simp [h] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  have inPool (a n : Nat) (ha : a+n≤1798) : ∀q∈wireBlock w a n,q∈skywalkPoolWires w :=
    blk_sub w a n 0 1798 (by omega) ha
  have wPool (i : Nat) (hi : i<1798) : w i∈skywalkPoolWires w :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have keepI (i : Nat) (hi : i < 1798) (h1 : 257 ≤ i) (h2 : i < 770 ∨ 1028 < i) :
      field.basis (w i)=initial.basis (w i) := by
    rw [hpool _ (wPool i hi)]
    apply zrest
    simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨nb w hn i 0 257 hi (by omega) (by omega),nb w hn i 770 258 hi (by omega) (by omega)⟩,
      w_ne w hn i 1028 hi (by omega) (by omega)⟩
  have hR0 : regValue (hR w) field.basis=
      2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat := by
    rw [regValue_congr (hR w) field.basis _ (fun q hq => hpool q (inPool 0 258 (by omega) q hq))]
    exact zh
  have kR0 : regValue (kR w) field.basis=(X/2+kConstant false (decide (X%2=1)))%2^258 := by
    rw [regValue_congr (kR w) field.basis _ (fun q hq => hpool q (inPool 770 258 (by omega) q hq))]
    exact zk
  have tR0 : regValue (tR w) field.basis=0 := by
    rw [regValue_congr (tR w) field.basis initial.basis (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact keepI i (by omega) (by omega) (by omega))]
    exact ht
  have f1028 : field.basis (w 1028)=decide (X%2=1) := (hpool _ (wPool 1028 (by omega))).trans z1028
  have f514 : field.basis (w 514)=false := (keepI 514 (by omega) (by omega) (by omega)).trans h514
  have f721 : field.basis (w 721)=false := (keepI 721 (by omega) (by omega) (by omega)).trans h721
  have f722 : field.basis (w 722)=false := (keepI 722 (by omega) (by omega) (by omega)).trans h722
  have hac : ∀q∈aC w,field.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [keepI i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp hin.carry _ hq
  have h1797 : field.basis (w 1797)=false := (keepI 1797 (by omega) (by omega) (by omega)).trans hin.cin
  have mf0 : MF w field.basis (2*(X/2+(if decide (X%2=1) then hConstant else 0))+(!decide (X%2=1)).toNat)
      ((X/2+kConstant false (decide (X%2=1)))%2^258) 0 (decide (X%2=1)) false false false field.basis :=
    ⟨hR0,kR0,tR0,f1028,f514,f721,f722,fun _ _ => rfl⟩
  obtain ⟨tp,o1,o2,o3,o4,o5,o6,o7,o8⟩ := program_triple w g hn hg k hk field.basis X hX hac h1797 field m mf0
  have outMut (q : Wire) (hq : q∉skywalkPoolWires w) : q∉mutL w := fun h => hq (mutL_pool w q h)
  refine ⟨tp.trans (hphase.trans zp),o2,?_,fun q hq => o8 q (outMut q hq)⟩
  intro q hq hk'
  by_cases qh : q∈hR w
  · rw [(regValue_zero _ _).mp o1 q qh]
    exact ((regValue_zero _ _).mp hin.a q qh).symm
  by_cases qt : q∈tR w
  · rw [(regValue_zero _ _).mp o3 q qt]
    exact ((regValue_zero _ _).mp ht q qt).symm
  by_cases q1 : q=w 1028
  · rw [q1,o4]; exact hin.one.symm
  by_cases q2 : q=w 514
  · rw [q2,o5]; exact h514.symm
  by_cases q3 : q=w 721
  · rw [q3,o6]; exact h721.symm
  by_cases q4 : q=w 722
  · rw [q4,o7]; exact h722.symm
  have nm : q∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,hk'⟩,qt⟩,q1,q2,q3,q4⟩
  rw [o8 q nm,hpool q hq]
  apply zrest
  simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),hk'⟩,q1⟩

end Run

/-! ### Resources -/

theorem program_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (program w g k)=770 ∧ measurementCount (program w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (tR w)
  have c1' := compareLt_counts none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC2,tR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have kh := KnownOutputAdder.program_counts (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
    (by rw [dBitsX_length]; simp [hpR,wireBlock_length]) (by rw [desiredX_length]; simp [hpR,wireBlock_length])
    (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (tR w) (xR w) (hC3 w) (w 1797) (w 514)
    (by simp [xR,tR,wireBlock_length]) (by simp [hC3,xR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pb : toffoliCount (parBack w g k)=0 ∧ measurementCount (parBack w g k)=0 := by
    unfold parBack; split_ifs <;> simp [toffoliCount,measurementCount]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  rw [lt] at c1'
  rw [lk] at k1
  rw [lh] at kh
  rw [lx] at e1
  simp only [program,fPart,eraseH,addPart,eraseF,loadTX,loadKX,knownH,kAddM,FastConst.maskedNot,
    toffoliCount_append,measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,
    n1.1,n1.2,c1'.1,c1'.2.1,r1.2.2.1,r1.2.2.2,k1.1,k1.2,kh.1,kh.2,e1.1,e1.2,cp1.1,cp1.2,pb.1,pb.2]
  simp [toffoliCount,measurementCount]

theorem program_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (program w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have notT : wires (notRegister (tR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 1029 256 (by omega))
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have ccx1 : wires [.CCX g (w 1028) (w 721)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl
    · exact G
    · exact I _ (by omega)
    · exact I _ (by omega)
  have ccx2 : wires [.CCX (w 514) (w 1028) (w 722)]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hT : wires (loadTX w g k)⊆(mSites w g).toFinset := by
    simp only [loadTX,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have cmp : wires (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514) (by simp [hp8,tR,wireBlock_length])
      (by simp [hC2,tR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 1797 (by omega)
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
  have hF : wires (fPart w g k)⊆(mSites w g).toFinset := by
    simp only [fPart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨ccx1,hT⟩,cmp⟩,cxg 514 (by omega)⟩,hT⟩,ccx2⟩
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hKn : wires (knownH w)⊆(mSites w g).toFinset := by
    apply (KnownOutputAdder.program_support _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with (((hq|hq)|hq)|hq)|rfl
    · rw [dBitsX_wire w q hq]; exact I 1028 (by omega)
    · rw [desiredX,mappedRead_wires] at hq; exact B 770 257 (by omega) q hq
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hE : wires (eraseH w)⊆(mSites w g).toFinset := by
    simp only [eraseH,wires_append,Finset.union_subset_iff]
    exact ⟨⟨hW,hKn⟩,hCp⟩
  have hNeg : wires (FastConst.maskedNot g (kR w))⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (kR w) _).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 770 258 (by omega) q hq))
  have hL : wires (loadKX w g k)⊆(mSites w g).toFinset := by
    simp only [loadKX,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hK : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hM : wires ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)⊆
      (mSites w g).toFinset := by
    rw [show ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] : Program)=
      [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++[.measureX (w 721) [] [.CZ g (w 1028)]] from rfl,
      wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
        Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hA : wires (addPart w g k)⊆(mSites w g).toFinset := by
    simp only [addPart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨hNeg,hL⟩,hK⟩,hL⟩,hM⟩
  have hRot : wires (rotateLeft (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).2]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hP : wires (parBack w g k)⊆(mSites w g).toFinset := by
    unfold parBack
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hEr : wires (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1029 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hEF : wires (eraseF w g k)⊆(mSites w g).toFinset := by
    simp only [eraseF,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskT g G _,notT⟩,hEr⟩,notT⟩,mskT g G _⟩
  simp only [program,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨hF,hE⟩,hA⟩,hRot⟩,hP⟩,hEF⟩

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem program_physical (k : Nat) : GatePhysical (program w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gK : g∉kR w := g_out w hn g hg 770 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 1 256 1540 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 1029 256 1540 256 (by omega) (by omega) (by omega)
      have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
      have l2 : (hp8 w++tR w++hC2 w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 1540 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 1797 (by omega) (by omega) (by omega),nb w hn 514 1 256 (by omega) (by omega) (by omega),
          nb w hn 514 1029 256 (by omega) (by omega) (by omega),nb w hn 514 1540 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega),
          nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · simp
  have khP : GatePhysical (knownH w) := by
    unfold knownH
    apply KnownOutputAdder.program_physical
    · rw [dBitsX_length]; simp [hpR,wireBlock_length]
    · rw [desiredX_length]; simp [hpR,wireBlock_length]
    · simp [hC2,hpR,wireBlock_length]
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBitsX w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBitsX_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [desiredX,mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq'
      simp only [List.mem_range'_1] at hi
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne i 1797 (by omega) (by omega) (by omega),nb w hn i 1 257 (by omega) (by omega) (by omega),
        nb w hn i 1540 256 (by omega) (by omega) (by omega)⟩
  have kP : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have eP : GatePhysical (eraseLtChain (tR w) (xR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1029 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (tR w++xR w).Nodup := List.nodup_append'.mpr ⟨tR_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (tR w++xR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1029 256 (by omega) (by omega) (by omega),nb w hn 1797 770 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parBack w g k) := by
    unfold parBack
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).2
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h721 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h722 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t721 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadKX w g k) := by
    simp only [loadKX,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h721⟩,maskedConstant_physical _ _ _ h722⟩
  have ltP : GatePhysical (loadTX w g k) := by
    simp only [loadTX,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t721⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have mP : GatePhysical ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],.measureX (w 721) [] [.CZ g (w 1028)]] :
      Program) := by
    simp [GatePhysical,PhysicalInstr]
  have fP : GatePhysical (fPart w g k) := by
    simp only [fPart,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),ltP⟩,cmpP⟩,
      cxp _ _ (gn _ (by omega))⟩,ltP⟩,
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have eHP : GatePhysical (eraseH w) := by
    simp only [eraseH,gatePhysical_append]
    exact ⟨⟨w0P,khP⟩,cpP⟩
  have aP : GatePhysical (addPart w g k) := by
    simp only [addPart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gK,lkP⟩,kP⟩,lkP⟩,mP⟩
  have eFP : GatePhysical (eraseF w g k) := by
    simp only [eraseF,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gT,notRegister_physical _⟩,eP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gT⟩
  simp only [program,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨fP,eHP⟩,aP⟩,rotP⟩,parP⟩,eFP⟩

end Phys

theorem program_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (program w g k)≤22000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (hp8 w) (tR w) (hC2 w) (w 1797) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).2
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.knownAdder_gateSlots_le (dBitsX w) (desiredX w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (tR w) (xR w) (hC3 w) (w 1797) (w 514)
  have pb : Challenge.gateSlots (parBack w g k)≤6 := by
    unfold parBack; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g1 : Challenge.gateSlots [.CCX g (w 1028) (w 721)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g2 : Challenge.gateSlots [.CCX (w 514) (w 1028) (w 722)]=1 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have g3 : Challenge.gateSlots [.CX g (w 514)]=1 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots ([.measureX (w 722) [] [.CZ (w 514) (w 1028)],
      .measureX (w 721) [] [.CZ g (w 1028)]] : Program)=4 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadKX w g k)≤6*258 := by
    simp only [loadKX,Challenge.gateSlots_append]
    have := x1 (hR w) (c1X k); have := m1 g (hR w) (cgX k); have := m1 (w 514) (hR w) (cfX k)
    have := m1 (w 1028) (hR w) (cpX k); have := m1 (w 721) (hR w) (cgpX k); have := m1 (w 722) (hR w) (cfpX k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadTX w g k)≤2*256 := by
    simp only [loadTX,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrXA k); have := m1 (w 721) (tR w) (thrXB k)
    simp only [tR,wireBlock_length] at *
    omega
  have nT : Challenge.gateSlots (notRegister (tR w))=256 := by
    simp [Baselines.notRegister_gateSlots,tR,wireBlock_length]
  have mT : Challenge.gateSlots (maskedConstant g (tR w) (2^256-1-k))≤256 := by
    have := m1 g (tR w) (2^256-1-k); simpa [tR,wireBlock_length] using this
  have mK : Challenge.gateSlots (FastConst.maskedNot g (kR w))≤258 := by
    have := m1 g (kR w) (2^(kR w).length-1); simpa [FastConst.maskedNot,kR,wireBlock_length] using this
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lp : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBitsX_length] at h1
  rw [lt] at e1
  rw [lp,lt] at c1'
  simp only [program,fPart,eraseH,addPart,eraseF,knownH,kAddM,Challenge.gateSlots_append,g1,g2,g3,w0,q1,cp,nT]
  omega

end ECDSAAdd.Entrant.ExitMerge
