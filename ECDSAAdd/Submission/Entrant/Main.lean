import ECDSAAdd.Submission.Entrant.JointEntry
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
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Baselines.SlotNativeFirst


section E1MergedComponent

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1Merge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to `x>>1` to obtain the first-tick `K` word directly. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then (if G then (kConstant false par+2^258-(p+par.toNat-(x0 k G f par).toNat-k)/2)%2^258 else 0)
  else if G then (kConstant false par+((x0 k G f par).toNat+k-par.toNat)/2)%2^258
  else kConstant false par

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X := Nat.mod_eq_of_lt (by omega)
    have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-0<X)=false := by
      simp only [decide_eq_false_iff_not]; omega
    simp only [if_false,Bool.false_eq_true,e1,e2,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one X with h|h <;>
    simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
      Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
    exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : 115792089237316195423570985008687907853269984665640564039457584007908834671663≤X+k
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
        rw [Nat.mod_eq_sub_mod hf,Nat.mod_eq_of_lt (by omega)]
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=true := by
        simp only [decide_eq_true_iff]; omega
      simp only [e1,e2,Bool.xor_true]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=false := by
        simp only [decide_eq_false_iff_not]; omega
      simp only [e1,e2,Bool.xor_false]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) (cmpC+k)++notRegister (srcR w)++
  compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)++
  notRegister (srcR w)++maskedConstant g (srcR w) (cmpC+k)

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Compare-first constant addition `x ↦ x + g·k mod p` merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++kAddM w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddM w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (S<X))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(srcR w++xR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (srcR w++xR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨w514_src w hn,nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨n513,nb w hn 513 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (srcR w) (xR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : cmpC+k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (2^256-1-(if b0 g then cmpC+k else 0)<X))) := by
  have t := ((((cfMask w hn b0 0 F g gs g514 (cmpC+k) hk).seq
    (cfNot w hn b0 _ F)).seq (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfNot w hn b0 _ _)).seq (cfMask w hn b0 _ _ g gs g514 (cmpC+k) hk)
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have lt : (if b0 g then cmpC+k else 0)<2^256 := by split <;> omega
  refine ⟨?_,?_,h.2.2⟩
  · rw [h.1]
    have e : 2^256-1-(2^256-1-(0^^^(if b0 g then cmpC+k else 0)))=(if b0 g then cmpC+k else 0) := by
      simp only [Nat.zero_xor]; omega
    rw [e,Nat.xor_self]
  · rw [h.2.1]; simp only [Nat.zero_xor]

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : cmpC+k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (2^256-1-(if b0 g then cmpC+k else 0)<X)) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · exact kC_lt par

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have s6 := stepKAdd w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
  rw [show (tk k G f par+X/2)%2^258=K by rw [Nat.add_comm]; exact a2] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAdd w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The merged circuit leaves exactly the state of the old compare-first constant addition
followed by the direct first tick, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
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
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
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
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
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
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,hP,hR'⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hH⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1026 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  rw [lh] at h1
  rw [lt] at e1
  simp only [merged,comparePart,prodPart,loadK,kAddM,hAddM,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,k1.1,k1.2,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
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
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
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
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,parP,rotP⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hP⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBits_length] at h1
  rw [lh] at e1
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,kAddM,hAddM]
  omega

end ECDSAAdd.Entrant.E1Merge


end E1MergedComponent

namespace ECDSAAdd.Entrant.SquareAQ
def offset : Nat := 2^163-1
end ECDSAAdd.Entrant.SquareAQ

namespace ECDSAAdd.Entrant.EntryFuseQ5
abbrev kernelQS := OwnEntryFuseQ5.kernel5S
end ECDSAAdd.Entrant.EntryFuseQ5

section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport BalancedField
  History5 EntryFuse
attribute [local irreducible] run wires History5.allEncode

/-- A half-centered field frame and a canonical frame agree outside the target. -/
theorem encoded_pair5 (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Z : Fp) (t a : State)
    (half : History5.EncodedFieldFrame5 base (base 2409) origin (Z/2) 0 t)
    (canon : History5.EncodedCanonicalFrame5 origin Z 0 a) :
    regValue (wireBlock base 2056 256) t.basis=centerWord (Z/2) ∧
      ∀q,q∉wireBlock base 2056 256 → t.basis q=a.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let R := (balancedSharedPorts base (base 2409)).r
  let W := (balancedSharedPorts base (base 2409)).y
  have rEq : R=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
  have wEq : W=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)
  have split : (skywalkSharedField base).z=R++[base 2312] ∧
      (skywalkSharedField base).a=W++[base 1026] := by
    rw [skywalkShared_field_z,rEq,wEq]
    constructor
    · have h := wireBlock_append base 2056 256 1
      simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using h.symm
    · have h := wireBlock_append base 770 256 1
      simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using h.symm
  obtain ⟨rawT,_,halfFrame,encodedT⟩ := half
  obtain ⟨rawA,_,canonicalFrame,encodedA⟩ := canon
  rw [split.1,split.2,ZMod.val_zero] at canonicalFrame
  have zBound : Z.val<2^256 := (ZMod.val_lt Z).trans (by norm_num [p])
  have canonicalNarrow := balancedPair_narrow R W (base 2312) (base 1026) origin rawA.basis Z.val 0
    (by rw [rEq,wireBlock_length]; exact zBound) (by rw [wEq,wireBlock_length]; norm_num)
    canonicalFrame hr hy
  change PairFrame R W origin (centerWord (Z/2)) (centerWord 0) rawT.basis at halfFrame
  rw [HalfField.centerWord_zero] at halfFrame
  have rawSame (q : Wire) (hq : q∉R) : rawT.basis q=rawA.basis q := by
    by_cases hW : q∈W
    · exact regValue_equal_bits W _ _ (halfFrame.2.1.trans canonicalNarrow.2.1.symm) q hW
    · exact (halfFrame.2.2 q hq hW).trans (canonicalNarrow.2.2 q hq hW).symm
  have support := HalfField5.encoder_pool_support
  have away (q : Wire) (hq : q∈wires (History5.allEncode base 102)) : q∉R := by
    rw [rEq]
    exact pool_away q (List.mem_toFinset.mp (support hq))
  have reads : ∀q∈wires (History5.allEncode base 102),rawT.basis q=rawA.basis q := by
    intro q hq
    exact rawSame q (away q hq)
  have inc := run_local_increment (History5.allEncode base 102) rawT rawA [] reads
  constructor
  · rw [←rEq,encodedT]
    apply (regValue_congr _ _ _ ?_).trans halfFrame.1
    intro q hq
    exact run_preserves_outside _ [] rawT q (fun used => away q used hq)
  · intro q hq
    rw [encodedT,encodedA]
    by_cases used : q∈wires (History5.allEncode base 102)
    · exact inc.2 q used
    · rw [run_preserves_outside _ [] rawT q used,run_preserves_outside _ [] rawA q used]
      exact rawSame q (by simpa only [rEq] using hq)

end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
  CompressedFieldSupport OffsetBorrowedCanonical History5 EntryFuse LaneI
attribute [local irreducible] run wires OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT OneBankReplay5.replay

def exitSegment5 : Program :=
  OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ OneBankReplay5.replay false)

private theorem run_three_states (a b c : Program) (P : State → State → Prop)
    (h : ∀(s s1 s2 s3 : State) (m1 m2 m3 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → P s s3)
    (s : State) (m : List Bool) : P s (run (a++(b++c)) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ rfl rfl rfl

theorem exitSegment5_spec (origin : BasisState) (ctx : OneBankReplay5.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let out := run exitSegment5 m s
    out.phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin (fieldResult false origin x Y/2) 0 out := by
  let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ FieldFrameOB5.EncodedFieldFrame origin (fieldResult false origin x Y/2) 0 out
  have all := run_three_states OwnQ5Endpoint.centerT HalfFieldOB5.copyN (OneBankReplay5.replay false) P (by
    intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
    have c1 := OwnQ5Endpoint.center_frame ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal ctx.parity ha
      Y initial m1 hin
    rw [h1] at c1
    have c2 := HalfFieldOB5.copy_fill ctx.hn origin (Y/2) s1 m2 c1.2
    rw [h2] at c2
    have c3 := OneBankReplay5.inverse_frame origin ctx x hx0 hx trace (Y/2) s2 m3 c2.2
    rw [h3] at c3
    have eq : (if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y/2 := by
      unfold fieldResult
      split <;> simp [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    refine ⟨c3.1.trans (c2.1.trans c1.1),?_⟩
    rw [←eq]
    exact c3.2) s m
  exact all input

theorem placed_frame_pair5 (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Z : Fp) (t old : State)
    (newer : FieldFrameOB5.EncodedFieldFrame origin (Z/2) 0 t)
    (older : FieldFrameOB5.EncodedCanonicalFrame origin Z 0 old)
    (phase : t.phase=old.phase) :
    t.phase=old.phase ∧ regValue (wireBlock base 2056 256) t.basis=centerWord (Z/2) ∧
      ∀q,q∉wireBlock base 2056 256 → t.basis q=old.basis q := by
  have pair := encoded_pair5 hn origin hr hy Z (pullState (OB5.sig 511) t)
    (pullState (OB5.sig 511) old) newer older
  have value : regValue (wireBlock base 2056 256) t.basis=centerWord (Z/2) := by
    apply (regValue_congr _ _ _ ?_).trans pair.1
    intro q hq
    change t.basis q=t.basis (OB5.sig 511 q)
    rw [sig_num_fix q hq]
  have same (q : Wire) (hq : q∉wireBlock base 2056 256) : t.basis q=old.basis q := by
    have h := pair.2 (OB5.sig 511 q) (sig_num_away q hq)
    change t.basis (OB5.sig 511 (OB5.sig 511 q))=
      old.basis (OB5.sig 511 (OB5.sig 511 q)) at h
    simpa only [OB5.sig_invol 511 (by decide)] using h
  exact ⟨phase,value,same⟩

theorem instr_prefix (P Q : Program) : InstrSub P (P++Q) := by
  constructor
  · intro i hi
    exact Or.inl (List.mem_append_left _ hi)
  · rw [Challenge.gateSlots_append]
    omega

theorem exitSegment5_sub : InstrSub exitSegment5 (SegmentOB5.program false) := by
  have h := (InstrSub.refl OwnQ5Endpoint.centerT).append
    ((InstrSub.refl HalfFieldOB5.copyN).append
      (instr_prefix (OneBankReplay5.replay false) OwnQ5Endpoint.canonT))
  simpa only [exitSegment5,SegmentOB5.program,Bool.false_eq_true,if_false] using h


end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires compactForward5 compactReverse5 W.compactForward5 OB5.forward OB5.reverse
  skywalkArithmeticClear NativeFirstDirect.forward NativeFirstKnown.inverse
  OneBankReplay5.replay OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT exitSegment5 SegmentOB5.program

def hostExitSegment5 : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap exitSegment5 ++ [.X (base 511)])

def exitKernel5 : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostExitSegment5 ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

attribute [local irreducible] exitKernel5 hostExitSegment5

theorem reverse_pool5 : wires (stackReverseT)⊆(skywalkPoolWires base).toFinset := by
  apply stackReverseT_subset.trans
  apply StackOB5.reverse_support.trans
  intro q hq
  obtain ⟨i,rfl,hi⟩ := (OB5.integerSites_mem q).mp hq
  apply List.mem_toFinset.mpr
  exact arith_mem base 0 1798 i (by omega) (by omega)

theorem inverse_pool5 : wires (NativeFirstKnown.inverse base)⊆(skywalkPoolWires base).toFinset := by
  have last := NativeFirstKnown.inverse_support base
  apply last.trans
  intro q hq
  exact List.mem_toFinset.mpr (NativeFirstDirect.prefix_pool_subset base (List.mem_toFinset.mp hq))

theorem exitUnhosted_field_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (v1 v2 v3 v4 a4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 s=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run exitSegment5 m4 v3=v4)
    (hOld : run (SegmentOB5.program false) [] v3=a4) :
    v4.phase=a4.phase ∧
      regValue (wireBlock base 2056 256) v4.basis=
        centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → v4.basis q=a4.basis q := by
  let t2 := run (compactForward5 base 1 511) m2 v1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [h1] at first
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ v1.basis).mpr first
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 v1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp gap hx cop v1 m2 m2 first
  have e2 : v2=pullState (OB5.sig 511) t2 := by
    rw [←h2,stackForwardT_run hn hlo x hx0 hx v1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx v1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : v3=pullState (OB5.sig 511) t3 := by rw [←h3,e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin v1 t2 t3 h1 rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have ctx : OneBankReplay5.Context origin.basis := ⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 v3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) v3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  let Z := fieldResult false origin.basis x Y
  have newer := exitSegment5_spec origin.basis ctx facts.sourceZero x hx0 hx facts.trace Y v3 m4 placedInput
  rw [h4] at newer
  have older := SegmentOB5.program_spec false hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y v3 [] placedInput
  change v4.phase=v3.phase ∧ FieldFrameOB5.EncodedFieldFrame origin.basis (Z/2) 0 v4 at newer
  rw [hOld] at older
  change a4.phase=v3.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin.basis Z 0 a4 at older
  have fieldPair := placed_frame_pair5 hn origin.basis facts.targetHigh facts.sourceHigh Z v4 a4
    newer.2 older.2 (newer.1.trans older.1.symm)
  have result : Z=directSkywalkResult false (s.basis (base 2400)) x Y := by
    simp only [Z,fieldResult,directSkywalkResult,skywalkArithmeticResult,facts.controls (base 2400) (by simp)]
  rw [result] at fieldPair
  exact fieldPair



theorem exitKernel5_field_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (v1 v2 v3 v4 a4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 s=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostExitSegment5 m4 v3=v4)
    (hOld : run (KernelOB5.segH false) [] v3=a4) :
    v4.phase=a4.phase ∧
      regValue (wireBlock base 2056 256) v4.basis=
        centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → v4.basis q=a4.basis q := by
  let v4' := run exitSegment5 m4 v3
  let a4' := run (SegmentOB5.program false) [] v3
  have unPair := exitUnhosted_field_state hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 hin hg0 hs0
    v1 v2 v3 v4' a4' h1 h2 h3 rfl rfl
  let t2 := run (compactForward5 base 1 511) m2 v1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [h1] at first
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ v1.basis).mpr first
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 v1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp gap hx cop v1 m2 m2 first
  have e2 : v2=pullState (OB5.sig 511) t2 := by
    rw [←h2,stackForwardT_run hn hlo x hx0 hx v1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx v1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : v3=pullState (OB5.sig 511) t3 := by rw [←h3,e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin v1 t2 t3 h1 rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 v3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) v3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have fresh := SegmentOB5.program_spec false hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y v3 [] placedInput
  have ins := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y v3 placedInput
  have outs := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero _ _ fresh.2
  have hostBits := encoded_host_bits5 x hx0 hx origin t3 v3 facts.trace encEq e3
  have away (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 := by
    intro mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have e := base_injective eq
    omega
  have outQ2409 : v4'.basis (base 2409)=false :=
    (unPair.2.2 _ (away 2409 (by omega))).trans outs.1
  have outQ2410 : v4'.basis (base 2410)=false :=
    (unPair.2.2 _ (away 2410 (by omega))).trans outs.2
  have freeP := KernelOB5.seg_free false
  have freeQ511 : base 511∉wires exitSegment5 := fun h => freeP.1 (exitSegment5_sub.wires_sub h)
  have freeQ1542 : base 1542∉wires exitSegment5 := fun h => freeP.2 (exitSegment5_sub.wires_sub h)
  have oldEq := HostOB5.hosted_run (SegmentOB5.program false) v3 [] freeP.1 freeP.2
    ins.1 hostBits.1 ins.2 hostBits.2 outs.1 outs.2
  have newEq := HostOB5.hosted_run exitSegment5 v3 m4 freeQ511 freeQ1542
    ins.1 hostBits.1 ins.2 hostBits.2 outQ2409 outQ2410
  have oldState : a4=a4' := by
    rw [←hOld]
    exact oldEq
  have newState : v4=v4' := by
    rw [←h4]
    simpa only [hostExitSegment5] using newEq
  rw [newState,oldState]
  exact unPair

theorem suffix_transport5 (A B C : Program)
    (ha : wires A⊆(skywalkPoolWires base).toFinset)
    (hb : wires B⊆(skywalkPoolWires base).toFinset)
    (hc : wires C⊆(skywalkPoolWires base).toFinset)
    (s a4 v4 : State) (m5 m6 m7 : List Bool) (v5 v6 v7 : State)
    (h5 : run A m5 v4=v5) (h6 : run B m6 v5=v6) (h7 : run C m7 v6=v7)
    (V : Nat)
    (fieldPair : v4.phase=a4.phase ∧ regValue (wireBlock base 2056 256) v4.basis=V ∧
      ∀q,q∉wireBlock base 2056 256 → v4.basis q=a4.basis q)
    (oldPhase : (run C m7 (run B m6 (run A m5 a4))).phase=s.phase)
    (oldRest : ∀q,q∉wireBlock base 2056 256 →
      (run C m7 (run B m6 (run A m5 a4))).basis q=s.basis q) :
    v7.phase=s.phase ∧ regValue (wireBlock base 2056 256) v7.basis=V ∧
      ∀q,q∉wireBlock base 2056 256 → v7.basis q=s.basis q := by
  have paired := pool_three A B C ha hb hc a4 v4 m5 m6 m7
    fieldPair.1.symm (fun q hq => (fieldPair.2.2 q hq).symm) v5 v6 v7 h5 h6 h7
  dsimp only at paired
  refine ⟨paired.1.symm.trans oldPhase,?_,?_⟩
  · exact (regValue_congr _ _ _ paired.2.2).trans fieldPair.2.1
  · intro q hq
    exact (paired.2.1 q hq).symm.trans (oldRest q hq)

theorem exitKernel5_states
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (v1 v2 v3 v4 v5 v6 v7 a4 a5 a6 a7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 s=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostExitSegment5 m4 v3=v4)
    (h5 : run (skywalkArithmeticClear base) m5 v4=v5)
    (h6 : run (stackReverseT) m6 v5=v6)
    (h7 : run (NativeFirstKnown.inverse base) m7 v6=v7)
    (h4a : run (KernelOB5.segH false) [] v3=a4)
    (h5a : run (skywalkArithmeticClear base) m5 a4=a5)
    (h6a : run (stackReverseT) m6 a5=a6)
    (h7a : run (NativeFirstKnown.inverse base) m7 a6=a7) :
    v7.phase=s.phase ∧
      regValue (wireBlock base 2056 256) v7.basis=
        centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → v7.basis q=s.basis q := by
  have fieldPair := exitKernel5_field_state hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 hin hg0 hs0
    v1 v2 v3 v4 a4 h1 h2 h3 h4 h4a
  have strong := KernelOB5.program_states false hn hlo ho hf x Y hx0 hx s m1 m2 m3 [] m5 m6 m7
    hin hg0 hs0 v1 v2 v3 a4 a5 a6 a7 h1 h2 h3 h4a h5a h6a h7a
  unfold DirectSkywalkArithmeticStrong at strong
  have oldPhase : (run (NativeFirstKnown.inverse base) m7
      (run (stackReverseT) m6 (run (skywalkArithmeticClear base) m5 a4))).phase=s.phase := by
    rw [h5a,h6a,h7a]
    exact strong.1
  have oldRest : ∀q,q∉wireBlock base 2056 256 →
      (run (NativeFirstKnown.inverse base) m7
        (run (stackReverseT) m6 (run (skywalkArithmeticClear base) m5 a4))).basis q=s.basis q := by
    rw [h5a,h6a,h7a]
    exact strong.2.2
  exact suffix_transport5 (skywalkArithmeticClear base) (stackReverseT)
    (NativeFirstKnown.inverse base) clear_pool5 reverse_pool5 inverse_pool5 s a4 v4 m5 m6 m7
    v5 v6 v7 h5 h6 h7 _ fieldPair oldPhase oldRest

theorem exitKernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let v := run exitKernel5 m s
    v.phase=s.phase ∧ regValue (wireBlock base 2056 256) v.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → v.basis q=s.basis q := by
  let P : State → State → Prop := fun initial out => initial=s →
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) hostExitSegment5 (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 eq
      subst eq
      let a4 := run (KernelOB5.segH false) [] v3
      let a5 := run (skywalkArithmeticClear base) m5 a4
      let a6 := run (stackReverseT) m6 a5
      let a7 := run (NativeFirstKnown.inverse base) m7 a6
      exact exitKernel5_states hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 v1 v2 v3 v4 v5 v6 v7 a4 a5 a6 a7 h1 h2 h3 h4 h5 h6 h7 rfl rfl rfl rfl) s m
  simpa only [exitKernel5,List.append_assoc] using all rfl

end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse LaneI
attribute [local irreducible] run wires toffoliCount measurementCount

theorem hostExitSegment5_sub : InstrSub hostExitSegment5 (KernelOB5.segH false) := by
  have h := (InstrSub.refl [.X (base 511)]).append
    ((exitSegment5_sub.rename HostOB5.hostSwap).append (InstrSub.refl [.X (base 511)]))
  simpa only [hostExitSegment5,KernelOB5.segH] using h

theorem exitKernel5_sub : InstrSub exitKernel5 (KernelOB5.program false) := by
  have h := ((((((InstrSub.refl (NativeFirstDirect.forward base)).append
    (InstrSub.refl (stackForwardT))).append
    (InstrSub.refl (skywalkArithmeticClear base))).append hostExitSegment5_sub).append
    (InstrSub.refl (skywalkArithmeticClear base))).append
    (InstrSub.refl (stackReverseT))).append
    (InstrSub.refl (NativeFirstKnown.inverse base))
  simpa only [exitKernel5,KernelOB5.program] using h

theorem exitKernel5_support : wires exitKernel5⊆OB5Support.logicalSites :=
  exitKernel5_sub.wires_sub.trans (KernelOB5.program_support_logical false)

theorem exitKernel5_physical : GatePhysical exitKernel5 :=
  exitKernel5_sub.physical (KernelOB5.program_physical false)

theorem exitKernel5_gateSlots_le : Challenge.gateSlots exitKernel5≤20500006 :=
  exitKernel5_sub.slots.trans (KernelOB5.program_gateSlots_le false)

theorem exitKernel5_counts :
    toffoliCount exitKernel5=1048872 ∧ measurementCount exitKernel5=721023 := by
  have old := KernelOB5.program_counts false
  have cv := OwnQ5Endpoint.endpoint_counts
  have renNew := renameProgram_counts HostOB5.hostSwap exitSegment5
  have renOld := renameProgram_counts HostOB5.hostSwap (SegmentOB5.program false)
  have x : toffoliCount [.X (base 511)]=0 ∧ measurementCount [.X (base 511)]=0 := by
    simp [toffoliCount,measurementCount]
  simp only [KernelOB5.program,KernelOB5.segH,toffoliCount_append,measurementCount_append,
    renOld.1,renOld.2,x.1,x.2] at old
  simp only [SegmentOB5.program,Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,
    cv.2.2.1,cv.2.2.2] at old
  simp only [exitKernel5,hostExitSegment5,toffoliCount_append,measurementCount_append,
    renNew.1,renNew.2,x.1,x.2]
  simp only [exitSegment5,toffoliCount_append,measurementCount_append]
  omega

end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires toffoliCount measurementCount

def exitSegment5S : Program := OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ SW.replayS false)
def hostExitSegment5S : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap exitSegment5S ++ [.X (base 511)])
def exitKernel5S : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostExitSegment5S ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem selExitSegment5 : SW.Sel (base 2400) 1020 exitSegment5S exitSegment5 := by
  have away := SW.selCenter_away
  have replay := SW.selReplay_sel false
  have fix : OwnPlusEndpoint.swap (base 2400)=base 2400 := by decide +kernel
  have plusAway : base 2400∉wires OwnPlusEndpoint.centerT :=
    OwnPlusHost.rename_avoid OwnPlusEndpoint.swap _ HalfFieldOB5.centerT fix away.1
  have fixGuard : OwnGuardEndpoint.swap (base 2400)=base 2400 := by decide +kernel
  have guardAway : base 2400∉wires OwnGuardEndpoint.centerT :=
    OwnPlusHost.rename_avoid OwnGuardEndpoint.swap _ OwnPlusEndpoint.centerT fixGuard plusAway
  have fixQ4 : OwnQ4Endpoint.swap (base 2400)=base 2400 := by decide +kernel
  have q4Away : base 2400∉wires OwnQ4Endpoint.centerT :=
    OwnPlusHost.rename_avoid OwnQ4Endpoint.swap _ OwnGuardEndpoint.centerT fixQ4 guardAway
  have fixQ5 : OwnQ5Endpoint.swap (base 2400)=base 2400 := by decide +kernel
  have centerAway : base 2400∉wires OwnQ5Endpoint.centerT :=
    OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ OwnQ4Endpoint.centerT fixQ5 q4Away
  have center := SW.Sel.refl (base 2400) OwnQ5Endpoint.centerT centerAway
  have copy := SW.Sel.refl (base 2400) HalfFieldOB5.copyN away.2.2
  have h := center.append (copy.append replay)
  simpa only [exitSegment5S,exitSegment5,Nat.zero_add] using h

theorem selHostExitSegment5 : SW.Sel (base 2400) 1020 hostExitSegment5S hostExitSegment5 := by
  have r := (selExitSegment5.rename_inj HostOB5.hostSwap HostOB5.hostSwap_injective).castb SW.selHost_fix
  have h := (SW.Sel.refl _ _ SW.selX511_away).append
    (r.append (SW.Sel.refl _ _ SW.selX511_away))
  simpa only [hostExitSegment5S,hostExitSegment5,Nat.zero_add,Nat.add_zero] using h

theorem selExitKernel5 : SW.Sel (base 2400) 1020 exitKernel5S exitKernel5 := by
  have native := NativeFirstDirect.prefix_support base
  have known := NativeFirstKnown.inverse_support base
  have fw : base 2400∉wires (NativeFirstDirect.forward base) := fun h => SW.selPrefix_away (native.1 h)
  have iv : base 2400∉wires (NativeFirstKnown.inverse base) := fun h => SW.selPrefix_away (known h)
  have ints := SW.selInt_away
  have h := ((((((SW.Sel.refl _ _ fw).append (SW.Sel.refl _ _ ints.1)).append
    (SW.Sel.refl _ _ SW.selClear_away)).append selHostExitSegment5).append
    (SW.Sel.refl _ _ SW.selClear_away)).append (SW.Sel.refl _ _ ints.2)).append (SW.Sel.refl _ _ iv)
  simpa only [exitKernel5S,exitKernel5,Nat.zero_add,Nat.add_zero] using h

end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires exitKernel5 exitKernel5S

def forceControlE (s : State) : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩

theorem forceControlE_keep (s : State) (q : Wire) (hq : q≠base 2400) :
    (forceControlE s).basis q=s.basis q := by simp [forceControlE,writeBit,Function.update_of_ne hq]

theorem forceControlE_true (s : State) : (forceControlE s).basis (base 2400)=true := by
  simp [forceControlE,writeBit]

theorem exitKernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run exitKernel5S m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (skywalkArithmeticResult false x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let t := forceControlE s
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact forceControlE_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact forceControlE_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [forceControlE_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : t.basis (base 2409)=false := (forceControlE_keep s _ (by simp [base])).trans hg0
  have hs : t.basis (base 2410)=false := (forceControlE_keep s _ (by simp [base])).trans hs0
  have tb : t.basis (base 2400)=true := forceControlE_true s
  have strong := exitKernel5_correct hn hlo ho hf x Y hx0 hx t m input hg hs
  obtain ⟨equiv,_⟩ := selExitKernel5.eq m t tb
  rw [tb,←equiv] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree := pool_run_agrees exitKernel5S (wires exitKernel5S) (Finset.Subset.refl _) m s t rfl
    (fun q hq => (forceControlE_keep s q (fun e => selExitKernel5.away (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run exitKernel5S m s).basis q=(run exitKernel5S m t).basis q := by
    by_cases used : q∈wires exitKernel5S
    · exact agree.2 q used
    · rw [run_preserves_outside _ m s q used,run_preserves_outside _ m t q used]
      exact (forceControlE_keep s q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e => numAway (e ▸ hq))
  · intro q hq
    by_cases e : q=base 2400
    · subst q
      exact run_preserves_outside _ m s _ selExitKernel5.away
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (forceControlE_keep s q e))

end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires toffoliCount measurementCount exitKernel5 exitKernel5S

theorem exitKernel5S_support : wires exitKernel5S⊆OB5Support.logicalSites :=
  selExitKernel5.sub.wires_sub.trans exitKernel5_support

theorem exitKernel5S_physical : GatePhysical exitKernel5S :=
  selExitKernel5.sub.physical exitKernel5_physical

theorem exitKernel5S_gateSlots_le : Challenge.gateSlots exitKernel5S≤20500006 :=
  selExitKernel5.sub.slots.trans exitKernel5_gateSlots_le

theorem exitKernel5S_counts_diff : toffoliCount exitKernel5S+254=toffoliCount (SW.kernelS false) ∧
    measurementCount exitKernel5S+254=measurementCount (SW.kernelS false) := by
  have newSelT := selExitKernel5.tc
  have newSelM := selExitKernel5.mc
  have oldSelT := (SW.selKernel_sel false).tc
  have oldSelM := (SW.selKernel_sel false).mc
  have old := KernelOB5.program_counts false
  simp only [Bool.false_eq_true,if_false,if_true] at old
  have new := exitKernel5_counts
  constructor <;> omega

end ECDSAAdd.Entrant.ExitFuse
end

end


set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ExitFuseQ5
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport BalancedField History5 EntryFuse ExitFuse Q5Global718
attribute [local irreducible] run wires firstPhase lastPhase exitKernel5S hostExitSegment5S

def exitKernelQS : Program :=
  renameProgram swap firstPhase ++ hostExitSegment5S ++ renameProgram swap lastPhase

private theorem run_append_all (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

theorem hostExitSegment5S_free1026 : base 1026∉wires hostExitSegment5S := by
  intro h
  exact OwnQ5Actual.hosted_field_free false (hostExitSegment5_sub.wires_sub (selHostExitSegment5.sub.wires_sub h))

theorem exitKernelQS_eq (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    run exitKernelQS m s=run exitKernel5S m s := by
  let n1 := measurementCount firstPhase
  let n2 := measurementCount hostExitSegment5S
  let mf := m.drop n1
  let mr := m.drop (n1+n2)
  have oldShape : exitKernel5S=firstPhase++hostExitSegment5S++lastPhase := by
    simp only [exitKernel5S,firstPhase,lastPhase,List.append_assoc]
  have oldRun : run exitKernel5S m s=
      run lastPhase mr (run hostExitSegment5S mf (run firstPhase m s)) := by
    simp only [oldShape,run_append_all,measurementCount_append,List.drop_drop,n1,n2,mf,mr]
  have n1026 : base 1026∉wireBlock base 2056 256 := OwnPlusHost.not_block 1026 2056 256 (by omega)
  have n718 : base 718∉wireBlock base 2056 256 := OwnPlusHost.not_block 718 2056 256 (by omega)
  have c1026 : s.basis (base 1026)=false := input_clean x Y.val 1026 s hin (Or.inr rfl)
  have c718 : s.basis (base 718)=false := input_clean x Y.val 718 s hin (Or.inl rfl)
  have strong := exitKernel5S_correct hn hlo ho hf x Y hx0 hx s m hin hg0 hs0
  have o1026 : (run lastPhase mr (run hostExitSegment5S mf (run firstPhase m s))).basis (base 1026)=false := by
    rw [←oldRun]
    exact (strong.2.2 _ n1026).trans c1026
  have o718 : (run lastPhase mr (run hostExitSegment5S mf (run firstPhase m s))).basis (base 718)=false := by
    rw [←oldRun]
    exact (strong.2.2 _ n718).trans c718
  have eq := Q5Global718.three_states_eq hn x Y hx0 hx s m mf mr hostExitSegment5S hin
    hostExitSegment5S_free1026 o1026 o718
  have count := (renameProgram_counts swap firstPhase).2
  simp only [exitKernelQS,run_append_all,measurementCount_append,count,List.drop_drop,n1,n2,mf,mr]
  rw [eq,←oldRun]

end ECDSAAdd.Entrant.ExitFuseQ5


set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ExitFuseQ5
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport BalancedField History5 EntryFuse ExitFuse Q5Global718
attribute [local irreducible] wires toffoliCount measurementCount firstPhase lastPhase exitKernel5S

theorem exitSegment5S_sub : SW.InstrSub2 exitSegment5S (SW.segmentS false) := by
  constructor
  · intro i hi
    left
    simp only [exitSegment5S,SW.segmentS,Bool.false_eq_true,if_false,List.mem_append] at hi ⊢
    tauto
  · simp only [exitSegment5S,SW.segmentS,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
    omega

theorem hostExitSegment5S_sub : SW.InstrSub2 hostExitSegment5S (SW.segHS false) := by
  have h := (SW.InstrSub2.refl [.X (base 511)]).append
    ((exitSegment5S_sub.rename HostOB5.hostSwap HostOB5.hostSwap_injective).append
      (SW.InstrSub2.refl [.X (base 511)]))
  simpa only [hostExitSegment5S,SW.segHS] using h

theorem exitKernelQS_sub : SW.InstrSub2 exitKernelQS (OwnQ5Runtime.kernelS false) := by
  have h := ((SW.InstrSub2.refl (renameProgram swap firstPhase)).append hostExitSegment5S_sub).append
    (SW.InstrSub2.refl (renameProgram swap lastPhase))
  simpa only [exitKernelQS,OwnQ5Runtime.kernelS,OwnQ5SW.kernelQ] using h

theorem exitKernelQS_support : wires exitKernelQS⊆OB5Support.logicalSites :=
  exitKernelQS_sub.wires_sub.trans ((OwnQ5SW.selKernelQ_sel false).sub.wires_sub.trans
    (OwnQ5Integer.program_support_logical false))

theorem exitKernelQS_physical : GatePhysical exitKernelQS :=
  exitKernelQS_sub.physical ((OwnQ5SW.selKernelQ_sel false).sub.physical (OwnQ5Integer.program_physical false))

theorem exitKernelQS_slots : Challenge.gateSlots exitKernelQS≤20500006 :=
  exitKernelQS_sub.slots.trans ((OwnQ5SW.selKernelQ_sel false).sub.slots.trans (OwnQ5Actual.kernel_slots false))

theorem exitKernelQS_counts_diff :
    toffoliCount exitKernelQS+254=toffoliCount (OwnQ5Runtime.kernelS false) ∧
    measurementCount exitKernelQS+254=measurementCount (OwnQ5Runtime.kernelS false) := by
  have f := renameProgram_counts swap firstPhase
  have l := renameProgram_counts swap lastPhase
  have eqT : toffoliCount exitKernelQS=toffoliCount exitKernel5S := by
    simp only [exitKernelQS,toffoliCount_append,f.1,l.1]
    simp only [exitKernel5S,firstPhase,lastPhase,toffoliCount_append]
    omega
  have eqM : measurementCount exitKernelQS=measurementCount exitKernel5S := by
    simp only [exitKernelQS,measurementCount_append,f.2,l.2]
    simp only [exitKernel5S,firstPhase,lastPhase,measurementCount_append]
    omega
  have old := exitKernel5S_counts_diff
  have q := OwnQ5SW.kernelQ_counts false
  simp only [OwnQ5Runtime.kernelS,q.1,q.2,eqT,eqM]
  exact old

end ECDSAAdd.Entrant.ExitFuseQ5


set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField ControlledPointLayout EntryFuse ExitFuseQ5
attribute [local irreducible] run wires

theorem exitKernelQS_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run exitKernelQS m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (skywalkArithmeticResult false x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  rw [exitKernelQS_eq hn hlo ho hf x Y hx0 hx s m hin hg0 hs0]
  exact exitKernel5S_correct hn hlo ho hf x Y hx0 hx s m hin hg0 hs0

private theorem exit_mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

private theorem exit_divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem exit_numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem exit_control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

/-- Transfer a half-centered multiplication result from logical to point wires. -/
theorem exitTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (P : Program) (sites : wires P⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (P_spec : ∀(a : State) (records : List Bool), SkywalkArithmeticInput base X Y.val a.basis →
      a.basis (base 2409)=false → a.basis (base 2410)=false →
      let out := run P records a
      out.phase=a.phase ∧ regValue (wireBlock base 2056 256) out.basis=
        centerWord (skywalkArithmeticResult false X Y/2) ∧
        ∀q,q∉wireBlock base 2056 256 → out.basis q=a.basis q)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=centerWord (skywalkArithmeticResult false X Y/2) ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  have bits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [exit_mapped_regS f _ a.basis s.basis (fun q hq => bits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [exit_mapped_regS f _ a.basis s.basis (fun q hq => bits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have control : a.basis (base 2400)=B := by rw [bits _ bSite,controlMap,hb]
  have strong := P_spec a m input (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective P sites m a s rfl bits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (exit_mapped_regS f _ (run P m a).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (bits r hr))
    · exact run_rename_pool_outside f domain P sites m s q image

def arithExitS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) exitKernelQS

theorem arithExitS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) :
    let out := run (arithExitS L) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=centerWord (skywalkArithmeticResult false X Y/2) ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  have cfg := laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  exact exitTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    exit_divisor_sitesS exit_numerator_sitesS exit_control_siteS
    exitKernelQS (exitKernelQS_support.trans ArithmeticOB5.logical_sub_old) cfg.1 above cfg.2.1 cfg.2.2
    X Y B hX0 hX (fun a records input hg hs =>
      exitKernelQS_correct cfg.1 above cfg.2.1 cfg.2.2 X Y hX0 hX a records input hg hs)
    s m hb hx hy clean

theorem arithExitS_support (L : ControlledPointLayout) :
    wires (arithExitS L)⊆wires (ArithmeticOB5.arith L true) := by
  rw [arithExitS,ArithmeticOB5.arith,renameProgram_support,renameProgram_support]
  simp only [Bool.not_true]
  intro q hq
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨r,(OwnQ5SW.selKernelQ_sel false).sub.wires_sub (exitKernelQS_sub.wires_sub hr),rfl⟩

theorem arithExitS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithExitS L) := by
  apply gatePhysical_rename_support (wireFn2 L) exitKernelQS
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (exitKernelQS_support ha)) b
      (ArithmeticOB5.logical_sub_old (exitKernelQS_support hb)) eq
  · exact exitKernelQS_physical

theorem arithExitS_counts_diff (L : ControlledPointLayout) :
    toffoliCount (arithExitS L)+254=toffoliCount (arithS L true) ∧
    measurementCount (arithExitS L)+254=measurementCount (arithS L true) := by
  have c := exitKernelQS_counts_diff
  have a := renameProgram_counts (wireFn2 L) exitKernelQS
  have b := renameProgram_counts (wireFn2 L) (OwnQ5Runtime.kernelS false)
  simp only [arithExitS,arithS,Bool.not_true,a.1,a.2,b.1,b.2]
  exact c

theorem arithExitS_gateSlots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (arithExitS L)≤20500006 := by
  simpa only [arithExitS,Baselines.rename_gateSlots] using exitKernelQS_slots


end ECDSAAdd.Entrant.ExitFuse


set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic EntryFuse

def undoSign (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CX K.flag K.high] ++ parityControl g K.high k ++ [.CX (sign K) K.high,.CX K.flag (sign K)] ++
  parityControl g (sign K) k ++ [.CX K.high (sign K)] ++ rotateLeft K.out ++
  [.CX K.high (lowBit K),.CX (lowBit K) K.high]

def exit (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  [.CCX g (sign K) (alpha K)] ++ threshold K g c k ++
  compareLt none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag ++
  (if 2^255≤k/2+(c+1)/2 then [.CX (alpha K) K.flag] else []) ++
  unthreshold K g c k ++ [.CCX K.flag (sign K) K.high] ++
  table K g c k ++
  mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin ++
  untabled K g c k ++
  [.measureX K.high [] [.CZ K.flag (sign K)],.measureX (alpha K) [] [.CZ g (sign K)]] ++
  undoSign K g k ++ maskedConstant g K.src (c+k) ++ notRegister K.src ++
  eraseLtChain K.src K.out (K.carry.take 255) K.cin K.flag ++
  notRegister K.src ++ maskedConstant g K.src (c+k)

theorem exit_counts (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hw : K.Widths 256) : toffoliCount (exit K g c k)=766 ∧ measurementCount (exit K g c k)=767 := by
  have cmp := compareLt_counts none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
    (by simp [lowSrc,lowOut,hw.src,hw.out]) (by simp [lowSrc,hw.src,hw.carry])
  have sub := mappedSub_counts (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin
    (by simp [mappedRead_length,lowSrc,lowOut,hw.src,hw.out]) (by simp [lowOut,hw.out,hw.carry])
  have er := eraseLtChain_counts K.src K.out (K.carry.take 255) K.cin K.flag
    (by rw [hw.src,hw.out]) (by simp [hw.carry,hw.out])
  have rot := rotate_counts K.out
  simp only [exit,undoSign,table,untabled,threshold,unthreshold,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,
    (notRegister_counts _).1,(notRegister_counts _).2,cmp.1,cmp.2.1,sub.1,sub.2,er.1,er.2,rot.2.2.1,rot.2.2.2]
  simp only [lowSrc,lowOut,List.length_take,hw.src,hw.out, Option.isSome_none, Bool.false_eq_true, if_false]
  norm_num
  unfold parityControl
  split_ifs <;> simp [toffoliCount,measurementCount]


def lowSubtract (K : MeasuredCanonicalModLayout) : Program :=
  mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin

def tableSub (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  table K g c k ++ lowSubtract K ++ untabled K g c k

private theorem run_three (A B C : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 : List Bool,
      run (A++B++C) m s=run C m3 (run B m2 (run A m1 s)) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    (m.drop (measurementCount A)).drop (measurementCount B),
    by simp only [List.append_assoc,run_append]⟩

/-- Load, add, and unload the selected word. All non-output wires and the
phase are restored, for every incoming source value and measurement record. -/
theorem tableSub_correct (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hn : (K.cin::(lowOut K ++ K.carry.take 254)).Nodup)
    (haway : ∀q∈mappedWires (mappedRead (lowSrc K) false),
      q∉K.cin::(lowOut K ++ K.carry.take 254))
    (hlen : (lowSrc K).length=(lowOut K).length)
    (hcarryLen : (K.carry.take 254).length+1=(lowOut K).length)
    (hctrlSrc : ∀e∈entryMasks K g c k,e.1∉lowSrc K)
    (hctrlOut : ∀e∈entryMasks K g c k,e.1∉lowOut K)
    (s : State) (m : List Bool)
    (hcarry : ∀q∈K.carry.take 254,s.basis q=false) (hcin : s.basis K.cin=false) :
    let u := run (tableSub K g c k) m s
    u.phase=s.phase ∧
    regValue (lowOut K) u.basis=
      (regValue (lowOut K) s.basis+2^(lowOut K).length-
        (regValue (lowSrc K) s.basis ^^^ masksValue (lowSrc K) s.basis (entryMasks K g c k)))%2^(lowOut K).length ∧
    ∀q,q∉lowOut K → u.basis q=s.basis q := by
  have srcAway (q : Wire) (hq : q∈lowSrc K) :
      q∉K.cin::(lowOut K ++ K.carry.take 254) := by
    apply haway q
    simpa only [mappedRead_wires] using hq
  have srcOut (q : Wire) (hq : q∈lowSrc K) : q∉lowOut K := by
    intro bad
    exact srcAway q hq (by simp [bad])
  have outSrc (q : Wire) (hq : q∈lowOut K) : q∉lowSrc K := by
    intro bad
    exact srcOut q bad hq
  have cinSrc : K.cin∉lowSrc K := by
    intro bad
    exact srcAway K.cin bad (by simp)
  have carrySrc (q : Wire) (hq : q∈K.carry.take 254) : q∉lowSrc K := by
    intro bad
    exact srcAway q bad (by simp [hq])
  obtain ⟨m1,m2,m3,he⟩ := run_three (table K g c k) (lowSubtract K) (untabled K g c k) m s
  let s1 := run (table K g c k) m1 s
  let s2 := run (lowSubtract K) m2 s1
  let s3 := run (untabled K g c k) m3 s2
  have first := table_load K g c k hsrc hctrlSrc s m1
  change s1.phase=s.phase ∧ (∀q,q∉lowSrc K → s1.basis q=s.basis q) ∧
    regValue (lowSrc K) s1.basis=regValue (lowSrc K) s.basis ^^^
      masksValue (lowSrc K) s.basis (entryMasks K g c k) at first
  have carry1 : ∀q∈K.carry.take 254,s1.basis q=false := by
    intro q hq
    exact (first.2.1 q (carrySrc q hq)).trans (hcarry q hq)
  have cin1 : s1.basis K.cin=false := (first.2.1 K.cin cinSrc).trans hcin
  have middle := mappedSub_correct (mappedRead (lowSrc K) false) (lowOut K)
    (K.carry.take 254) K.cin hn haway (by simpa [mappedRead_length] using hlen)
    hcarryLen s1 m2 carry1 cin1
  change s2.phase=s1.phase ∧ (∀q,q∉lowOut K → s2.basis q=s1.basis q) ∧
    regValue (lowOut K) s2.basis=(regValue (lowOut K) s1.basis+2^(lowOut K).length-
      mappedValue (mappedRead (lowSrc K) false) s1.basis)%2^(lowOut K).length at middle
  have out1 : regValue (lowOut K) s1.basis=regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.1 q (outSrc q hq))
  have src2 : regValue (lowSrc K) s2.basis=regValue (lowSrc K) s1.basis :=
    regValue_congr _ _ _ (fun q hq => middle.2.1 q (srcOut q hq))
  have ctrl2 : ∀e∈entryMasks K g c k,s2.basis e.1=s.basis e.1 := by
    intro e he'
    exact (middle.2.1 e.1 (hctrlOut e he')).trans (first.2.1 e.1 (hctrlSrc e he'))
  have masks2 : masksValue (lowSrc K) s2.basis (entryMasks K g c k)=
      masksValue (lowSrc K) s.basis (entryMasks K g c k) :=
    masksValue_congr _ _ _ _ ctrl2
  have last := table_unload K g c k hsrc hctrlSrc s2 m3
  change s3.phase=s2.phase ∧ (∀q,q∉lowSrc K → s3.basis q=s2.basis q) ∧
    regValue (lowSrc K) s3.basis=regValue (lowSrc K) s2.basis ^^^
      masksValue (lowSrc K) s2.basis (entryMasks K g c k).reverse at last
  have src3 : regValue (lowSrc K) s3.basis=regValue (lowSrc K) s.basis := by
    rw [last.2.2,src2,first.2.2,masksValue_reverse,masks2]
    simp [Nat.xor_assoc]
  have out3 : regValue (lowOut K) s3.basis=regValue (lowOut K) s2.basis :=
    regValue_congr _ _ _ (fun q hq => last.2.1 q (outSrc q hq))
  have value : regValue (lowOut K) s3.basis =
      (regValue (lowOut K) s.basis+2^(lowOut K).length-
        (regValue (lowSrc K) s.basis ^^^ masksValue (lowSrc K) s.basis (entryMasks K g c k)))%2^(lowOut K).length := by
    rw [out3,middle.2.2,mappedRead_value,first.2.2,out1]
  have frame : ∀q,q∉lowOut K → s3.basis q=s.basis q := by
    intro q hq
    by_cases hqs : q∈lowSrc K
    · exact (regValue_eq_iff _ _ _).mp src3 q hqs
    · exact (last.2.1 q hqs).trans ((middle.2.1 q hq).trans (first.2.1 q hqs))
  dsimp only
  rw [show tableSub K g c k=table K g c k++lowSubtract K++untabled K g c k from rfl,he]
  exact ⟨last.1.trans (middle.1.trans first.1),value,frame⟩


def recoverWrap (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  threshold K g c k ++
  compareLt none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag ++
  highCorrection K c k ++ unthreshold K g c k

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,
      run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A), (m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩

/-- Fresh-record output comparison recovers the wrap without changing phase. -/
theorem recoverWrap_correct (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hsrc : (lowSrc K).Nodup)
    (hnd : (K.flag::K.cin::(lowOut K++lowSrc K++K.carry.take 255)).Nodup)
    (hlen : (lowOut K).length=(lowSrc K).length)
    (hcarryLen : (K.carry.take 255).length=(lowSrc K).length)
    (haway : ∀q∈K.cin::(lowOut K++K.carry.take 255),q∉lowSrc K)
    (hctrl : ∀e∈thresholdMasks K g c k,e.1∉lowSrc K)
    (hflagSrc : K.flag∉lowSrc K) (hflagOut : K.flag∉lowOut K)
    (hflagCarry : K.flag∉K.carry.take 255) (hcinFlag : K.cin≠K.flag)
    (hgFlag : g≠K.flag) (haFlag : alpha K≠K.flag)
    (s : State) (m : List Bool) (hzero : regValue (lowSrc K) s.basis=0)
    (hcarry : ∀q∈K.carry.take 255,s.basis q=false) (hcin : s.basis K.cin=false) :
    let v := run (recoverWrap K g c k) m s
    v.phase=s.phase ∧
      v.basis K.flag=((s.basis K.flag ^^ decide (regValue (lowOut K) s.basis <
        masksValue (lowSrc K) s.basis (thresholdMasks K g c k))) ^^
          (if 2^255≤k/2+(c+1)/2 then s.basis (alpha K) else false)) ∧
      ∀q,q≠K.flag → v.basis q=s.basis q := by
  have hgSrc : g∉lowSrc K := hctrl (g,(k+1)/2) (by simp [thresholdMasks])
  have haSrc : alpha K∉lowSrc K := hctrl
    (alpha K,Nat.xor ((k+1)/2) (k/2+(c+1)/2)) (by simp [thresholdMasks])
  have ctrlFlag : ∀e∈thresholdMasks K g c k,e.1≠K.flag := by
    intro e he
    simp only [thresholdMasks,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact hgFlag
    · exact haFlag
  have cinSrc : K.cin∉lowSrc K := haway K.cin (by simp)
  have outSrc (q : Wire) (hq : q∈lowOut K) : q∉lowSrc K := haway q (by simp [hq])
  have carrySrc (q : Wire) (hq : q∈K.carry.take 255) : q∉lowSrc K := haway q (by simp [hq])
  let A := threshold K g c k
  let B := compareLt none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
  let C := highCorrection K c k
  let D := unthreshold K g c k
  obtain ⟨m1,m2,m3,m4,he⟩ := run_four A B C D m s
  let s1 := run A m1 s
  let s2 := run B m2 s1
  let s3 := run C m3 s2
  let s4 := run D m4 s3
  have first := threshold_load K g c k hsrc hctrl s m1
  change s1.phase=s.phase ∧ (∀q,q∉lowSrc K → s1.basis q=s.basis q) ∧
    regValue (lowSrc K) s1.basis=regValue (lowSrc K) s.basis ^^^
      masksValue (lowSrc K) s.basis (thresholdMasks K g c k) at first
  have src1 : regValue (lowSrc K) s1.basis=masksValue (lowSrc K) s.basis (thresholdMasks K g c k) := by
    rw [first.2.2,hzero]; simp
  have out1 : regValue (lowOut K) s1.basis=regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.1 q (outSrc q hq))
  have cin1 : s1.basis K.cin=false := (first.2.1 K.cin cinSrc).trans hcin
  have carry1 : ∀q∈K.carry.take 255,s1.basis q=false := by
    intro q hq
    exact (first.2.1 q (carrySrc q hq)).trans (hcarry q hq)
  have second := compareLt_correct none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
    hnd (by simp) hlen hcarryLen s1 m2 cin1 carry1
  change s2.phase=s1.phase ∧ (∀q,q≠K.flag → s2.basis q=s1.basis q) ∧
    s2.basis K.flag=(s1.basis K.flag ^^ (controlValue none s1.basis &&
      decide (regValue (lowOut K) s1.basis < regValue (lowSrc K) s1.basis))) at second
  have flag2 : s2.basis K.flag=(s.basis K.flag ^^
      decide (regValue (lowOut K) s.basis < masksValue (lowSrc K) s.basis (thresholdMasks K g c k))) := by
    rw [second.2.2,first.2.1 K.flag hflagSrc,out1,src1]
    simp [controlValue]
  have third : s3.phase=s2.phase ∧
    s3.basis K.flag=(s2.basis K.flag ^^ (if 2^255≤k/2+(c+1)/2 then s2.basis (alpha K) else false)) ∧
    ∀q,q≠K.flag → s3.basis q=s2.basis q := by
    by_cases h : 2^255≤k/2+(c+1)/2
    · simpa only [s3,C,highCorrection,if_pos h,if_true] using
        conditional_cx (alpha K) K.flag true s2 m3
    · simpa only [s3,C,highCorrection,if_neg h,if_false] using
        conditional_cx (alpha K) K.flag false s2 m3
  have src3 : regValue (lowSrc K) s3.basis=regValue (lowSrc K) s1.basis := by
    apply regValue_congr
    intro q hq
    exact (third.2.2 q (fun e => hflagSrc (e ▸ hq))).trans
      (second.2.1 q (fun e => hflagSrc (e ▸ hq)))
  have controls3 : ∀e∈thresholdMasks K g c k,s3.basis e.1=s.basis e.1 := by
    intro e he'
    exact (third.2.2 e.1 (ctrlFlag e he')).trans
      ((second.2.1 e.1 (ctrlFlag e he')).trans (first.2.1 e.1 (hctrl e he')))
  have masks3 := masksValue_congr (lowSrc K) (thresholdMasks K g c k) s3.basis s.basis controls3
  have fourth := threshold_unload K g c k hsrc hctrl s3 m4
  change s4.phase=s3.phase ∧ (∀q,q∉lowSrc K → s4.basis q=s3.basis q) ∧
    regValue (lowSrc K) s4.basis=regValue (lowSrc K) s3.basis ^^^
      masksValue (lowSrc K) s3.basis (thresholdMasks K g c k).reverse at fourth
  have src4 : regValue (lowSrc K) s4.basis=regValue (lowSrc K) s.basis := by
    rw [fourth.2.2,src3,first.2.2,masksValue_reverse,masks3]
    simp [Nat.xor_assoc]
  have alpha2 : s2.basis (alpha K)=s.basis (alpha K) :=
    (second.2.1 (alpha K) haFlag).trans (first.2.1 (alpha K) haSrc)
  have flag4 : s4.basis K.flag=((s.basis K.flag ^^
      decide (regValue (lowOut K) s.basis < masksValue (lowSrc K) s.basis (thresholdMasks K g c k))) ^^
        (if 2^255≤k/2+(c+1)/2 then s.basis (alpha K) else false)) := by
    rw [fourth.2.1 K.flag hflagSrc,third.2.1,flag2,alpha2]
  have frame : ∀q,q≠K.flag → s4.basis q=s.basis q := by
    intro q hqf
    by_cases hq : q∈lowSrc K
    · exact (regValue_eq_iff _ _ _).mp src4 q hq
    · exact (fourth.2.1 q hq).trans
        ((third.2.2 q hqf).trans ((second.2.1 q hqf).trans (first.2.1 q hq)))
  dsimp only
  rw [show recoverWrap K g c k=A++B++C++D from rfl,he]
  exact ⟨fourth.1.trans (third.1.trans (second.1.trans first.1)),flag4,frame⟩

theorem compare255_nodup (K : MeasuredCanonicalModLayout) (g : Wire)
    (hn : (g::K.wires).Nodup) :
    (K.flag::K.cin::(lowOut K++lowSrc K++K.carry.take 255)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := (List.take_sublist 255 K.src).count_le q
  have b := (List.take_sublist 255 K.out).count_le q
  have c := (List.take_sublist 255 K.carry).count_le q
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
  simp only [lowSrc,lowOut,List.count_cons,List.count_append]
  omega

theorem other255_away (K : MeasuredCanonicalModLayout) (g : Wire)
    (hn : (g::K.wires).Nodup) :
    ∀q∈K.cin::(lowOut K++K.carry.take 255),q∉lowSrc K := by
  intro q hq bad
  have h := List.nodup_iff_count_le_one.mp (compare255_nodup K g hn) q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [List.count_cons,List.count_append,List.count_nil] at h a
  omega

def findWrap (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  [.CCX g (sign K) (alpha K)] ++ recoverWrap K g c k

/-- Derive the original modular wrap directly from the half-centered output. -/
theorem findWrap_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hy : Y<EntryFuseArithmetic.prime) (hk : k<EntryFuseArithmetic.prime)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false)
    (hlo : regValue (lowOut K) s.basis=
      ((Y+(if s.basis g then k else 0))%EntryFuseArithmetic.prime)/2+
        (((Y+(if s.basis g then k else 0))%EntryFuseArithmetic.prime)%2)*EntryFuseArithmetic.offset)
    (hsign : s.basis (sign K)=decide (((Y+(if s.basis g then k else 0))%EntryFuseArithmetic.prime)%2=1)) :
    let v := run (findWrap K g EntryFuseArithmetic.complement k) m s
    v.phase=s.phase ∧
    v.basis K.flag=decide (EntryFuseArithmetic.prime≤Y+(if s.basis g then k else 0)) ∧
    v.basis (alpha K)=(s.basis g && s.basis (sign K)) ∧
    ∀q,q≠K.flag → q≠alpha K → v.basis q=s.basis q := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q∈controls K g) : q∉lowOut K := controls_out K g hn hw q h
  have alphaMem : alpha K∈K.src := by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm]
    simp
  have alpha0 : s.basis (alpha K)=false := (regValue_zero K.src s.basis).mp hsrc _ alphaMem
  have away := other255_away K g hn
  have carryAlpha : alpha K∉K.carry.take 255 := by
    intro bad
    have full : alpha K∈K.src := alphaMem
    have h := List.nodup_iff_count_le_one.mp hn (alpha K)
    have a := List.count_pos_iff.mpr full
    have b := List.count_pos_iff.mpr (List.mem_of_mem_take bad)
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h
    omega
  have src0 : regValue (lowSrc K) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (regValue_zero K.src s.basis).mp hsrc q (List.mem_of_mem_take hq)
  have hctrl : ∀e∈thresholdMasks K g EntryFuseArithmetic.complement k,e.1∉lowSrc K := by
    intro e he
    exact cs _ ((mask_controls K g EntryFuseArithmetic.complement k).2 e he)
  let s1 := run [.CCX g (sign K) (alpha K)] m s
  have first := ccx_clean g (sign K) (alpha K) s m alpha0
  change s1.phase=s.phase ∧ s1.basis (alpha K)=(s.basis g && s.basis (sign K)) ∧
    ∀q,q≠alpha K → s1.basis q=s.basis q at first
  have src1 : regValue (lowSrc K) s1.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => first.2.2 q
      (fun e => cs (alpha K) (by simp [controls]) (e ▸ hq))),src0]
  have cin1 : s1.basis K.cin=false := (first.2.2 K.cin hcA).trans hcin
  have carry1 : ∀q∈K.carry.take 255,s1.basis q=false := by
    intro q hq
    exact (first.2.2 q (fun e => carryAlpha (e ▸ hq))).trans (hcarry q (List.mem_of_mem_take hq))
  have out1 : regValue (lowOut K) s1.basis=regValue (lowOut K) s.basis :=
    regValue_congr _ _ _ (fun q hq => first.2.2 q
      (fun e => co (alpha K) (by simp [controls]) (e ▸ hq)))
  have g1 : s1.basis g=s.basis g := first.2.2 g hgA
  have sign1 : s1.basis (sign K)=s.basis (sign K) := first.2.2 (sign K) (Ne.symm haS)
  have flag1 : s1.basis K.flag=false := (first.2.2 K.flag hfA).trans hf
  have alpha1 : s1.basis (alpha K)=(s1.basis g && s1.basis (sign K)) := by
    rw [first.2.1,g1,sign1]
  have second := recoverWrap_correct K g EntryFuseArithmetic.complement k
    (lowSrc_nodup K g hn hw) (compare255_nodup K g hn)
    (by rw [low.2.1,low.1]) (by simp [hw.carry,low.1]) away hctrl
    (cs K.flag (by simp [controls])) (co K.flag (by simp [controls]))
    (by intro bad; have h := List.nodup_iff_count_le_one.mp (compare255_nodup K g hn) K.flag
        have a := List.count_pos_iff.mpr bad
        simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
        omega)
    (Ne.symm hfC) hgF (Ne.symm hfA) s1 m src1 carry1 cin1
  let v := run (recoverWrap K g EntryFuseArithmetic.complement k) m s1
  change v.phase=s1.phase ∧ v.basis K.flag=((s1.basis K.flag ^^
    decide (regValue (lowOut K) s1.basis < masksValue (lowSrc K) s1.basis
      (thresholdMasks K g EntryFuseArithmetic.complement k))) ^^
    (if 2^255≤k/2+(EntryFuseArithmetic.complement+1)/2 then s1.basis (alpha K) else false)) ∧
    ∀q,q≠K.flag → v.basis q=s1.basis q at second
  have mask := thresholdMasks_value K g EntryFuseArithmetic.complement k s1 alpha1
  have mask' : masksValue (lowSrc K) s1.basis (thresholdMasks K g EntryFuseArithmetic.complement k) =
      (if s.basis g then (if s.basis (sign K) then k/2+(EntryFuseArithmetic.complement+1)/2 else (k+1)/2) else 0)%2^255 := by
    simpa only [g1,sign1,low.1] using mask
  have wrap : v.basis K.flag=decide (EntryFuseArithmetic.prime≤Y+(if s.basis g then k else 0)) := by
    rw [second.2.1,flag1,out1,hlo,mask',hsign,first.2.1,hsign]
    simp only [Bool.false_xor]
    rw [← threshold_math Y k (s.basis g) hy hk]
    simp [Bool.xor_assoc]

  dsimp only
  rw [findWrap,run_append,run_take,show measurementCount [.CCX g (sign K) (alpha K)]=0 from rfl,List.drop_zero]
  change v.phase=s.phase ∧ _
  refine ⟨second.1.trans first.1,wrap,?_,?_⟩
  · exact (second.2.2 (alpha K) (Ne.symm hfA)).trans first.2.1
  · intro q hqf hqa
    exact (second.2.2 q hqf).trans (first.2.2 q hqa)

private theorem subtract_mod (a b n : Nat) (ha : a<n) (hb : b<n) (hn : 0<n) :
    ((a+b)%n+n-b)%n=a := by
  by_cases h : a+b<n
  · rw [Nat.mod_eq_of_lt h,show a+b+n-b=a+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt ha]
  · rw [Nat.mod_eq_sub_mod (by omega : n≤a+b),Nat.mod_eq_of_lt (by omega : a+b-n<n)]
    rw [show a+b-n+n-b=a by omega,Nat.mod_eq_of_lt ha]

theorem selected_inverse_math (y k : Nat) (g : Bool) (hy : y<EntryFuseArithmetic.prime)
    (hk : k<EntryFuseArithmetic.prime) :
    let z := (y+(if g then k else 0))%EntryFuseArithmetic.prime
    let u := z/2+(z%2)*EntryFuseArithmetic.offset
    let q := selected g (decide (EntryFuseArithmetic.prime≤y+(if g then k else 0)))
      (decide (z%2=1)) EntryFuseArithmetic.complement k%2^255
    (u+2^255-q)%2^255=y/2 := by
  dsimp only
  rw [←selected_math y k g hy hk]
  let q := selected g (decide (EntryFuseArithmetic.prime≤y+(if g then k else 0)))
    (decide (((y+(if g then k else 0))%EntryFuseArithmetic.prime)%2=1))
    EntryFuseArithmetic.complement k%2^255
  change ((q+y/2)%2^255+2^255-q)%2^255=y/2
  rw [Nat.add_comm q (y/2)]
  apply subtract_mod
  · norm_num [EntryFuseArithmetic.prime,EntryFuseArithmetic.modulus,EntryFuseArithmetic.complement] at hy ⊢
    omega
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

def unselect (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  [.CCX K.flag (sign K) K.high] ++ tableSub K g c k ++
    [.measureX K.high [] [.CZ K.flag (sign K)]] ++
    [.measureX (alpha K) [] [.CZ g (sign K)]]

/-- Subtract the selected table entry and erase both AND flags with fresh records. -/
theorem unselect_correct (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (s : State) (m : List Bool)
    (hzero : regValue (lowSrc K) s.basis=0)
    (ha : s.basis (alpha K)=(s.basis g && s.basis (sign K)))
    (hh : s.basis K.high=false) (hcarry : ∀q∈K.carry.take 254,s.basis q=false)
    (hcin : s.basis K.cin=false) (hwrap : s.basis K.flag=true → s.basis g=true) :
    let v := run (unselect K g c k) m s
    v.phase=s.phase ∧ v.basis (alpha K)=false ∧
      regValue (lowOut K) v.basis=
        (regValue (lowOut K) s.basis+2^255-
          selected (s.basis g) (s.basis K.flag) (s.basis (sign K)) c k%2^255)%2^255 ∧
      ∀q,q∉lowOut K → q≠alpha K → v.basis q=s.basis q := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q∈controls K g) : q∉lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q∈controls K g) : q∉K.carry.take 254 := carry_away K g hn hw q h
  have hhSrc : K.high∉lowSrc K := cs _ (by simp [controls])
  have haOut : alpha K∉lowOut K := co _ (by simp [controls])
  have hhOut : K.high∉lowOut K := co _ (by simp [controls])
  have hfOut : K.flag∉lowOut K := co _ (by simp [controls])
  have hsOut : sign K∉lowOut K := co _ (by simp [controls])
  have hctrlSrc : ∀e∈entryMasks K g c k,e.1∉lowSrc K := by
    intro e he
    exact cs _ ((mask_controls K g c k).1 e he)
  have hctrlOut : ∀e∈entryMasks K g c k,e.1∉lowOut K := by
    intro e he
    exact co _ ((mask_controls K g c k).1 e he)
  have haway : ∀q∈mappedWires (mappedRead (lowSrc K) false),
      q∉K.cin::(lowOut K++K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let A : Program := [.CCX K.flag (sign K) K.high]
  let B := tableSub K g c k
  let C : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  let D : Program := [.measureX (alpha K) [] [.CZ g (sign K)]]
  obtain ⟨m1,m2,m3,m4,he⟩ := run_four A B C D m s
  let s1 := run A m1 s
  let s2 := run B m2 s1
  let s3 := run C m3 s2
  let s4 := run D m4 s3
  have first := ccx_clean K.flag (sign K) K.high s m1 hh
  change s1.phase=s.phase ∧ s1.basis K.high=(s.basis K.flag && s.basis (sign K)) ∧
    ∀q,q≠K.high → s1.basis q=s.basis q at first
  have tg : s1.basis g=s.basis g := first.2.2 g hgH
  have tf : s1.basis K.flag=s.basis K.flag := first.2.2 K.flag hfH
  have ts : s1.basis (sign K)=s.basis (sign K) := first.2.2 (sign K) (Ne.symm hhS)
  have ta : s1.basis (alpha K)=(s1.basis g && s1.basis (sign K)) := by
    rw [first.2.2 (alpha K) (Ne.symm hhA),tg,ts,ha]
  have tb : s1.basis K.high=(s1.basis K.flag && s1.basis (sign K)) := by
    rw [tf,ts,first.2.1]
  have tw : s1.basis K.flag=true → s1.basis g=true := by rw [tf,tg]; exact hwrap
  have src0 : regValue (lowSrc K) s1.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => first.2.2 q (fun e => hhSrc (e ▸ hq))),hzero]
  have carry0 : ∀q∈K.carry.take 254,s1.basis q=false := by
    intro q hq
    exact (first.2.2 q (fun e => cc K.high (by simp [controls]) (e ▸ hq))).trans (hcarry q hq)
  have cin0 : s1.basis K.cin=false := (first.2.2 K.cin (Ne.symm hhC)).trans hcin
  have second := tableSub_correct K g c k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1,low.2.1]) (by rw [low.2.2,low.2.1]) hctrlSrc hctrlOut
    s1 m2 carry0 cin0
  change s2.phase=s1.phase ∧ regValue (lowOut K) s2.basis=
    (regValue (lowOut K) s1.basis+2^(lowOut K).length-
      (regValue (lowSrc K) s1.basis ^^^ masksValue (lowSrc K) s1.basis (entryMasks K g c k)))%
        2^(lowOut K).length ∧ ∀q,q∉lowOut K → s2.basis q=s1.basis q at second
  have bg : s2.basis g=s.basis g := (second.2.2 g (co _ (by simp [controls]))).trans tg
  have bf : s2.basis K.flag=s.basis K.flag := (second.2.2 K.flag hfOut).trans tf
  have bs : s2.basis (sign K)=s.basis (sign K) := (second.2.2 (sign K) hsOut).trans ts
  have ba : s2.basis (alpha K)=s.basis (alpha K) :=
    (second.2.2 (alpha K) haOut).trans (first.2.2 (alpha K) (Ne.symm hhA))
  have beta : s2.basis K.high=(s2.basis K.flag && s2.basis (sign K)) := by
    rw [second.2.2 K.high hhOut,bf,bs,first.2.1]
  have third := erase_and K.flag (sign K) K.high hfH (Ne.symm hhS) s2 m3 beta
  change s3=⟨s2.phase,writeBit s2.basis K.high false⟩ at third
  have phase3 : s3.phase=s2.phase := by rw [third]
  have keep3 (q : Wire) (hq : q≠K.high) : s3.basis q=s2.basis q := by
    rw [third]; simp [writeBit,Function.update_apply,hq]
  have known3 : s3.basis (alpha K)=(s3.basis g && s3.basis (sign K)) := by
    rw [keep3 (alpha K) (Ne.symm hhA),keep3 g hgH,keep3 (sign K) (Ne.symm hhS),ba,bg,bs,ha]
  have fourth := erase_and g (sign K) (alpha K) hgA (Ne.symm haS) s3 m4 known3
  change s4=⟨s3.phase,writeBit s3.basis (alpha K) false⟩ at fourth
  have phase4 : s4.phase=s3.phase := by rw [fourth]
  have keep4 (q : Wire) (hq : q≠alpha K) : s4.basis q=s3.basis q := by
    rw [fourth]; simp [writeBit,Function.update_apply,hq]
  have out0 : regValue (lowOut K) s1.basis=regValue (lowOut K) s.basis := by
    apply regValue_congr
    intro q hq
    exact first.2.2 q (fun e => hhOut (e ▸ hq))
  have out4 : regValue (lowOut K) s4.basis=regValue (lowOut K) s2.basis := by
    apply regValue_congr
    intro q hq
    exact (keep4 q (fun e => haOut (e ▸ hq))).trans (keep3 q (fun e => hhOut (e ▸ hq)))
  have mask := entryMasks_value K g c k s1 ta tb tw
  have mask' : masksValue (lowSrc K) s1.basis (entryMasks K g c k)=
      selected (s.basis g) (s.basis K.flag) (s.basis (sign K)) c k%2^255 := by
    simpa [selected,tg,tf,ts,low.1] using mask
  have value : regValue (lowOut K) s4.basis =
      (regValue (lowOut K) s.basis+2^255-
        selected (s.basis g) (s.basis K.flag) (s.basis (sign K)) c k%2^255)%2^255 := by
    rw [out4,second.2.1,out0,src0,mask',low.2.1]
    simp
  have frame (q : Wire) (hq : q∉lowOut K) (hqa : q≠alpha K) : s4.basis q=s.basis q := by
    rw [keep4 q hqa]
    by_cases hqh : q=K.high
    · subst q
      rw [third]
      simp [writeBit,hh]
    · exact (keep3 q hqh).trans ((second.2.2 q hq).trans (first.2.2 q hqh))
  dsimp only
  rw [show unselect K g c k=A++B++C++D from rfl,he]
  refine ⟨phase4.trans (phase3.trans (second.1.trans first.1)),?_,value,frame⟩
  change s4.basis (alpha K)=false
  rw [fourth]
  simp [writeBit]

def undoTail (g d t b : Wire) (k : Nat) : Program :=
  [.CX d t] ++ parityControl g t k ++ [.CX b t,.CX d b] ++
    parityControl g b k ++ [.CX t b]

/-- Reverse only the measurement-free sign preparation. -/
theorem undoTail_correct (g d t b : Wire) (k : Nat) (s : State) (m : List Bool)
    (hgb : g≠b) (hdb : d≠b) (htb : t≠b) (hgt : g≠t) (hdt : d≠t)
    (ht : s.basis t=false) :
    let r := run (undoTail g d t b k) m s
    r.phase=s.phase ∧
    r.basis t=(s.basis b ^^ (if k%2=1 then s.basis g else false) ^^ s.basis d) ∧
    r.basis b=false ∧ ∀q,q≠b → q≠t → r.basis q=s.basis q := by
  dsimp only
  by_cases hk : k%2=1
  all_goals
    cases hg : s.basis g <;> cases hd : s.basis d <;> cases hb : s.basis b <;>
      simp [undoTail,parityControl,hk,run,writeBit,Function.update_apply,hgb,hdb,htb,hgt,hdt,
        Ne.symm hgb,Ne.symm hdb,Ne.symm htb,Ne.symm hgt,Ne.symm hdt,ht,hg,hd,hb]
  all_goals
    intro q hqb hqt
    simp [hqb,hqt]

/-- Reconstruct the original low bit and undo the word rotation. -/
theorem undoSign_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hh : s.basis K.high=false)
    (hlo : regValue (lowOut K) s.basis=Y/2)
    (hsign : s.basis (sign K)=(decide (Y%2=1) ^^
      (if k%2=1 then s.basis g else false) ^^ s.basis K.flag)) :
    let v := run (undoSign K g k) m s
    v.phase=s.phase ∧ regValue K.out v.basis=Y ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  obtain ⟨rest,hout⟩ := out_shape K hw
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have ho : K.high∉K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have hsOut : sign K∉lowOut K := controls_out K g hn hw _ (by simp [controls])
  have hhOut : K.high∉lowOut K := controls_out K g hn hw _ (by simp [controls])
  have bitmem : lowBit K∈K.out := by rw [hout]; simp
  have bitHigh : lowBit K≠K.high := fun e => ho (e ▸ bitmem)
  let A := undoTail g K.flag K.high (sign K) k
  let B := rotateLeft K.out
  let C : Program := [.CX K.high (lowBit K),.CX (lowBit K) K.high]
  obtain ⟨m1,m2,m3,he⟩ := run_three A B C m s
  let s1 := run A m1 s
  let s2 := run B m2 s1
  let s3 := run C m3 s2
  have first := undoTail_correct g K.flag K.high (sign K) k s m1
    hgS hfS hhS hgH hfH hh
  change s1.phase=s.phase ∧
    s1.basis K.high=(s.basis (sign K) ^^ (if k%2=1 then s.basis g else false) ^^ s.basis K.flag) ∧
    s1.basis (sign K)=false ∧
    ∀q,q≠sign K → q≠K.high → s1.basis q=s.basis q at first
  have high1 : s1.basis K.high=decide (Y%2=1) := by
    rw [first.2.1,hsign]
    cases h1 : decide (Y%2=1) <;> cases h2 : (if k%2=1 then s.basis g else false) <;>
      cases h3 : s.basis K.flag <;> simp [h1,h2,h3]
  have low1 : regValue (lowOut K) s1.basis=Y/2 := by
    rw [regValue_congr _ _ _ (fun q hq => first.2.2.2 q
      (fun e => hsOut (e ▸ hq)) (fun e => hhOut (e ▸ hq))),hlo]
  have word1 : regValue K.out s1.basis=Y/2 := by
    have h := word_low_value K.out hw.out s1.basis first.2.2.1
    exact h.symm.trans low1
  have fit : 2*(Y/2)<2^K.out.length := by
    have h := regValue_lt (lowOut K) s.basis
    rw [low_widths K hw |>.2.1,hlo] at h
    rw [hw.out]
    norm_num at *
    omega
  have second := rotateLeft_spec K.out (out_nodup K g hn) (Y/2) fit s1 m2 word1
  have rf := rotate_frame K.out s1 m2
  change s2.phase=s1.phase ∧ regValue K.out s2.basis=2*(Y/2) at second
  have high2 : s2.basis K.high=decide (Y%2=1) :=
    (rf.2.2.2 K.high ho).trans high1
  have bit2 : s2.basis (lowBit K)=false := by
    have h := word_low_bit K.out s2.basis (by rw [hw.out]; decide)
    rw [second.2,show 2*(Y/2)%2=0 by omega] at h
    simpa [lowBit] using h
  have third := move_low K.high (lowBit K) (Ne.symm bitHigh) s2 m3 bit2
  change s3.phase=s2.phase ∧ s3.basis (lowBit K)=s2.basis K.high ∧
    s3.basis K.high=false ∧ ∀q,q≠K.high → q≠lowBit K → s3.basis q=s2.basis q at third
  have restSame : regValue rest s3.basis=regValue rest s2.basis := by
    apply regValue_congr
    intro q hq
    apply third.2.2.2 q
    · intro e; exact ho (by rw [hout]; simp [←e,hq])
    · intro e
      have nd := out_nodup K g hn
      rw [hout] at nd
      exact (List.nodup_cons.mp nd).1 (e ▸ hq)
  have value3 : regValue K.out s3.basis=Y := by
    have hv := second.2
    rw [hout] at hv ⊢
    change (if s2.basis (lowBit K) then 1 else 0)+2*regValue rest s2.basis=2*(Y/2) at hv
    change (if s3.basis (lowBit K) then 1 else 0)+2*regValue rest s3.basis=Y
    rw [third.2.1,high2,restSame]
    rw [bit2] at hv
    simp only [Bool.false_eq_true,if_false,zero_add] at hv
    have rv : regValue rest s2.basis=Y/2 := by omega
    rw [rv]
    have decomposition := Nat.mod_add_div Y 2
    have parity : Y%2=0 ∨ Y%2=1 := by omega
    rcases parity with h|h
    · have hnot : ¬Y%2=1 := by omega
      simp [hnot] <;> omega
    · simp [h] <;> omega
  have frame (q : Wire) (hq : q∉K.out) : s3.basis q=s.basis q := by
    by_cases hqh : q=K.high
    · subst q
      exact third.2.2.1.trans hh.symm
    · have hqb : q≠lowBit K := fun e => hq (e ▸ bitmem)
      have hqs : q≠sign K := by
        intro e
        apply hq
        rw [show K.out=lowOut K++[sign K] from (word_split K.out hw.out).symm]
        simp [e]
      exact (third.2.2.2 q hqh hqb).trans ((rf.2.2.2 q hq).trans (first.2.2.2 q hqs hqh))
  have decomp : undoSign K g k=A++B++C := by
    simp [undoSign,undoTail,A,B,C,List.append_assoc]
  dsimp only
  rw [decomp,he]
  exact ⟨third.1.trans (second.1.trans first.1),value3,frame⟩

def clearOriginal (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat) : Program :=
  maskedConstant g K.src (c+k) ++ notRegister K.src ++
  eraseLtChain K.src K.out (K.carry.take 255) K.cin K.flag ++
  notRegister K.src ++ maskedConstant g K.src (c+k)

/-- Erase the original full-width wrap with a fresh measurement record. -/
theorem clearOriginal_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (s : State) (m : List Bool)
    (hy : Y<EntryFuseArithmetic.prime) (hk : k<EntryFuseArithmetic.prime)
    (hsrc : regValue K.src s.basis=0) (hout : regValue K.out s.basis=Y)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false)
    (hflag : s.basis K.flag=decide (EntryFuseArithmetic.prime≤Y+(if s.basis g then k else 0))) :
    let v := run (clearOriginal K g EntryFuseArithmetic.complement k) m s
    v.phase=s.phase ∧ v.basis K.flag=false ∧
      ∀q,q≠K.flag → v.basis q=s.basis q := by
  let c := EntryFuseArithmetic.complement
  let p := EntryFuseArithmetic.prime
  have pc : p+c=2^256 := by norm_num [p,c,EntryFuseArithmetic.prime,EntryFuseArithmetic.modulus,EntryFuseArithmetic.complement]
  have hck : c+k<2^256 := by omega
  let d := decide (p≤Y+(if s.basis g then k else 0))
  let S := 2^256-1-(if s.basis g then c+k else 0)
  have predicate : d=decide (S<Y) := by
    dsimp [d,S]
    cases hg : s.basis g
    · have a : ¬p≤Y := by omega
      have b : ¬2^256-1<Y := by omega
      simp [hg,a,b] <;> omega
    · have h : (p≤Y+k) ↔ (2^256-1-(c+k)<Y) := by omega
      simp [hg,h]
  have start : FastConst.Frame K s.basis 0 Y d s.basis := ⟨hsrc,hout,hflag,by intro q hq; rfl⟩
  have load := (FastConst.step_mask_g hn 256 hw s.basis 0 Y d (c+k) hck).seq
    (FastConst.step_not_src hn 256 hw s.basis _ _ _)
  have load' : Triple (FastConst.Frame K s.basis 0 Y d)
      (maskedConstant g K.src (c+k) ++ notRegister K.src)
      (FastConst.Frame K s.basis S Y d) := by
    simpa only [Nat.zero_xor,S] using load
  have erase := FastConst.step_erase_so hn 256 hw s.basis hcarry hcin (by decide) S Y d predicate
  have unload := (FastConst.step_not_src hn 256 hw s.basis S Y false).seq
    (FastConst.step_mask_g hn 256 hw s.basis _ Y false (c+k) hck)
  have unload' : Triple (FastConst.Frame K s.basis S Y false)
      (notRegister K.src ++ maskedConstant g K.src (c+k))
      (FastConst.Frame K s.basis 0 Y false) := by
    apply Triple.conseq (fun _ h => h) unload
    intro t ht
    refine ⟨ht.1.trans ?_,ht.2⟩
    dsimp [S]
    cases hg : s.basis g <;> simp [hg] <;> omega
  have all := (load'.seq erase).seq unload'
  have proof := all s m start
  have eq : clearOriginal K g c k =
      (maskedConstant g K.src (c+k) ++ notRegister K.src ++
        eraseLtChain K.src K.out (K.carry.take (K.out.length-1)) K.cin K.flag) ++
        (notRegister K.src ++ maskedConstant g K.src (c+k)) := by
    simp [clearOriginal,hw.out,List.append_assoc]
  let v := run (clearOriginal K g c k) m s
  have frame : v.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y false v.basis := by
    simpa only [←eq] using proof
  refine ⟨frame.1,frame.2.2.2.1,?_⟩
  intro q hq
  by_cases hqs : q∈K.src
  · have same := (regValue_eq_iff K.src v.basis s.basis).mp (frame.2.1.trans hsrc.symm)
    exact same q hqs
  by_cases hqo : q∈K.out
  · have same := (regValue_eq_iff K.out v.basis s.basis).mp (frame.2.2.1.trans hout.symm)
    exact same q hqo
  · apply frame.2.2.2.2 q
    simp [FastConst.mutable,hqs,hqo,hq]

/-- Split a canonical half-centered encoding into its low word and sign. -/
theorem encoding_parts (K : MeasuredCanonicalModLayout) (hw : K.Widths 256)
    (s : State) (z : Nat) (hz : z<EntryFuseArithmetic.prime)
    (hword : regValue K.out s.basis=z/2+(z%2)*EntryFuseArithmetic.offset+
      (if z%2=1 then 2^255 else 0)) :
    regValue (lowOut K) s.basis=z/2+(z%2)*EntryFuseArithmetic.offset ∧
      s.basis (sign K)=decide (z%2=1) := by
  have split := word_value_split K.out hw.out s.basis
  change regValue K.out s.basis=regValue (lowOut K) s.basis+
    (if s.basis (sign K) then 2^255 else 0) at split
  have low := regValue_lt (lowOut K) s.basis
  rw [(low_widths K hw).2.1] at low
  have upper := EntryFuseArithmetic.low_lt z hz
  change z/2+(z%2)*EntryFuseArithmetic.offset<2^255 at upper
  rw [hword] at split
  by_cases h : z%2=1
  · cases hs : s.basis (sign K) <;> simp [h,hs] at split ⊢ <;> omega
  · cases hs : s.basis (sign K) <;> simp [h,hs] at split ⊢ <;> omega

/-- Exact all-record inverse for the fused exit converter. -/
theorem exit_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hy : Y<EntryFuseArithmetic.prime) (hk : k<EntryFuseArithmetic.prime)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false)
    (hword : let z := (Y+(if s.basis g then k else 0))%EntryFuseArithmetic.prime
      regValue K.out s.basis=z/2+(z%2)*EntryFuseArithmetic.offset+(if z%2=1 then 2^255 else 0)) :
    let v := run (exit K g EntryFuseArithmetic.complement k) m s
    v.phase=s.phase ∧ regValue K.out v.basis=Y ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q∈controls K g) : q∉lowOut K := controls_out K g hn hw q h
  have go : g∉K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag∉K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have ao : alpha K∉K.out := controls_fullOut K g hn hw (alpha K) (by simp [controls]) haS
  have ho : K.high∉K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have cio : K.cin∉K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have sfOut (q : Wire) (hq : q∈lowSrc K) : q∉K.out :=
    src_fullOut K g hn q (List.mem_of_mem_take hq)
  have alphaMem : alpha K∈K.src := by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm]
    simp
  have alpha0 : s.basis (alpha K)=false := (regValue_zero K.src s.basis).mp hsrc _ alphaMem
  have fcarry : K.flag∉K.carry := by
    intro bad
    have h := FastConst.fixed_not_mutable hn K.flag (by simp [bad])
    exact h (by simp [FastConst.mutable])
  have acarry : alpha K∉K.carry := by
    intro bad
    have h := FastConst.fixed_not_mutable hn (alpha K) (by simp [bad])
    exact h (by simp [FastConst.mutable,alphaMem])
  let z := (Y+(if s.basis g then k else 0))%EntryFuseArithmetic.prime
  let u := z/2+(z%2)*EntryFuseArithmetic.offset
  let b := decide (z%2=1)
  let d := decide (EntryFuseArithmetic.prime≤Y+(if s.basis g then k else 0))
  have hz : z<EntryFuseArithmetic.prime := Nat.mod_lt _ (by norm_num [EntryFuseArithmetic.prime,EntryFuseArithmetic.modulus,EntryFuseArithmetic.complement])
  have parts := encoding_parts K hw s z hz hword
  change regValue (lowOut K) s.basis=u ∧ s.basis (sign K)=b at parts
  let A := findWrap K g EntryFuseArithmetic.complement k
  let B := unselect K g EntryFuseArithmetic.complement k
  let C := undoSign K g k
  let D := clearOriginal K g EntryFuseArithmetic.complement k
  obtain ⟨m1,m2,m3,m4,he⟩ := run_four A B C D m s
  let s1 := run A m1 s
  let s2 := run B m2 s1
  let s3 := run C m3 s2
  let s4 := run D m4 s3
  have first := findWrap_correct K g k Y hn hw s m1 hy hk hsrc hf hcin hcarry parts.1 parts.2
  change s1.phase=s.phase ∧ s1.basis K.flag=d ∧
    s1.basis (alpha K)=(s.basis g && s.basis (sign K)) ∧
    ∀q,q≠K.flag → q≠alpha K → s1.basis q=s.basis q at first
  have g1 : s1.basis g=s.basis g := first.2.2.2 g hgF hgA
  have sign1 : s1.basis (sign K)=b :=
    (first.2.2.2 (sign K) (Ne.symm hfS) (Ne.symm haS)).trans parts.2
  have src1 : regValue (lowSrc K) s1.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qf : q≠K.flag := fun e => cs K.flag (by simp [controls]) (e ▸ hq)
    have qa : q≠alpha K := fun e => cs (alpha K) (by simp [controls]) (e ▸ hq)
    rw [first.2.2.2 q qf qa]
    exact (regValue_zero K.src s.basis).mp hsrc q (List.mem_of_mem_take hq)
  have high1 : s1.basis K.high=false :=
    (first.2.2.2 K.high (Ne.symm hfH) hhA).trans hh
  have cin1 : s1.basis K.cin=false :=
    (first.2.2.2 K.cin (Ne.symm hfC) hcA).trans hcin
  have carry1 : ∀q∈K.carry.take 254,s1.basis q=false := by
    intro q hq
    have hq' := List.mem_of_mem_take hq
    exact (first.2.2.2 q (fun e => fcarry (e ▸ hq'))
      (fun e => acarry (e ▸ hq'))).trans (hcarry q hq')
  have alpha1 : s1.basis (alpha K)=(s1.basis g && s1.basis (sign K)) := by
    rw [first.2.2.1,g1,sign1,parts.2]
  have wrap1 : s1.basis K.flag=true → s1.basis g=true := by
    rw [first.2.1,g1]
    exact EntryFuseArithmetic.wrap_implies_control Y k (s.basis g) hy
  have low1 : regValue (lowOut K) s1.basis=u := by
    apply (regValue_congr _ _ _ (fun q hq => first.2.2.2 q
      (fun e => co K.flag (by simp [controls]) (e ▸ hq))
      (fun e => co (alpha K) (by simp [controls]) (e ▸ hq)))).trans
    exact parts.1
  have second := unselect_correct K g EntryFuseArithmetic.complement k hn hw s1 m2
    src1 alpha1 high1 carry1 cin1 wrap1
  change s2.phase=s1.phase ∧ s2.basis (alpha K)=false ∧
    regValue (lowOut K) s2.basis=(regValue (lowOut K) s1.basis+2^255-
      selected (s1.basis g) (s1.basis K.flag) (s1.basis (sign K)) EntryFuseArithmetic.complement k%2^255)%2^255 ∧
    ∀q,q∉lowOut K → q≠alpha K → s2.basis q=s1.basis q at second
  have low2 : regValue (lowOut K) s2.basis=Y/2 := by
    rw [second.2.2.1,low1,g1,first.2.1,sign1]
    exact selected_inverse_math Y k (s.basis g) hy hk
  have flag2 : s2.basis K.flag=d :=
    (second.2.2.2 K.flag (co K.flag (by simp [controls])) hfA).trans first.2.1
  have g2 : s2.basis g=s.basis g :=
    (second.2.2.2 g (co g (by simp [controls])) hgA).trans g1
  have sign2 : s2.basis (sign K)=b :=
    (second.2.2.2 (sign K) (co (sign K) (by simp [controls])) (Ne.symm haS)).trans sign1
  have high2 : s2.basis K.high=false :=
    (second.2.2.2 K.high (co K.high (by simp [controls])) hhA).trans high1
  have outside2 (q : Wire) (hq : q∉K.out) (hqf : q≠K.flag) : s2.basis q=s.basis q := by
    by_cases hqa : q=alpha K
    · subst q
      exact second.2.1.trans alpha0.symm
    · have hqLow : q∉lowOut K := fun h => hq (List.mem_of_mem_take h)
      exact (second.2.2.2 q hqLow hqa).trans (first.2.2.2 q hqf hqa)
  have signFormula : s2.basis (sign K)=(decide (Y%2=1) ^^
      (if k%2=1 then s2.basis g else false) ^^ s2.basis K.flag) := by
    rw [sign2,g2,flag2]
    have h := EntryFuseArithmetic.output_sign_controlled Y k (s.basis g) hy hk
    have odd : (if k%2=1 then s.basis g else false)=(s.basis g && decide (k%2=1)) := by
      cases s.basis g <;> by_cases h : k%2=1 <;> simp [h]
    rw [odd]
    exact h
  have third := undoSign_correct K g k Y hn hw s2 m3 high2 low2 signFormula
  change s3.phase=s2.phase ∧ regValue K.out s3.basis=Y ∧
    ∀q,q∉K.out → s3.basis q=s2.basis q at third
  have src3 : regValue K.src s3.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have qo := src_fullOut K g hn q hq
    have qf : q≠K.flag := fun e => FastConst.flag_not_src hn (e ▸ hq)
    rw [third.2.2 q qo,outside2 q qo qf]
    exact (regValue_zero K.src s.basis).mp hsrc q hq
  have cin3 : s3.basis K.cin=false := by
    rw [third.2.2 K.cin cio,outside2 K.cin cio (Ne.symm hfC),hcin]
  have carry3 : ∀q∈K.carry,s3.basis q=false := by
    intro q hq
    have qo := carry_fullOut K g hn q hq
    have qf : q≠K.flag := fun e => fcarry (e ▸ hq)
    rw [third.2.2 q qo,outside2 q qo qf,hcarry q hq]
  have g3 : s3.basis g=s.basis g := by
    rw [third.2.2 g go,outside2 g go hgF]
  have flag3 : s3.basis K.flag=decide (EntryFuseArithmetic.prime≤Y+(if s3.basis g then k else 0)) := by
    rw [third.2.2 K.flag fo,flag2,g3]
  have fourth := clearOriginal_correct K g k Y hn hw s3 m4 hy hk src3 third.2.1 cin3 carry3 flag3
  change s4.phase=s3.phase ∧ s4.basis K.flag=false ∧
    ∀q,q≠K.flag → s4.basis q=s3.basis q at fourth
  have out4 : regValue K.out s4.basis=Y := by
    apply (regValue_congr _ _ _ (fun q hq => fourth.2.2 q (fun e => fo (e ▸ hq)))).trans
    exact third.2.1
  have frame (q : Wire) (hq : q∉K.out) : s4.basis q=s.basis q := by
    by_cases hqf : q=K.flag
    · subst q
      exact fourth.2.1.trans hf.symm
    · exact (fourth.2.2 q hqf).trans ((third.2.2 q hq).trans (outside2 q hq hqf))
  have decomp : exit K g EntryFuseArithmetic.complement k=A++B++C++D := by
    simp [exit,findWrap,recoverWrap,unselect,tableSub,lowSubtract,undoSign,clearOriginal,
      highCorrection,A,B,C,D,List.append_assoc]
  dsimp only
  rw [decomp,he]
  exact ⟨fourth.1.trans (third.1.trans (second.1.trans first.1)),out4,frame⟩

/-- Field-level form of the exit converter. -/
theorem exit_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k Z : ECDSAAdd.Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool)
    (hZ : regValue K.out s.basis=Arithmetic.BalancedField.centerWord (Z/2))
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    let v := run (exit K g EntryFuseArithmetic.complement k.val) m s
    v.phase=s.phase ∧ regValue K.out v.basis=(Z-(if s.basis g then k else 0)).val ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  letI : NeZero ECDSAAdd.p := ⟨ECDSAAdd.Secp256k1.p_prime.ne_zero⟩
  let Y := Z-(if s.basis g then k else 0)
  have hy : Y.val<EntryFuseArithmetic.prime := by rw [prime_eq_secp]; exact ZMod.val_lt Y
  have hk : k.val<EntryFuseArithmetic.prime := by rw [prime_eq_secp]; exact ZMod.val_lt k
  have hZlt : Z.val<EntryFuseArithmetic.prime := by rw [prime_eq_secp]; exact ZMod.val_lt Z
  have relation : (Y.val+(if s.basis g then k.val else 0))%EntryFuseArithmetic.prime=Z.val := by
    have field : Y+(if s.basis g then k else 0)=Z := by simp [Y]
    have value := congrArg ZMod.val field
    rw [prime_eq_secp]
    cases hg : s.basis g
    · simp [hg,Nat.mod_eq_of_lt (ZMod.val_lt Y)] at value ⊢
      exact value
    · simpa [hg,ZMod.val_add] using value
  have henc := encoding_centerWord Z.val hZlt
  have enc : regValue K.out s.basis=
      ((Y.val+(if s.basis g then k.val else 0))%EntryFuseArithmetic.prime)/2+
      (((Y.val+(if s.basis g then k.val else 0))%EntryFuseArithmetic.prime)%2)*EntryFuseArithmetic.offset+
      (if ((Y.val+(if s.basis g then k.val else 0))%EntryFuseArithmetic.prime)%2=1 then 2^255 else 0) := by
    rw [relation,hZ,henc,ZMod.natCast_zmod_val]
  have h := exit_correct K g k.val Y.val hn hw s m hy hk hsrc hf hh hcin hcarry enc
  exact ⟨h.1,h.2.1,h.2.2⟩

end ECDSAAdd.Entrant.ExitFuse

section
-- ===== ExitFusePhysical =====
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic RecordedQuantum EntryFuse

theorem exit_physical (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (exit K g c k) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  obtain ⟨rest,hout⟩ := out_shape K hw
  have bitmem : lowBit K∈K.out := by rw [hout]; simp
  have highOut : K.high∉K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have bitHigh : lowBit K≠K.high := fun e => highOut (e ▸ bitmem)
  have masked (q : Wire) (hq : q∈controls K g) (v : Nat) :
      GatePhysical (maskedConstant q (lowSrc K) v) := maskedConstant_physical q _ v (cs q hq)
  have mg := maskedConstant_physical g K.src (c+k) (FastConst.g_not_src hn)
  have nr := notRegister_physical K.src
  have cmp := compareLt_physical none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
    (compare255_nodup K g hn) (by simp)
  have nd := adder_nodup K g hn hw
  have ap := mappedAdd_physical (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin
    nd (by
      intro b hb q hq
      apply src_away K g hn hw q
      have h : q∈mappedWires (mappedRead (lowSrc K) false) := by
        simp only [mappedWires,List.mem_flatMap]
        exact ⟨b,hb,by simpa using hq⟩
      simpa only [mappedRead_wires] using h)
  have nt := notRegister_physical (lowOut K)
  have sub : GatePhysical (mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin) := by
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ap) nt
  have er := eraseLtChain_physical K.src K.out (K.carry.take 255) K.cin K.flag
    (List.nodup_cons.mp (FastConst.erase_nodup hn 255).2).2
  have rot := (rotate_physical K.out (FastConst.out_nodup hn)).2
  have moveP : GatePhysical [.CX K.high (lowBit K),.CX (lowBit K) K.high] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,bitHigh,Ne.symm bitHigh]
  have signP : GatePhysical [.CX K.high (sign K)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,hhS]
  have flagHighP : GatePhysical [.CX K.flag K.high] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,hfH]
  have pairP : GatePhysical [.CX (sign K) K.high,.CX K.flag (sign K)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,hfS,Ne.symm hhS]
  have parity (q : Wire) (hq : g≠q) : GatePhysical (parityControl g q k) := by
    unfold parityControl
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate,hq]
  have alphaFlagP : GatePhysical [.CCX g (sign K) (alpha K)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,hgA,Ne.symm haS]
  have betaFlagP : GatePhysical [.CCX K.flag (sign K) K.high] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,hfH,Ne.symm hhS]
  have tableP : GatePhysical (table K g c k) := by
    simp only [table,gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have untableP : GatePhysical (untabled K g c k) := by
    simp only [untabled,gatePhysical_append]
    repeat' (first | exact masked _ (by simp [controls]) _ | apply And.intro)
  have thresholdP : GatePhysical (threshold K g c k) := by
    simp only [threshold,gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _,masked _ (by simp [controls]) _⟩
  have unthresholdP : GatePhysical (unthreshold K g c k) := by
    simp only [unthreshold,gatePhysical_append]
    exact ⟨masked _ (by simp [controls]) _,masked _ (by simp [controls]) _⟩
  have highP : GatePhysical (if 2^255≤k/2+(c+1)/2 then [.CX (alpha K) K.flag] else []) := by
    split <;> simp [GatePhysical,PhysicalInstr,ProperGate,Ne.symm hfA]
  have betaP : GatePhysical [.measureX K.high [] [.CZ K.flag (sign K)]] := by
    simp [GatePhysical,PhysicalInstr]
  have alphaP : GatePhysical [.measureX (alpha K) [] [.CZ g (sign K)]] := by
    simp [GatePhysical,PhysicalInstr]
  have bothP : GatePhysical [.measureX K.high [] [.CZ K.flag (sign K)],
      .measureX (alpha K) [] [.CZ g (sign K)]] := by
    simp [GatePhysical,PhysicalInstr]
  have ps := parity _ hgS
  have ph := parity _ hgH
  have undoP : GatePhysical (undoSign K g k) := by
    simp only [undoSign,gatePhysical_append]
    tauto
  simp only [exit,gatePhysical_append]
  tauto

end ECDSAAdd.Entrant.ExitFuse
end

section
-- ===== ExitFuseSupport =====
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic EntryFuse

theorem exit_support (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hw : K.Widths 256) : wires (exit K g c k)⊆(g::K.wires).toFinset := by
  let site := (g::K.wires).toFinset
  have member (q : Wire) (h : q∈K.src ∨ q∈K.out ∨ q∈K.carry ∨
      q=K.flag ∨ q=K.high ∨ q=K.cin ∨ q=g) : q∈site := by
    simp only [site,List.mem_toFinset,MeasuredCanonicalModLayout.wires,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false]
    tauto
  have sig : sign K∈K.out := by
    rw [show K.out=lowOut K++[sign K] from (word_split K.out hw.out).symm]
    simp
  have alp : alpha K∈K.src := by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm]
    simp
  obtain ⟨rest,hout⟩ := out_shape K hw
  have bit : lowBit K∈K.out := by rw [hout]; simp
  have hg : g∈site := member g (by simp)
  have hf : K.flag∈site := member K.flag (by simp)
  have hh : K.high∈site := member K.high (by simp)
  have hi : K.cin∈site := member K.cin (by simp)
  have hs : sign K∈site := member _ (by simp [sig])
  have ha : alpha K∈site := member _ (by simp [alp])
  have hb : lowBit K∈site := member _ (by simp [bit])
  have mask (q : Wire) (hq : q∈site) (v : Nat) :
      wires (maskedConstant q (lowSrc K) v)⊆site := by
    intro w h
    have h' := List.mem_toFinset.mp (maskedConstant_wires_subset q (lowSrc K) v h)
    rcases List.mem_cons.mp h' with rfl|h'
    · exact hq
    · exact member w (Or.inl (List.mem_of_mem_take h'))
  have maskS (v : Nat) := mask (sign K) hs v
  have maskG (v : Nat) := mask g hg v
  have maskA (v : Nat) := mask (alpha K) ha v
  have maskF (v : Nat) := mask K.flag hf v
  have maskH (v : Nat) := mask K.high hh v
  obtain ⟨full,_,nr,_,_,_,_⟩ := FastConst.parts_support (K:=K) (g:=g) ⟨256,hw⟩
  have mg : wires (maskedConstant g K.src (c+k))⊆site := full g (by simp) _
  have rot : wires (rotateLeft K.out)⊆site := by
    intro q hq
    rw [(rotate_wires K.out).2] at hq
    simp only [hw.out,show ¬256<2 by decide,if_false,List.mem_toFinset] at hq
    exact member q (by simp [hq])
  have cmp : wires (compareLt none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag)⊆site := by
    intro q hq
    have low := low_widths K hw
    rw [(compareLt_wires none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
      (by rw [low.2.1,low.1]) (by simp [hw.carry,low.1])).1] at hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at hq
    have cases : q=K.flag ∨ q=K.cin ∨ q∈lowOut K ∨ q∈lowSrc K ∨ q∈K.carry.take 255 := by
      simpa only [or_assoc] using hq
    rcases cases with rfl|rfl|h|h|h
    · exact hf
    · exact hi
    · exact member q (Or.inr (Or.inl (List.mem_of_mem_take h)))
    · exact member q (Or.inl (List.mem_of_mem_take h))
    · exact member q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have sub : wires (mappedSub (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin)⊆site := by
    intro q hq
    have h := mappedSub_wires_subset (mappedRead (lowSrc K) false) (lowOut K) (K.carry.take 254) K.cin hq
    rw [mappedRead_wires] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with hs'|ho'|hc'|rfl
    · exact member q (Or.inl (List.mem_of_mem_take hs'))
    · exact member q (Or.inr (Or.inl (List.mem_of_mem_take ho')))
    · exact member q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take hc'))))
    · exact hi
  have er : wires (eraseLtChain K.src K.out (K.carry.take 255) K.cin K.flag)⊆site := by
    intro q hq
    have h := eraseLtChain_wires_subset K.src K.out (K.carry.take 255) K.cin K.flag hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with hs'|ho'|hc'|rfl|rfl
    · exact member q (Or.inl hs')
    · exact member q (Or.inr (Or.inl ho'))
    · exact member q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take hc'))))
    · exact hi
    · exact hf
  have small (q : Wire) (h : q=g ∨ q=K.flag ∨ q=K.high ∨ q=lowBit K ∨ q=sign K ∨ q=alpha K) : q∈site := by
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
  have moveS : wires [.CX K.high (lowBit K),.CX (lowBit K) K.high]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have signS : wires [.CX K.high (sign K)]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have parityS (q : Wire) (hq : q∈site) : wires (parityControl g q k)⊆site := by
    unfold parityControl
    split
    · intro w hw'
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hw'
      rcases hw' with rfl|rfl <;> assumption
    · simp [wires]
  have pairS : wires [.CX (sign K) K.high,.CX K.flag (sign K)]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have flagHighS : wires [.CX K.flag K.high]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have alphaFlagS : wires [.CCX g (sign K) (alpha K)]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have betaFlagS : wires [.CCX K.flag (sign K) K.high]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have tableS : wires (table K g c k)⊆site := by
    simp only [table,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨maskS _,maskG _⟩,maskA _⟩,maskF _⟩,maskH _⟩
  have untableS : wires (untabled K g c k)⊆site := by
    simp only [untabled,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨maskH _,maskF _⟩,maskA _⟩,maskG _⟩,maskS _⟩
  have thresholdS : wires (threshold K g c k)⊆site := by
    simp only [threshold,wires_append,Finset.union_subset_iff]
    exact ⟨maskG _,maskA _⟩
  have unthresholdS : wires (unthreshold K g c k)⊆site := by
    simp only [unthreshold,wires_append,Finset.union_subset_iff]
    exact ⟨maskA _,maskG _⟩
  have highS : wires (if 2^255≤k/2+(c+1)/2 then [.CX (alpha K) K.flag] else [])⊆site := by
    split
    · intro q hq; apply small q
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hq
      tauto
    · simp [wires]
  have betaS : wires [.measureX K.high [] [.CZ K.flag (sign K)]]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have alphaS : wires [.measureX (alpha K) [] [.CZ g (sign K)]]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have bothS : wires [.measureX K.high [] [.CZ K.flag (sign K)],
      .measureX (alpha K) [] [.CZ g (sign K)]]⊆site := by
    intro q hq; apply small q
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    tauto
  have ps := parityS (sign K) hs
  have ph := parityS K.high hh
  have undoS : wires (undoSign K g k)⊆site := by
    simp only [undoSign,wires_append,Finset.union_subset_iff]
    tauto
  simp only [exit,wires_append,Finset.union_subset_iff]
  tauto

end ECDSAAdd.Entrant.ExitFuse
end

section
-- ===== ExitFuseSlots =====
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Challenge Baselines EntryFuse

theorem exit_gateSlots_le (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hw : K.Widths 256) : gateSlots (exit K g c k)≤25000 := by
  have full := Baselines.maskedConstant_gateSlots_le g K.src (c+k)
  have a := Baselines.maskedConstant_gateSlots_le (sign K) (lowSrc K) ((c+1)/2)
  have b := Baselines.maskedConstant_gateSlots_le g (lowSrc K) ((k+1)/2)
  have d := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K)
    (Nat.xor (Nat.xor ((c+1)/2) ((k+1)/2)) (k/2+(c+1)/2))
  have e := Baselines.maskedConstant_gateSlots_le K.flag (lowSrc K) (Nat.xor ((k+1)/2) (k/2+(c+1)/2))
  have f := Baselines.maskedConstant_gateSlots_le K.high (lowSrc K) (Nat.xor ((k+1)/2+c) ((k+1)/2))
  have t := Baselines.maskedConstant_gateSlots_le (alpha K) (lowSrc K) (Nat.xor ((k+1)/2) (k/2+(c+1)/2))
  have cmp := Baselines.compareLt_gateSlots_le none (lowOut K) (lowSrc K) (K.carry.take 255) K.cin K.flag
  have sub := Baselines.mappedSub_gateSlots_le (mappedRead (lowSrc K) false)
    (lowOut K) (K.carry.take 254) K.cin
  have er := Baselines.eraseLt_gateSlots_le K.src K.out (K.carry.take 255) K.cin K.flag
  have rot := (Baselines.rotate_gateSlots_le K.out).2
  have parity (q : Wire) : gateSlots (parityControl g q k)≤1 := by
    unfold parityControl
    split <;> simp [gateSlots_cons,gateSlots_nil,instructionSlots]
  have ps := parity (sign K)
  have ph := parity K.high
  have hi : gateSlots (if 2^255≤k/2+(c+1)/2 then [.CX (alpha K) K.flag] else [])≤1 := by
    split <;> simp [gateSlots_cons,gateSlots_nil,instructionSlots]
  have low := low_widths K hw
  simp only [low.1,hw.src] at full a b d e f t
  simp only [low.2.1,low.1] at cmp
  simp only [mappedRead_length,low.1] at sub
  simp only [hw.src,hw.out] at er
  simp only [hw.out] at rot
  simp only [exit,undoSign,table,untabled,threshold,unthreshold,gateSlots_append,
    Baselines.notRegister_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,hw.src,
    List.length_cons,List.length_nil,Nat.reduceAdd]
  omega

end ECDSAAdd.Entrant.ExitFuse
end

section
-- ===== ExitFusePoint =====
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog BalancedField
  MappedCompressed CompressedAllocation CompressedFieldSupport DirectSkywalk EntryFuse

def fusedExitY (L : ControlledPointLayout) (k : Fp) : Program :=
  exit (L.recoveryConstant L.point.y) L.core.generic EntryFuseArithmetic.complement k.val

theorem fusedExitY_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Z k : Fp) (s : State) (m : List Bool)
    (hy : regValue L.point.y s.basis=centerWord (Z/2))
    (hc : regValue L.dialogPool s.basis=0) :
    let v := run (fusedExitY L k) m s
    v.phase=s.phase ∧ regValue L.point.y v.basis=(Z-(if s.basis L.core.generic then k else 0)).val ∧
      ∀q,q∉L.point.y → v.basis q=s.basis q := by
  let K := L.recoveryConstant L.point.y
  have aux (q : Wire) (hq : q∈K.src++K.carry++[K.high,K.cin,K.flag]) : s.basis q=false := by
    change q∈(L.recoveryConstant L.point.y).src++(L.recoveryConstant L.point.y).carry++
      [(L.recoveryConstant L.point.y).high,(L.recoveryConstant L.point.y).cin,
        (L.recoveryConstant L.point.y).flag] at hq
    rw [L.recoveryConstant_pool hw L.point.y] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have sz : regValue K.src s.basis=0 := (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have flag : s.basis K.flag=false := aux _ (by simp)
  have high : s.basis K.high=false := aux _ (by simp)
  have cin : s.basis K.cin=false := aux _ (by simp)
  have carry : ∀q∈K.carry,s.basis q=false := by intro q hq; exact aux q (by simp [hq])
  have result := exit_field_correct K L.core.generic k Z (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY) s m hy sz flag high cin carry
  simpa only [fusedExitY,K,ControlledPointLayout.recoveryConstant] using result

theorem fusedExitY_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (fusedExitY L k)⊆(L.core.generic::(L.recoveryConstant L.point.y).wires).toFinset :=
  exit_support _ _ _ _ (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem fusedExitY_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (fusedExitY L k) :=
  exit_physical _ _ _ _ (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem fusedExitY_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (fusedExitY L k)=766 ∧ measurementCount (fusedExitY L k)=767 :=
  exit_counts _ _ _ _ (L.recoveryConstant_widths hw L.point.y hw.inputY)

end ECDSAAdd.Entrant.ExitFuse
end

section
-- ===== ExitFuseNegTransport =====
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog EntryFuse
attribute [local irreducible] run wires

/-- Programs that avoid a register preserve a paired frame through all records. -/
theorem register_transport (P : Program) (r : List Wire)
    (away : ∀q∈wires P,q∉r) (s t : State) (m : List Bool)
    (phase : t.phase=s.phase) (same : ∀q,q∉r → t.basis q=s.basis q) :
    (run P m t).phase=(run P m s).phase ∧
      (∀q,q∉r → (run P m t).basis q=(run P m s).basis q) ∧
      (∀q,q∈r → (run P m t).basis q=t.basis q ∧ (run P m s).basis q=s.basis q) := by
  have inc := run_local_increment P t s m (fun q hq => same q (away q hq))
  refine ⟨?_,?_,?_⟩
  · rw [phase] at inc
    cases s.phase <;> simpa using inc.1
  · intro q hq
    by_cases used : q∈wires P
    · exact inc.2 q used
    · rw [run_preserves_outside P m t q used,run_preserves_outside P m s q used]
      exact same q hq
  · intro q hq
    have unused : q∉wires P := fun h => away q h hq
    exact ⟨run_preserves_outside P m t q unused,run_preserves_outside P m s q unused⟩

/-- The x-only reflection never touches a y-coordinate wire. -/
theorem fastNeg_away_y (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (q : Wire) (hq : q∈wires (fastConstNeg L k)) : q∉L.point.y := by
  have bound := FastConst.fastNeg_support (K:=L.recoveryConstant L.point.x) (g:=L.core.generic)
    p k.val ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩
  have h := bound (by simpa only [fastConstNeg] using hq)
  have member := List.mem_toFinset.mp h
  have away (q : Wire) (hq : q∈L.point.x ∨ q=L.core.generic ∨ q∈L.dialogPool) : q∉L.point.y := by
    intro bad
    have nd := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) q
    have y := List.count_pos_iff.mpr bad
    simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_append,
      List.count_cons,List.count_nil] at nd
    rcases hq with hx|rfl|hp
    · have x := List.count_pos_iff.mpr hx; omega
    · simp only [beq_self_eq_true,if_true] at nd; omega
    · have pool := List.count_pos_iff.mpr hp; omega
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
  have parts : q=L.core.generic ∨ q∈(L.recoveryConstant L.point.x).out ∨
      q∈(L.recoveryConstant L.point.x).src++(L.recoveryConstant L.point.x).carry++
        [(L.recoveryConstant L.point.x).high,(L.recoveryConstant L.point.x).cin,
          (L.recoveryConstant L.point.x).flag] := by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  rcases parts with hgen|hout|haux
  · exact away q (Or.inr (Or.inl hgen))
  · have eq : (L.recoveryConstant L.point.x).out=L.point.x := rfl
    rw [eq] at hout
    exact away q (Or.inl hout)
  · have hp : q∈L.dialogPool.take 515 := by
      rw [←L.recoveryConstant_pool hw L.point.x]
      exact haux
    exact away q (Or.inr (Or.inr (List.mem_of_mem_take hp)))

end ECDSAAdd.Entrant.ExitFuse
end




set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField EntryFuse
attribute [local irreducible] run arithExitS arithS

theorem exitMid_pairS (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Nat) (Y : Fp) (G : Bool) (positive : 0<D) (bound : D<p)
    (fixed a c : State) (records : List Bool)
    (fixedG : fixed.basis L.core.generic=G) (fixedX : regValue L.point.x fixed.basis=D)
    (fixedY : regValue L.point.y fixed.basis=Y.val) (fixedClean : regValue L.dialogPool fixed.basis=0)
    (ha : run (arithExitS L) records fixed=a) (hc : run (arithS L true) [] fixed=c) :
    a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord (skywalkArithmeticResult false D Y/2) ∧
      ∀q,q∉L.point.y → a.basis q=c.basis q := by
  have newer := arithExitS_correct L hw hn D Y G positive bound fixed records
    fixedG fixedX fixedY fixedClean
  have older := arithS_correct L hw hn true D Y.val bound positive Y.isLt fixed []
    fixedX fixedY fixedClean
  rw [ha] at newer
  rw [hc] at older
  exact ⟨newer.1.trans older.1.symm,newer.2.1,fun q hq =>
    (newer.2.2 q hq).trans (older.2.2 q hq).symm⟩

end ECDSAAdd.Entrant.ExitFuse

section
-- ===== ExitFusePointComposition =====
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog BalancedField
  MappedCompressed CompressedAllocation CompressedFieldSupport DirectSkywalk EntryFuse
attribute [local irreducible] run wires arithExitS arithS fastConstNeg fusedExitY fastConstAdd

private theorem pool_away_y (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.y := by
  intro bad
  have nd := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,List.count_nil] at nd
  omega

private theorem generic_away_y (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    L.core.generic∉L.point.y := by
  intro bad
  have nd := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) L.core.generic
  have b := List.count_pos_iff.mpr bad
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_append,
    List.count_cons,List.count_nil,beq_self_eq_true,if_true] at nd
  omega

/-- Multiply, reflect x, and remove the classical y offset through the fused exit. -/
theorem exitCompose_genericZ (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P Q : Program) (X Y Z cx cy : Fp) (G : Bool) (origin : BasisState)
    (oldMul : Triple (PointDialogValues L X Y G origin) Q
      (PointDialogValues L X Z G origin))
    (pair : ∀(s : State) (m : List Bool), PointDialogValues L X Y G origin s.basis →
      let a := run P m s
      let c := run Q [] s
      a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord (Z/2) ∧
        ∀q,q∉L.point.y → a.basis q=c.basis q) :
    Triple (PointDialogValues L X Y G origin) (P++(fastConstNeg L cx++fusedExitY L cy))
      (PointDialogValues L (if G then cx-X else X) (Z-(if G then cy else 0)) G origin) := by
  intro s m v
  let n1 := measurementCount P
  let n2 := measurementCount (fastConstNeg L cx)
  let m1 := m.take n1
  let m2 := (m.drop n1).take n2
  let m3 := (m.drop n1).drop n2
  let a := run P m1 s
  let c := run Q [] s
  let a2 := run (fastConstNeg L cx) m2 a
  let c2 := run (fastConstNeg L cx) m2 c
  let r := run (fusedExitY L cy) m3 a2
  let old := run (fastConstAdd L L.point.y (-cy)) [] c2
  have oldResult := oldMul s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := by
    exact oldResult.2
  have paired := pair s m1 v
  change a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord (Z/2) ∧
    (∀q,q∉L.point.y → a.basis q=c.basis q) at paired
  have phase1 : a.phase=c.phase := paired.1
  have same1 (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q := paired.2.2 q hq
  have half1 : regValue L.point.y a.basis=centerWord (Z/2) := paired.2.1
  have trans := register_transport (fastConstNeg L cx) L.point.y
    (fastNeg_away_y L hw hn cx) c a m2 phase1 same1
  change a2.phase=c2.phase ∧
    (∀q,q∉L.point.y → a2.basis q=c2.basis q) ∧
    (∀q,q∈L.point.y → a2.basis q=a.basis q ∧ c2.basis q=c.basis q) at trans
  have half2 : regValue L.point.y a2.basis=centerWord (Z/2) := by
    apply (regValue_congr _ _ _ (fun q hq => (trans.2.2 q hq).1)).trans
    exact half1
  have g2 : a2.basis L.core.generic=G := by
    rw [trans.2.1 _ (generic_away_y L hn)]
    have h := fastStep_negX L hw hn X Z G origin cx c m2 canonical
    exact h.2.generic
  have oldNeg := fastStep_negX L hw hn X Z G origin cx c m2 canonical
  have clean2 : regValue L.dialogPool a2.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [trans.2.1 q (pool_away_y L hn q hq)]
    exact (regValue_zero _ _).mp oldNeg.2.clean q hq
  have newEnd := fusedExitY_correct L hw hn Z cy a2 m3 half2 clean2
  have oldEnd := fastStep_addY L hw hn (if G then cx-X else X) Z G origin (-cy) c2 [] oldNeg.2
  have oldFrame := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) (-cy) Z.val G Z.isLt c2 []
    oldNeg.2.generic oldNeg.2.y oldNeg.2.clean
  have wordEq : regValue L.point.y r.basis=regValue L.point.y old.basis := by
    rw [newEnd.2.1,g2,oldEnd.2.y]
    cases G <;> simp [sub_eq_add_neg]
  have outputEq : r=old := by
    apply State.extensionality
    · exact newEnd.1.trans (trans.1.trans oldEnd.1.symm)
    · funext q
      by_cases hq : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp wordEq q hq
      · exact (newEnd.2.2 q hq).trans ((trans.2.1 q hq).trans (oldFrame.2.2 q hq).symm)
  have eqProgram : run (P++(fastConstNeg L cx++fusedExitY L cy)) m s=old := by
    rw [run_append,run_append]
    exact outputEq
  rw [eqProgram]
  refine ⟨oldEnd.1.trans (oldNeg.1.trans oldResult.1),?_⟩
  cases G <;> simpa [sub_eq_add_neg] using oldEnd.2





end ECDSAAdd.Entrant.ExitFuse
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitFuse
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField EntryFuse

def fusedExitF (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  arithExitS L ++ (fastConstNeg L cx ++ fusedExitY L cy)

theorem fusedExitF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedExitF L cx cy)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then cy else 0)) G origin) := by
  have hXpos : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have old := arith3F_step L hw hn X Y G origin true hX
  have pair : ∀(s : State) (m : List Bool), PointDialogValues L X Y G origin s.basis →
      let a := run (arithExitS L) m s
      let c := run (arithS L true) [] s
      a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord ((Y*X)/2) ∧
        ∀q,q∉L.point.y → a.basis q=c.basis q := by
    intro s m v
    have p := exitMid_pairS L hw hn X.val Y G hXpos X.isLt s _ _ m
      v.generic v.x v.y v.clean rfl rfl
    simpa only [skywalkArithmeticResult,Bool.false_eq_true,if_false,ZMod.natCast_zmod_val] using p
  have h := exitCompose_genericZ L hw hn (arithExitS L) (arithS L true)
    X Y (Y*X) cx cy G origin (by simpa only [if_true] using old) pair
  simpa only [fusedExitF] using h

end ECDSAAdd.Entrant.ExitFuse
end



namespace ECDSAAdd.Entrant.ExitFuseFinite
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite ExitFuse
open Challenge Baselines
def genericBothF (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ fusedDivisionF L (-cy) ++
  SquareOB5.program L ++ fastConstAdd L L.point.x (3*cx-(SquareAQ.offset:Fp)) ++ fusedExitF L cx cy

def midBothF (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L ++ renameProgram (swapF L) (genericBothF L cx cy) ++ clrF L

def genBothF (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L ++ midBothF L cx cy ++ zrep L


section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
attribute [local irreducible] toffoliCount measurementCount
include hw in
theorem genericBothF_counts_diff (cx cy : Fp) :
    toffoliCount (genericBothF L cx cy)+254=toffoliCount (genericFFused L cx cy) ∧
    measurementCount (genericBothF L cx cy)+254=measurementCount (genericFFused L cx cy) := by
  have ex := fusedExitY_counts L hw cy
  have old := fastConstAdd_counts L hw L.point.y (Or.inr rfl) (-cy)
  have ar := arithExitS_counts_diff L
  have ref := fastConstRefl_counts L hw (3*cx-1)
  have added := fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(SquareAQ.offset:Fp))
  simp only [genericBothF,fusedExitF,genericFFused,toffoliCount_append,measurementCount_append]
  constructor <;> omega

include hw in
theorem genBothF_counts_diff (cx cy : Fp) :
    toffoliCount (genBothF L cx cy)+254=toffoliCount (genFFused L cx cy) ∧
    measurementCount (genBothF L cx cy)+254=measurementCount (genFFused L cx cy) := by
  have g := genericBothF_counts_diff L hw cx cy
  have r := renameProgram_counts (swapF L) (genericBothF L cx cy)
  have r0 := renameProgram_counts (swapF L) (genericFFused L cx cy)
  simp only [genBothF,midBothF,genFFused,midFFused,toffoliCount_append,measurementCount_append,r.1,r.2,r0.1,r0.2]
  constructor <;> omega

end
end ECDSAAdd.Entrant.ExitFuseFinite

section InverseEndpointBorrowed
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.InverseTailC
open ECDSAAdd Arithmetic BalancedField BalancedCircuit

def third : Nat := q.toNat/3

def prep (L : Layout) : Program :=
  copyRegister none L.y L.r ++ signComplement L.ymsb L.ylow ++
  xorConstant L.low (third+1) ++ maskedConstant L.ymsb L.low ((third+1)^^^third)

def decision (L : Layout) : Program :=
  prep L ++ compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity ++
  [.CX L.sign L.parity] ++ (prep L).reverse

def double (L : Layout) : Program := [.CX L.ymsb L.rmsb] ++ rotateLeft L.r

def raw (L : Layout) : Program :=
  double L ++ [.X L.sign] ++ signedAdd L.sign L.y L.r (L.carry.take 255) ++ [.X L.sign]

def correction (L : Layout) : Program :=
  signComplement L.ymsb L.r ++
  mappedSub (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one ++
  signComplement L.ymsb L.r

def program (L : Layout) : Program :=
  decision L ++ raw L ++ correction L ++ [.CX L.r0 L.parity,.CX (L.ylow.headD L.ymsb) L.parity]

private theorem counts_prep (L : Layout) (hw : L.Widths) :
    toffoliCount (prep L)=0 ∧ measurementCount (prep L)=0 := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have c:=copyRegister_counts none L.y L.r (w.2.2.1.trans w.2.1.symm)
  simp only [prep,toffoliCount_append,measurementCount_append,c.1,c.2,signComplement_counts,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2]
  simp

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=766 ∧ measurementCount (program L)=765 := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have c:=counts_prep L hw
  have cmp:=compareLt_counts (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
    (hw.2.1.trans w.1.symm) (by simp [List.length_take,hw.2.2,w.1])
  have ad:=signedWord_counts L.sign L.y L.r (L.carry.take 255)
    (w.2.2.1.trans w.2.1.symm) (by simp [List.length_take,hw.2.2,w.2.1])
  have sub:=mappedSub_counts (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one
    (by simp [mappedConstant_length,w.2.1]) (by simp [List.length_take,hw.2.2,w.2.1])
  have rot:=(rotate_counts L.r).2
  simp only [program,decision,raw,double,correction,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,c.1,c.2,cmp.1,cmp.2.1,ad.1,ad.2.1,sub.1,sub.2,
    (signComplement_counts _ _).1,(signComplement_counts _ _).2,rot.2.1,rot.2.2,
    w.1,w.2.1,Option.isSome_some,if_true]
  norm_num [toffoliCount,measurementCount]


section Facts
variable {L : Layout}

theorem inventoryND (hn : L.wires.Nodup) :
    (L.sign::L.parity::L.one::L.lower::(L.y++L.r++L.carry.take 255)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro a
  have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) a
  have t:=(List.take_sublist 255 L.carry).count_le a
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.count_cons,List.count_append,List.count_nil] at h t ⊢
  omega

theorem yrND (hn : L.wires.Nodup) : (L.y++L.r).Nodup := by
  have nd:=inventoryND hn
  apply List.nodup_iff_count.mpr
  intro a
  have h:=List.nodup_iff_count.mp nd a
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem lowND (hn : L.wires.Nodup) : L.low.Nodup := by
  have nd:=(List.nodup_append'.mp (yrND hn)).2.1
  exact (List.nodup_append'.mp nd).1

theorem ylowND (hn : L.wires.Nodup) : L.ylow.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (yrND hn)).1).1

theorem y_away_r (hn : L.wires.Nodup) (a : Wire) (ha : a∈L.y) : a∉L.r :=
  List.disjoint_left.mp (List.nodup_append'.mp (yrND hn)).2.2 ha

theorem flagAway (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sign,L.parity,L.one,L.lower]) : a∉L.y++L.r++L.carry := by
  have f:=BalancedCircuit.flagAway L hn a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; tauto)
  intro bad
  apply f
  simp only [List.mem_append] at bad ⊢
  tauto

theorem lowSub : L.low⊆L.r := by
  intro a ha; exact List.mem_append_left _ ha

theorem ylowSub : L.ylow⊆L.y := by
  intro a ha; exact List.mem_append_left _ ha

theorem ysignAwayLow (hn : L.wires.Nodup) : L.ymsb∉L.ylow := by
  have nd:=(List.nodup_append'.mp (List.nodup_append'.mp (yrND hn)).1).2.2
  intro h; exact List.disjoint_left.mp nd h (by simp)

theorem ysignAwayR (hn : L.wires.Nodup) : L.ymsb∉L.r :=
  y_away_r hn _ (by simp [BalancedCleanup.Layout.y])

private theorem xor_proper (r : List Wire) (k : Nat) : ProperProgram (xorConstant r k) := by
  induction r generalizing k with
  | nil => simp [xorConstant,ProperProgram]
  | cons a r ih =>
    simp only [xorConstant,properProgram_append]
    constructor
    · split <;> simp [ProperProgram,ProperGate]
    · exact ih _

private theorem mask_proper (c : Wire) (r : List Wire) (k : Nat) (hc : c∉r) :
    ProperProgram (maskedConstant c r k) := by
  induction r generalizing k with
  | nil => simp [maskedConstant,ProperProgram]
  | cons a r ih =>
    have ca : c≠a := fun e=>hc (by simp [e])
    have cr : c∉r := fun h=>hc (by simp [h])
    simp only [maskedConstant,properProgram_append]
    constructor
    · split <;> simp [ProperProgram,ProperGate,ca]
    · exact ih _ cr

private theorem copy_proper (x y : List Wire) (hn : (x++y).Nodup) :
    ProperProgram (copyRegister none x y) := by
  induction x generalizing y with
  | nil => simp [copyRegister,ProperProgram]
  | cons a x ih =>
    cases y with
    | nil => simp [copyRegister,ProperProgram]
    | cons b y =>
      have cnt:=List.nodup_iff_count.mp hn
      have ne : a≠b := by
        intro e; have h:=cnt a
        simp only [List.count_cons,List.count_append,←e,beq_self_eq_true,if_true] at h
        omega
      have nd : (x++y).Nodup := by
        apply List.nodup_iff_count.mpr; intro q; have h:=cnt q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      simpa only [copyRegister,copyGate,properProgram_append] using
        And.intro (by simpa [ProperProgram,ProperGate] using ne) (ih y nd)

theorem prep_proper (hn : L.wires.Nodup) : ProperProgram (prep L) := by
  have ya:=ysignAwayLow hn
  have yr:=ysignAwayR hn
  simp only [prep,properProgram_append]
  exact ⟨⟨⟨copy_proper _ _ (yrND hn),BalancedCleanup.complement_proper _ _ ya⟩,
    xor_proper _ _⟩,mask_proper _ _ _ (fun h=>yr (lowSub h))⟩

theorem prep_support : wires (prep L)⊆(L.y++L.r).toFinset := by
  have c:=copyRegister_wires_subset none L.y L.r
  have a:=signComplement_wires_subset L.ymsb L.ylow
  have x:=xorConstant_wires_subset L.low (third+1)
  have z:=maskedConstant_wires_subset L.ymsb L.low ((third+1)^^^third)
  intro q hq
  simp only [prep,wires_append,Finset.mem_union] at hq
  rcases hq with ((hq|hq)|hq)|hq
  · have h:=c hq
    simpa only [Option.toList_none,List.nil_append] using h
  · have h:=a hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    exact List.mem_toFinset.mpr (by rcases h with rfl|h; simp [BalancedCleanup.Layout.y]; exact List.mem_append_left _ (ylowSub h))
  · have h:=List.mem_toFinset.mp (x hq)
    exact List.mem_toFinset.mpr (List.mem_append_right _ (lowSub h))
  · have h:=List.mem_toFinset.mp (z hq)
    simp only [List.mem_cons] at h
    exact List.mem_toFinset.mpr (by rcases h with rfl|h; simp [BalancedCleanup.Layout.y]; exact List.mem_append_right _ (lowSub h))

end Facts


private theorem no_records (P : Program) (hm : measurementCount P=0) (s : State) (m n : List Bool) :
    run P m s=run P n s := by
  rw [←run_take P m s,←run_take P n s,hm]
  rfl

private theorem third_bounds : third+1<2^255 ∧ third<2^255 := by
  decide +kernel

private theorem third_xor_bound : (third+1)^^^third<2^255 := by
  exact Nat.xor_lt_two_pow (third_bounds.1) (third_bounds.2)

theorem prep_data (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (heq : regValue L.r s.basis=regValue L.y s.basis) :
    let t:=run (prep L) m s
    t.phase=s.phase ∧
    regValue L.ylow t.basis=(if s.basis L.ymsb then 2^255-1-regValue L.ylow s.basis else regValue L.ylow s.basis) ∧
    regValue L.low t.basis=(if s.basis L.ymsb then third else third+1) := by
  let A:=copyRegister none L.y L.r
  let B:=signComplement L.ymsb L.ylow
  let C:=xorConstant L.low (third+1)
  let D:=maskedConstant L.ymsb L.low ((third+1)^^^third)
  let u:=run A m s
  let v:=run B m u
  let w:=run C m v
  let z:=run D m w
  have widths:=BalancedCleanup.widths L.toLayout hw
  have cp:=copyRegister_correct none L.y L.r (widths.2.2.1.trans widths.2.1.symm) (yrND hn) (by simp) s m
  have ur : regValue L.r u.basis=0 := by
    change regValue L.r (run A m s).basis=0
    simpa only [A,heq,copyValue,Nat.xor_self] using cp.2.2
  have ul : regValue L.low u.basis=0 := by
    exact (regValue_zero _ _).mpr (fun a ha=>(regValue_zero _ _).mp ur a (lowSub ha))
  have uy : ∀a∈L.y,u.basis a=s.basis a := fun a ha=>cp.2.1 a (y_away_r hn a ha)
  have us : u.basis L.ymsb=s.basis L.ymsb := uy _ (by simp [BalancedCleanup.Layout.y])
  have uv : regValue L.ylow u.basis=regValue L.ylow s.basis := regValue_congr _ _ _ (fun a ha=>uy a (ylowSub ha))
  have yc:=signComplement_correct L.ymsb L.ylow (ylowND hn) (ysignAwayLow hn) u m
  have low_away (a : Wire) (ha : a∈L.low) : a∉L.ylow := by
    intro bad
    exact y_away_r hn a (ylowSub bad) (lowSub ha)
  have vl : regValue L.low v.basis=0 :=
    (regValue_congr _ _ _ (fun a ha=>yc.2.1 a (low_away a ha))).trans ul
  have vs : v.basis L.ymsb=s.basis L.ymsb := (yc.2.1 _ (ysignAwayLow hn)).trans us
  have xc:=xorConstant_correct L.low (lowND hn) (third+1) (by rw [widths.1];exact third_bounds.1) v m
  have wl : regValue L.low w.basis=third+1 := by
    simpa only [vl,Nat.zero_xor] using xc.2.2
  have ws : w.basis L.ymsb=s.basis L.ymsb :=
    (xc.2.1 _ (fun h=>ysignAwayR hn (lowSub h))).trans vs
  have mc:=maskedConstant_correct L.ymsb L.low ((third+1)^^^third) (lowND hn)
    (fun h=>ysignAwayR hn (lowSub h)) (by rw [widths.1];exact third_xor_bound) w m
  have yl_away (a : Wire) (ha : a∈L.ylow) : a∉L.low :=
    fun bad=>y_away_r hn a (ylowSub ha) (lowSub bad)
  have zy : regValue L.ylow z.basis=regValue L.ylow v.basis :=
    (regValue_congr _ _ _ (fun a ha=>mc.2.1 a (yl_away a ha))).trans
      (regValue_congr _ _ _ (fun a ha=>xc.2.1 a (yl_away a ha)))
  have zl : regValue L.low z.basis=(if s.basis L.ymsb then third else third+1) := by
    rw [mc.2.2,wl,ws]
    cases s.basis L.ymsb <;> simp [Nat.xor_assoc]
  have actual : run (prep L) m s=z := by
    simp only [prep,List.append_assoc,run_append,run_take,
      (copyRegister_counts none L.y L.r (widths.2.2.1.trans widths.2.1.symm)).2,
      (signComplement_counts _ _).2,(xorConstant_counts _ _).2,List.drop_zero,
      Option.isSome_none,Bool.false_eq_true,if_false]
    rw [no_records _ (by simpa only [C] using (xorConstant_counts L.low (third+1)).2) _ (m.take 0) m,
      no_records _ (signComplement_counts _ _).2 _ (m.take 0) m,
      no_records _ (by simpa using (copyRegister_counts none L.y L.r (widths.2.2.1.trans widths.2.1.symm)).2) _ (m.take 0) m]
  rw [actual]
  exact ⟨mc.1.trans (xc.1.trans (yc.1.trans cp.1)),zy.trans (by simpa only [us,uv,hw.2.1] using yc.2.2),zl⟩

private theorem sandwich (P Q : Program) (flag : Wire) (hp : ProperProgram P)
    (hfree : flag∉wires P) (s : State) (m : List Bool) (b : Bool)
    (hQ : run Q m (run P m s)=run (if b then [.X flag] else []) [] (run P m s)) :
    run (P++Q++P.reverse) m s=run (if b then [.X flag] else []) [] s := by
  have hm:=properProgram_measurementCount P hp
  have pr:=properProgram_reverse P hp
  have dis : Disjoint (wires P.reverse) (wires (if b then [.X flag] else [])) := by
    cases b <;> simp [wires,wires_reverse,Instr.wires,Finset.disjoint_singleton_right,hfree]
  have eq := run_disjoint_commute P.reverse (if b then [.X flag] else []) dis
    (m.drop (measurementCount Q)) [] (run P m s)
  simp only [List.append_assoc,run_append,run_take,hm,List.drop_zero]
  rw [no_records P hm s (m.take 0) m,hQ,eq,run_reverse_proper P hp s m (m.drop (measurementCount Q))]

theorem regValue_xor (zs : List Wire) (b : BasisState) (c : Bool) :
    regValue zs (fun q => b q ^^ c)=if c then 2^zs.length-1-regValue zs b else regValue zs b := by
  induction zs with
  | nil => cases c <;> simp [regValue]
  | cons z zs ih =>
    have lt := regValue_lt zs b
    change (if (b z ^^ c) then 1 else 0)+2*regValue zs (fun q => b q ^^ c)=
      if c then 2^(zs.length+1)-1-((if b z then 1 else 0)+2*regValue zs b)
      else (if b z then 1 else 0)+2*regValue zs b
    rw [ih]
    cases c <;> cases b z <;> simp [pow_succ] <;> omega

theorem magnitude_word (L : BalancedCleanup.Layout) (hw : L.Widths) (Y : Int) (hy : Centered Y)
    (u : BasisState) (hyw : regValue L.y u=encodeWord 256 Y) :
    regValue L.ylow (fun q => u q ^^ u L.ymsb)=(magnitude Y).toNat := by
  have mag := BalancedCleanup.magnitude_encoded Y hy
  have hl : L.ylow.length=255 := hw.2.1
  rw [regValue_xor,hl]
  have split : regValue L.y u=regValue L.ylow u+2^255*(if u L.ymsb then 1 else 0) := by
    rw [BalancedCleanup.Layout.y,regValue_append,hl]
    cases hb : u L.ymsb <;> simp [regValue,hb]
  have lt := regValue_lt L.ylow u
  rw [hl] at lt
  have hp := constants
  unfold Centered at hy
  have enc : ((encodeWord 256 Y : Nat) : Int)=if Y<0 then Y+2^256 else Y := by
    unfold encodeWord
    split_ifs with hn
    · have e : Y%((2^256 : Nat) : Int)=Y+2^256 := by
        norm_num at hp ⊢; omega
      rw [e]; norm_num at hp ⊢; omega
    · have e : Y%((2^256 : Nat) : Int)=Y := by
        apply Int.emod_eq_of_lt <;> norm_num at hp ⊢ <;> omega
      rw [e]; omega
  rw [hyw] at split
  by_cases hn : Y<0
  · have neg : negative Y=true := by simp [negative,hn]
    rw [neg,if_pos rfl] at mag
    rw [if_pos hn] at enc
    cases hb : u L.ymsb
    · simp only [hb,Bool.false_eq_true,if_false] at split ⊢
      norm_num at hp; omega
    · simp only [hb,if_true] at split ⊢
      norm_num at hp; omega
  · have pos : negative Y=false := by simp [negative,hn]
    rw [pos] at mag
    simp only [Bool.false_eq_true,if_false] at mag
    rw [if_neg hn] at enc
    cases hb : u L.ymsb
    · simp only [hb,Bool.false_eq_true,if_false] at split ⊢
      norm_num at hp; omega
    · simp only [hb,if_true] at split ⊢
      norm_num at hp; omega


def reducedFlag (B : Bool) (Y : Int) : Bool := B && decide (q<3*|Y|)

theorem threshold_flag (B : Bool) (Y : Int) (hy : Centered Y) :
    (B && !decide ((magnitude Y).toNat < (if negative Y then third else third+1)))=reducedFlag B Y := by
  have c:=constants
  have h3 : (third : Int)*3=q := by decide +kernel
  have hm:=magnitude_bounds Y hy
  have cast:=Int.toNat_of_nonneg hm.1
  have e : (¬(magnitude Y).toNat < (if negative Y then third else third+1)) ↔ q<3*|Y| := by
    by_cases neg : Y<0
    · rw [abs_of_neg neg]
      simp only [magnitude,negative,neg,decide_true,if_true] at cast ⊢
      omega
    · rw [abs_of_nonneg (by omega)]
      simp only [magnitude,negative,neg,decide_false,Bool.false_eq_true,if_false] at cast ⊢
      omega
  unfold reducedFlag
  congr 1
  by_cases h : q<3*|Y|
  · have he:=e.mpr h
    simp [h,he]
  · have he : (magnitude Y).toNat < (if negative Y then third else third+1) := by
      by_contra bad
      exact h (e.mp bad)
    simp [h,he]

theorem prep_free (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sign,L.parity,L.one,L.lower] ∨ a∈L.carry) : a∉wires (prep L) := by
  intro bad
  have mem:=List.mem_toFinset.mp (prep_support bad)
  rcases ha with ha|ha
  · exact flagAway hn a ha (by simp only [List.mem_append] at mem ⊢; tauto)
  · have nd:=BalancedCleanup.Layout.dataND L.toLayout (List.nodup_append'.mp hn).2.1
    have dis:= (List.nodup_append'.mp nd).2.2
    have cya : a∉L.r++L.y := by
      intro h
      rcases List.mem_append.mp h with h|h
      · exact List.disjoint_left.mp dis h (by simp [ha])
      · have dys := (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.2
        exact List.disjoint_left.mp dys h ha
    exact cya (by simp only [List.mem_append] at mem ⊢; tauto)

theorem decision_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (heq : regValue L.r s.basis=regValue L.y s.basis)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (ho : s.basis L.one=false) (hc : ∀a∈L.carry.take 255,s.basis a=false) :
    run (decision L) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ reducedFlag (s.basis L.sign) Y)⟩ := by
  let t:=run (prep L) m s
  have prepared:=prep_data L hw hn s m heq
  have same (a : Wire) (ha : a∈[L.sign,L.parity,L.one,L.lower] ∨ a∈L.carry) : t.basis a=s.basis a :=
    run_preserves_outside (prep L) m s a (prep_free L hn a ha)
  have sg : t.basis L.sign=s.basis L.sign := same _ (Or.inl (by simp))
  have po : t.basis L.parity=s.basis L.parity := same _ (Or.inl (by simp))
  have ci : t.basis L.one=false := (same _ (Or.inl (by simp))).trans ho
  have cl : ∀a∈L.carry.take 255,t.basis a=false :=
    fun a ha=>(same _ (Or.inr (List.mem_of_mem_take ha))).trans (hc a ha)
  have dnd : (L.parity::L.one::(L.ylow++L.low++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ctl : ∀a∈some L.sign,a∉L.parity::L.one::(L.ylow++L.low++L.carry.take 255) := by
    intro a ha; simp only [Option.mem_some_iff] at ha; subst a
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.sign
    intro bad; have b:=List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at h b
    omega
  have w:=BalancedCleanup.widths L.toLayout hw
  let C:=compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
  have cmp:=compareLt_correct (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
    dnd ctl (hw.2.1.trans w.1.symm) (by simp [List.length_take,hw.2.2,w.1]) t m ci cl
  have mag:=magnitude_word L.toLayout hw Y hy s.basis hY
  have msb : s.basis L.ymsb=negative Y := by
    have all:=BalancedCleanup.result_msb
    have split:=regValue_highBit L.ylow L.ymsb s.basis
    have sign:=centerWord_sign (Y:ECDSAAdd.Fp)
    simp only [centerWord,centerFp_of_center Y hy] at sign
    rw [hw.2.1] at split
    change (s.basis L.ymsb=true ↔ 2^255≤regValue L.y s.basis) at split
    rw [hY] at split
    cases hb : s.basis L.ymsb <;> by_cases neg : Y<0 <;>
      simp [negative,neg] <;> simp [hb] at split <;> omega
  have v1 : regValue L.ylow t.basis=(magnitude Y).toNat := by
    rw [←mag,regValue_xor,hw.2.1]; exact prepared.2.1
  have v2 : regValue L.low t.basis=if negative Y then third else third+1 := by
    rw [←msb]; exact prepared.2.2
  have ne : L.sign≠L.parity := by
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.sign
    intro e
    simp only [List.count_cons,←e,beq_self_eq_true,if_true] at h
    omega
  have bvalue : (t.basis L.sign && !decide (regValue L.ylow t.basis<regValue L.low t.basis))=
      reducedFlag (s.basis L.sign) Y := by
    rw [sg,v1,v2]; exact threshold_flag _ _ hy
  have core : run (C++[.CX L.sign L.parity]) m t=
      run (if reducedFlag (s.basis L.sign) Y then [.X L.parity] else []) [] t := by
    rw [run_append]
    have ct:=run_take C m t
    rw [ct]
    apply State.extensionality
    · cases reducedFlag (s.basis L.sign) Y <;> simpa only [run] using cmp.1
    · funext a
      by_cases ae : a=L.parity
      · subst a
        have keep:=cmp.2.1 L.sign ne
        have tv:=cmp.2.2
        simp only [controlValue,Option.map_some,Option.getD_some] at tv
        simp only [run,writeBit,Function.update_self]
        change ((run C m t).basis L.parity ^^ (run C m t).basis L.sign)=_
        rw [tv,keep]
        rw [←bvalue]
        cases hp : t.basis L.parity <;> cases hb : t.basis L.sign <;>
          cases hc : decide (regValue L.ylow t.basis<regValue L.low t.basis) <;>
          simp [run,writeBit,hp,hb,hc]
      · change (writeBit (run C m t).basis L.parity _) a=_
        rw [writeBit,Function.update_of_ne ae,cmp.2.1 a ae]
        cases reducedFlag (s.basis L.sign) Y <;> simp [run,writeBit,ae]
  have sand:=sandwich (prep L) (C++[.CX L.sign L.parity]) L.parity
    (prep_proper hn) (prep_free L hn _ (Or.inl (by simp))) s m (reducedFlag (s.basis L.sign) Y) core
  have assoc : decision L=prep L++(C++[.CX L.sign L.parity])++(prep L).reverse := by
    simp only [decision,C,List.append_assoc]
  rw [assoc,sand]
  cases reducedFlag (s.basis L.sign) Y <;> simp [run,writeBit]


private theorem raw_mod (X H : Nat) (_hh : 0<H) (hx : X<2*H) (B : Bool) :
    (if !B then (2*(X%H)+2*H-X)%(2*H) else (X+2*(X%H))%(2*H))=
      (if B then 3*X else X)%(2*H) := by
  by_cases small : X<H
  · rw [Nat.mod_eq_of_lt small]
    cases B
    · simp only [Bool.not_false,if_true,Bool.false_eq_true,if_false]
      rw [show 2*X+2*H-X=X+2*H by omega,Nat.add_mod_right]
    · simp only [Bool.not_true,Bool.false_eq_true,if_false,if_true]
      congr 1; omega
  · have low : X%H=X-H := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [low]
    cases B
    · simp only [Bool.not_false,if_true,Bool.false_eq_true,if_false]
      rw [show 2*(X-H)+2*H-X=X by omega]
    · simp only [Bool.not_true,Bool.false_eq_true,if_false,if_true]
      have e : 3*X=(X+2*(X-H))+2*H := by omega
      conv_rhs => rw [e,Nat.add_mod_right]

private theorem raw_arithmetic (X : Nat) (hx : X<2^256) (B : Bool) :
    signedWordValue 256 (!B) X (2*(X%2^255))=(if B then 3*X else X)%2^256 := by
  have pow : 2^256=2*(2^255) := by rw [show 256=255+1 from rfl,pow_succ];omega
  have h:=raw_mod X (2^255) (by positivity) (by omega) B
  simpa only [signedWordValue,←pow,Nat.add_comm] using h

theorem double_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (heq : regValue L.r s.basis=regValue L.y s.basis) :
    (run (double L) m s).phase=s.phase ∧
    regValue L.r (run (double L) m s).basis=2*(regValue L.y s.basis%2^255) ∧
    ∀a,a∉L.r → (run (double L) m s).basis a=s.basis a := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have rnd:=(List.nodup_append'.mp (yrND hn)).2.1
  have ra : L.rmsb∉L.low := by
    intro h
    exact List.disjoint_left.mp (List.nodup_append'.mp rnd).2.2 h (by simp)
  have br:=regValue_append L.low [L.rmsb] s.basis
  have byy:=regValue_append L.ylow [L.ymsb] s.basis
  have rl:=regValue_lt L.low s.basis
  have yl:=regValue_lt L.ylow s.basis
  rw [w.1] at br rl
  rw [hw.2.1] at byy yl
  change regValue L.r s.basis=regValue L.low s.basis+2^255*regValue [L.rmsb] s.basis at br
  change regValue L.y s.basis=regValue L.ylow s.basis+2^255*regValue [L.ymsb] s.basis at byy
  have one (a : Wire) : regValue [a] s.basis=if s.basis a then 1 else 0 := rfl
  rw [one] at br byy
  have bits : s.basis L.rmsb=s.basis L.ymsb := by
    cases hr : s.basis L.rmsb <;> cases hy : s.basis L.ymsb <;>
      simp only [hr,hy,Bool.false_eq_true,if_false,if_true] at br byy ⊢ <;> omega
  have lowval : regValue L.low s.basis=regValue L.y s.basis%2^255 := by
    cases hr : s.basis L.rmsb <;> simp only [hr,Bool.false_eq_true,if_false,if_true] at br <;>
      norm_num at br rl ⊢ <;> omega
  let u : State:=⟨s.phase,writeBit s.basis L.rmsb false⟩
  have first (r : List Bool) : run [.CX L.ymsb L.rmsb] r s=u := by
    simp only [run,bits,Bool.xor_self]; rfl
  have ul : regValue L.low u.basis=regValue L.low s.basis := by
    apply regValue_congr; intro a ha
    simp [u,writeBit,show a≠L.rmsb from fun e=>ra (e ▸ ha)]
  have ur : regValue L.r u.basis=regValue L.low s.basis := by
    change regValue (L.low++[L.rmsb]) u.basis=_
    rw [regValue_append,ul]
    simp [regValue,u,writeBit]
  have rs:=rotateLeft_spec L.r rnd (regValue L.low s.basis) (by rw [w.2.1]; norm_num at rl ⊢;omega) u m ur
  have actual : run (double L) m s=run (rotateLeft L.r) m u := by
    simp only [double,run_append,show measurementCount [.CX L.ymsb L.rmsb]=0 from rfl,List.drop_zero,first]
  rw [actual]
  refine ⟨rs.1,rs.2.trans (by rw [lowval]),?_⟩
  intro a ha
  have same:=(rotate_frame L.r u m).2.2.2 a ha
  have am : a≠L.rmsb := fun e=>ha (by simp [BalancedCleanup.Layout.r,e])
  simpa [u,writeBit,am] using same

theorem raw_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (heq : regValue L.r s.basis=regValue L.y s.basis)
    (hc : ∀a∈L.carry.take 255,s.basis a=false) :
    (run (raw L) m s).phase=s.phase ∧
    regValue L.r (run (raw L) m s).basis=
      (if s.basis L.sign then 3*regValue L.y s.basis else regValue L.y s.basis)%2^256 ∧
    ∀a,a∉L.r → (run (raw L) m s).basis a=s.basis a := by
  let u:=run (double L) m s
  let v:=run [.X L.sign] m u
  let z:=run (signedAdd L.sign L.y L.r (L.carry.take 255)) m v
  let t:=run [.X L.sign] m z
  have w:=BalancedCleanup.widths L.toLayout hw
  have dc:=double_correct L hw hn s m heq
  have sg : L.sign∉L.r := fun h=>flagAway (L:=L) hn L.sign (by simp) (by simp [h])
  have sy : L.sign∉L.y := fun h=>flagAway (L:=L) hn L.sign (by simp) (by simp [h])
  have dd : (L.sign::(L.y++L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have csR (a : Wire) (ha : a∈L.carry.take 255) : a∉L.r := by
    intro bad
    have h:=List.nodup_iff_count.mp dd a
    have p1:=List.count_pos_iff.mpr ha
    have p2:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h;omega
  have csS (a : Wire) (ha : a∈L.carry.take 255) : a≠L.sign := by
    intro e
    exact flagAway (L:=L) hn L.sign (by simp) (by simp [←e,List.mem_of_mem_take ha])
  have vs : v.basis L.sign= !s.basis L.sign := by
    simp only [v,run,writeBit,Function.update_self]
    rw [dc.2.2 L.sign sg]
  have vr : regValue L.r v.basis=2*(regValue L.y s.basis%2^255) := by
    apply Eq.trans _ dc.2.1
    apply regValue_congr;intro a ha
    simp [v,u,run,writeBit,show a≠L.sign from fun e=>sg (e ▸ ha)]
  have vy : regValue L.y v.basis=regValue L.y s.basis := by
    apply regValue_congr;intro a ha
    have ar:=y_away_r hn a ha
    have asg : a≠L.sign := fun e=>sy (e ▸ ha)
    simp only [v,run,writeBit,Function.update_of_ne asg]
    exact dc.2.2 a ar
  have vc : regValue (L.carry.take 255) v.basis=0 := by
    apply (regValue_zero _ _).mpr;intro a ha
    simp only [v,run,writeBit,Function.update_of_ne (csS a ha)]
    exact (dc.2.2 a (csR a ha)).trans (hc a ha)
  have cl : (L.carry.take 255).length+1=L.r.length := by simp [List.length_take,hw.2.2,w.2.1]
  have ad:=(signedAdd_spec L.sign L.y L.r (L.carry.take 255) dd (w.2.2.1.trans w.2.1.symm) cl
    (!s.basis L.sign) (regValue L.y s.basis) (2*(regValue L.y s.basis%2^255))) v m ⟨⟨⟨vs,vy⟩,vr⟩,vc⟩
  have frame (a : Wire) (ha : a∉L.r) : z.basis a=v.basis a :=
    (signedWord_frame L.sign L.y L.r (L.carry.take 255) dd (w.2.2.1.trans w.2.1.symm) cl
      (!s.basis L.sign) (regValue L.y s.basis) (2*(regValue L.y s.basis%2^255)) v m vs vy vr vc a ha).1
  have dmc : measurementCount (double L)=0 := by
    simp [double,measurementCount_append,measurementCount,(rotate_counts L.r).2.2.2]
  have actual : run (raw L) m s=t := by
    simp only [raw,List.append_assoc,run_append,run_take,dmc,List.drop_zero]
    rw [no_records (double L) dmc s (m.take 0) m]
    simp only [show measurementCount [.X L.sign]=0 from rfl,List.drop_zero]
    change run [.X L.sign] _ z=t
    exact no_records [.X L.sign] (by rfl) z _ m
  rw [actual]
  refine ⟨ad.1.trans dc.1,?_,?_⟩
  · have tr : regValue L.r t.basis=regValue L.r z.basis := by
      apply regValue_congr;intro a ha
      simp [t,run,writeBit,show a≠L.sign from fun e=>sg (e ▸ ha)]
    rw [tr,ad.2.1.2,w.2.1]
    have hv:=regValue_lt L.y s.basis
    rw [w.2.2.1] at hv
    exact raw_arithmetic _ hv _
  · intro a ha
    by_cases ae : a=L.sign
    · subst a
      simp only [t,run,writeBit,Function.update_self]
      rw [ad.2.1.1.1]
      simp
    · simp only [t,v,run,writeBit,Function.update_of_ne ae,frame a ha]
      exact dc.2.2 a ha


def compWord (N : Bool) (R : Nat) : Nat := if N then 2^256-1-R else R

def correctionValue (N F : Bool) (R : Nat) : Nat :=
  compWord N ((compWord N R+2^256-(if F then p else 0))%2^256)

theorem correction_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hl : s.basis L.one=false)
    (hc : ∀a∈L.carry.take 255,s.basis a=false) :
    (run (correction L) m s).phase=s.phase ∧
    regValue L.r (run (correction L) m s).basis=
      correctionValue (s.basis L.ymsb) (s.basis L.parity) (regValue L.r s.basis) ∧
    ∀a,a∉L.r → (run (correction L) m s).basis a=s.basis a := by
  let A:=signComplement L.ymsb L.r
  let P:=mappedSub (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one
  let u:=run A m s
  let v:=run P m u
  let t:=run A m v
  have w:=BalancedCleanup.widths L.toLayout hw
  have rn:=(List.nodup_append'.mp (yrND hn)).2.1
  have ya:=ysignAwayR hn
  have fa (f : Wire) (hf : f∈[L.sign,L.parity,L.one,L.one]) : f∉L.r :=
    fun h=>flagAway hn f (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hf ⊢;tauto) (by simp [h])
  have ca (a : Wire) (ha : a∈L.carry.take 255) : a∉L.r := by
    intro bad
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    have c:=List.count_pos_iff.mpr ha
    have d:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h;omega
  have first:=signComplement_correct L.ymsb L.r rn ya s m
  have ur : regValue L.r u.basis=compWord (s.basis L.ymsb) (regValue L.r s.basis) := by
    simpa only [compWord,w.2.1] using first.2.2
  have ul : u.basis L.one=false := (first.2.1 _ (fa _ (by simp))).trans hl
  have up : u.basis L.parity=s.basis L.parity := first.2.1 _ (fa _ (by simp))
  have uy : u.basis L.ymsb=s.basis L.ymsb := first.2.1 _ ya
  have uc : ∀a∈L.carry.take 255,u.basis a=false :=
    fun a ha=>(first.2.1 a (ca a ha)).trans (hc a ha)
  have nd : (L.one::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr;intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [List.count_cons,List.count_append] at h ⊢;omega
  have src : ∀a∈mappedWires (mappedConstant (some L.parity) 256 p),a∉L.one::(L.r++L.carry.take 255) := by
    intro a ha
    have pa:=mappedConstant_wires (some L.parity) 256 p a ha
    simp only [Option.mem_some_iff] at pa
    subst a
    intro bad
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.parity
    have c:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h c
    omega
  have step:=mappedSub_correct (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one
    nd src (by rw [mappedConstant_length,w.2.1]) (by simp [List.length_take,hw.2.2,w.2.1]) u m uc ul
  have mv : mappedValue (mappedConstant (some L.parity) 256 p) u.basis=if s.basis L.parity then p else 0 := by
    rw [mappedConstant_value _ _ _ _ (by norm_num [p])]
    simp only [mappedEnabled,Option.map_some,Option.getD_some,up]
  have vr : regValue L.r v.basis=(compWord (s.basis L.ymsb) (regValue L.r s.basis)+2^256-
      (if s.basis L.parity then p else 0))%2^256 := by
    simpa only [P,ur,w.2.1,mv] using step.2.2
  have vy : v.basis L.ymsb=s.basis L.ymsb := (step.2.1 _ ya).trans uy
  have last:=signComplement_correct L.ymsb L.r rn ya v m
  have actual : run (correction L) m s=t := by
    simp only [correction,List.append_assoc,run_append,run_take,(signComplement_counts _ _).2,List.drop_zero]
    change run A _ (run P m (run A (m.take 0) s))=t
    rw [no_records A (signComplement_counts _ _).2 s (m.take 0) m]
    exact no_records A (signComplement_counts _ _).2 v _ m
  rw [actual]
  refine ⟨last.1.trans (step.1.trans first.1),?_,?_⟩
  · simpa only [correctionValue,compWord,vy,vr,w.2.1] using last.2.2
  · intro a ha
    exact (last.2.1 a ha).trans ((step.2.1 a ha).trans (first.2.1 a ha))


def rawValue (B : Bool) (Y : Int) : Int := if B then 3*Y else Y

def resultValue (B : Bool) (Y : Int) : Int :=
  rawValue B Y + (if reducedFlag B Y then (if negative Y then (p:Int) else -(p:Int)) else 0)

private theorem sub_encoded (Y : Int) (d : Nat) (hd : d<2^256) :
    (encodeWord 256 Y+2^256-d)%2^256=encodeWord 256 (Y-(d:Int)) := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod,Nat.cast_sub (show d≤encodeWord 256 Y+2^256 by omega),
    Nat.cast_add,encodeWord_cast,encodeWord_cast]
  simp only [Int.sub_emod,Int.add_emod,Int.emod_emod,Int.emod_self,Int.add_zero]

private theorem mul_encoded (Y : Int) :
    (3*encodeWord 256 Y)%2^256=encodeWord 256 (3*Y) := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod,Nat.cast_mul,encodeWord_cast,encodeWord_cast]
  simp only [Nat.cast_ofNat,Int.mul_emod,Int.emod_emod]

private theorem correction_none (N : Bool) (R : Nat) (hr : R<2^256) :
    correctionValue N false R=R := by
  unfold correctionValue compWord
  cases N
  · simp only [Bool.false_eq_true,if_false,Nat.sub_zero]
    rw [Nat.add_mod_right,Nat.mod_eq_of_lt hr]
  · simp only [if_true,Bool.false_eq_true,if_false,Nat.sub_zero]
    have ht : 2^256-1-R<2^256 := by omega
    rw [Nat.add_mod_right,Nat.mod_eq_of_lt ht]
    omega

private theorem correction_pos (Y : Int) :
    correctionValue false true (encodeWord 256 Y)=encodeWord 256 (Y-(p:Int)) := by
  unfold correctionValue compWord
  simp only [Bool.false_eq_true,if_false,if_true]
  exact sub_encoded Y p (by norm_num [p])

private theorem correction_neg (Y : Int) :
    correctionValue true true (encodeWord 256 Y)=encodeWord 256 (Y+(p:Int)) := by
  unfold correctionValue compWord
  simp only [if_true]
  rw [BalancedCleanup.complement_encoded,sub_encoded _ p (by norm_num [p]),BalancedCleanup.complement_encoded]
  congr 1;ring

theorem correction_encoded (B : Bool) (Y : Int) :
    correctionValue (negative Y) (reducedFlag B Y) (encodeWord 256 (rawValue B Y))=
      encodeWord 256 (resultValue B Y) := by
  unfold resultValue
  cases hn : negative Y <;> cases hf : reducedFlag B Y
  · simp only [Bool.false_eq_true,if_false,Int.add_zero]
    exact correction_none false _ (encodeWord_bound _ _)
  · simp only [Bool.false_eq_true,if_false,if_true]
    simpa only [sub_eq_add_neg] using correction_pos (rawValue B Y)
  · simp only [if_true,Bool.false_eq_true,if_false,Int.add_zero]
    exact correction_none true _ (encodeWord_bound _ _)
  · simp only [if_true]
    exact correction_neg (rawValue B Y)

theorem result_centered (B : Bool) (Y : Int) (hy : Centered Y) :
    Centered (resultValue B Y) := by
  have c:=constants
  unfold Centered at hy ⊢
  unfold resultValue rawValue reducedFlag negative
  cases B
  · simp only [Bool.false_eq_true,Bool.false_and,if_false,Int.add_zero];exact hy
  · simp only [if_true,Bool.true_and]
    by_cases neg : Y<0
    · rw [abs_of_neg neg]
      simp only [neg,decide_true,if_true]
      split_ifs <;> simp_all only [decide_eq_true_eq] <;> omega
    · rw [abs_of_nonneg (by omega)]
      simp only [neg,decide_false,Bool.false_eq_true,if_false]
      split_ifs <;> simp_all only [decide_eq_true_eq] <;> omega

theorem result_cast (B : Bool) (Y : Int) :
    (resultValue B Y:ECDSAAdd.Fp)=(if B then 3*(Y:ECDSAAdd.Fp) else (Y:ECDSAAdd.Fp)) := by
  unfold resultValue rawValue
  split_ifs <;> simp [Int.cast_add,Int.cast_neg,Int.cast_mul]

private theorem reduction_parity (B F N : Bool) (Y : Int) :
    decide (((if B then 3*Y else Y)+(if F then (if N then (p:Int) else -(p:Int)) else 0))%2≠Y%2)=F := by
  have odd : (p:Int)%2=1 := by norm_num [p]
  cases B <;> cases F <;> cases N <;>
    simp only [Bool.false_eq_true,if_false,if_true,Int.add_zero] <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [decide_eq_true_eq,Bool.false_eq_true,iff_false,not_not,iff_true] <;> omega

theorem result_parity (B : Bool) (Y : Int) :
    decide (resultValue B Y%2≠Y%2)=reducedFlag B Y := by
  exact reduction_parity B (reducedFlag B Y) (negative Y) Y

private theorem encode_parity (Y : Int) : ((encodeWord 256 Y%2:Nat):Int)=Y%2 := by
  have a:=encodeWord_cast 256 Y
  norm_num only [Nat.reducePow] at a
  omega


def Frame (L : Layout) (base : BasisState) (R : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue L.r s=R ∧ s L.parity=F ∧ ∀a,a∉L.r → a≠L.parity → s a=base a

theorem frame_y (L : Layout) (hn : L.wires.Nodup) (base : BasisState) (R : Nat) (F : Bool)
    (s : BasisState) (h : Frame L base R F s) : regValue L.y s=regValue L.y base := by
  apply regValue_congr;intro a ha
  have ap : a≠L.parity := fun e=>flagAway hn L.parity (by simp) (by simp [←e,ha])
  exact h.2.2 a (y_away_r hn a ha) ap

theorem frame_flag (L : Layout) (hn : L.wires.Nodup) (base : BasisState) (R : Nat) (F : Bool)
    (s : BasisState) (h : Frame L base R F s) (a : Wire)
    (ha : a∈[L.sign,L.one,L.lower] ∨ a∈L.carry.take 255) : s a=base a := by
  have cnt:=List.nodup_iff_count.mp (inventoryND hn) a
  have pos : 0<(L.sign::L.one::L.lower::L.carry.take 255).count a :=
    List.count_pos_iff.mpr (by simp only [List.mem_cons,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢;tauto)
  have ar : a∉L.r := by
    intro bad; have p:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at cnt pos;omega
  have ap : a≠L.parity := by
    intro e;subst a
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at cnt pos;omega
  exact h.2.2 a ar ap

theorem decision_triple (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (Y : Int) (hy : Centered Y) (hY : regValue L.y base=encodeWord 256 Y)
    (ho : base L.one=false) (hc : ∀a∈L.carry.take 255,base a=false) :
    Triple (Frame L base (encodeWord 256 Y) false) (decision L)
      (Frame L base (encodeWord 256 Y) (reducedFlag (base L.sign) Y)) := by
  intro s m h
  have y:=frame_y L hn base _ _ s.basis h
  have sy:=frame_flag L hn base _ _ s.basis h L.sign (Or.inl (by simp))
  have o:=(frame_flag L hn base _ _ s.basis h L.one (Or.inl (by simp))).trans ho
  have c : ∀a∈L.carry.take 255,s.basis a=false :=
    fun a ha=>(frame_flag L hn base _ _ s.basis h a (Or.inr ha)).trans (hc a ha)
  rw [decision_correct L hw hn Y hy s m (h.1.trans (y.trans hY).symm) (y.trans hY) o c]
  have pr : L.parity∉L.r := fun bad=>flagAway hn L.parity (by simp) (by simp [bad])
  refine ⟨rfl,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun a ha=>by simp [writeBit,show a≠L.parity from fun e=>pr (e ▸ ha)])).trans h.1
  · simp [writeBit,h.2.1,sy]
  · intro a ar ap;simpa [writeBit,ap] using h.2.2 a ar ap

theorem raw_triple (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (Y : Int) (hY : regValue L.y base=encodeWord 256 Y)
    (hc : ∀a∈L.carry.take 255,base a=false) (F : Bool) :
    Triple (Frame L base (encodeWord 256 Y) F) (raw L)
      (Frame L base (encodeWord 256 (rawValue (base L.sign) Y)) F) := by
  intro s m h
  have y:=frame_y L hn base _ _ s.basis h
  have sy:=frame_flag L hn base _ _ s.basis h L.sign (Or.inl (by simp))
  have c : ∀a∈L.carry.take 255,s.basis a=false :=
    fun a ha=>(frame_flag L hn base _ _ s.basis h a (Or.inr ha)).trans (hc a ha)
  have r:=raw_correct L hw hn s m (h.1.trans (y.trans hY).symm) c
  have pr : L.parity∉L.r := fun bad=>flagAway hn L.parity (by simp) (by simp [bad])
  refine ⟨r.1,?_,(r.2.2 _ pr).trans h.2.1,?_⟩
  · rw [r.2.1,y,hY,sy]
    cases base L.sign
    · simpa only [rawValue,Bool.false_eq_true,if_false] using Nat.mod_eq_of_lt (encodeWord_bound 256 Y)
    · simpa only [rawValue,if_true] using mul_encoded Y
  · intro a ar ap;exact (r.2.2 a ar).trans (h.2.2 a ar ap)

theorem correction_triple (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (Y : Int) (hy : Centered Y) (hY : regValue L.y base=encodeWord 256 Y)
    (hl : base L.one=false) (hc : ∀a∈L.carry.take 255,base a=false) :
    Triple (Frame L base (encodeWord 256 (rawValue (base L.sign) Y)) (reducedFlag (base L.sign) Y))
      (correction L) (Frame L base (encodeWord 256 (resultValue (base L.sign) Y)) (reducedFlag (base L.sign) Y)) := by
  intro s m h
  have y:=frame_y L hn base _ _ s.basis h
  have l:=(frame_flag L hn base _ _ s.basis h L.one (Or.inl (by simp))).trans hl
  have c : ∀a∈L.carry.take 255,s.basis a=false :=
    fun a ha=>(frame_flag L hn base _ _ s.basis h a (Or.inr ha)).trans (hc a ha)
  have msb : s.basis L.ymsb=negative Y := by
    have split:=regValue_highBit L.ylow L.ymsb s.basis
    have sign:=centerWord_sign (Y:ECDSAAdd.Fp)
    simp only [centerWord,centerFp_of_center Y hy] at sign
    rw [hw.2.1] at split
    change (s.basis L.ymsb=true ↔ 2^255≤regValue L.y s.basis) at split
    rw [y,hY] at split
    cases hb : s.basis L.ymsb <;> by_cases neg : Y<0 <;>
      simp [negative,neg] <;> simp [hb] at split <;> omega
  have r:=correction_correct L hw hn s m l c
  have pr : L.parity∉L.r := fun bad=>flagAway hn L.parity (by simp) (by simp [bad])
  refine ⟨r.1,?_,(r.2.2 _ pr).trans h.2.1,?_⟩
  · rw [r.2.1,msb,h.1,h.2.1]
    exact correction_encoded _ _
  · intro a ar ap;exact (r.2.2 a ar).trans (h.2.2 a ar ap)

private theorem head_mod (a : Wire) (xs : List Wire) (s : BasisState) :
    regValue (a::xs) s%2=(s a).toNat := by
  change ((if s a then 1 else 0)+2*regValue xs s)%2=_
  cases s a <;> simp

theorem erase_triple (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (Y : Int) (hY : regValue L.y base=encodeWord 256 Y) :
    Triple (Frame L base (encodeWord 256 (resultValue (base L.sign) Y)) (reducedFlag (base L.sign) Y))
      [.CX L.r0 L.parity,.CX (L.ylow.headD L.ymsb) L.parity]
      (Frame L base (encodeWord 256 (resultValue (base L.sign) Y)) false) := by
  intro s m h
  have pr : L.parity∉L.r := fun bad=>flagAway hn L.parity (by simp) (by simp [bad])
  have py : L.parity∉L.y := fun bad=>flagAway hn L.parity (by simp) (by simp [bad])
  have rp : L.r0≠L.parity := fun e=>pr (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  have yshape : L.y=(L.ylow.headD L.ymsb)::(L.ylow.drop 1++[L.ymsb]) := by
    cases e : L.ylow with
    | nil => have w:=hw.2.1;rw [e] at w;contradiction
    | cons a xs => simp only [BalancedCleanup.Layout.y,e,List.headD_cons,List.drop_succ_cons,List.drop_zero,List.cons_append]
  have yp : L.ylow.headD L.ymsb≠L.parity := by
    intro e;apply py;rw [yshape];exact List.mem_cons.mpr (Or.inl e.symm)
  have rb:=head_mod L.r0 (L.rtail++[L.rmsb]) s.basis
  change regValue L.r s.basis%2=(s.basis L.r0).toNat at rb
  have yb:=head_mod (L.ylow.headD L.ymsb) (L.ylow.drop 1++[L.ymsb]) s.basis
  rw [←yshape,frame_y L hn base _ _ s.basis h,hY] at yb
  rw [h.1] at rb
  have e1:=encode_parity (resultValue (base L.sign) Y)
  have e2:=encode_parity Y
  rw [rb] at e1
  rw [yb] at e2
  have ep:=result_parity (base L.sign) Y
  have erase : (s.basis L.parity ^^ s.basis L.r0 ^^ s.basis (L.ylow.headD L.ymsb))=false := by
    rw [h.2.1,←ep,←e1,←e2]
    cases hr : s.basis L.r0 <;> cases hy : s.basis (L.ylow.headD L.ymsb) <;> simp [hr,hy]
  have actual : run [.CX L.r0 L.parity,.CX (L.ylow.headD L.ymsb) L.parity] m s=
      ⟨s.phase,writeBit s.basis L.parity false⟩ := by
    simp only [run,writeBit,Function.update_of_ne rp,Function.update_of_ne yp]
    apply congrArg (State.mk s.phase);funext a
    by_cases ae : a=L.parity
    · subst a;simp only [Function.update_self];exact erase
    · simp [Function.update_of_ne ae]
  rw [actual]
  refine ⟨rfl,?_,by simp [writeBit],?_⟩
  · exact (regValue_congr _ _ _ (fun a ha=>by simp [writeBit,show a≠L.parity from fun e=>pr (e ▸ ha)])).trans h.1
  · intro a ar ap;simpa [writeBit,ap] using h.2.2 a ar ap

theorem program_triple (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (Y : Int) (hy : Centered Y) (hY : regValue L.y base=encodeWord 256 Y)
    (ho : base L.one=false) (_hl : base L.lower=false) (hc : ∀a∈L.carry.take 255,base a=false) :
    Triple (Frame L base (encodeWord 256 Y) false) (program L)
      (Frame L base (encodeWord 256 (resultValue (base L.sign) Y)) false) := by
  have d:=decision_triple L hw hn base Y hy hY ho hc
  have r:=raw_triple L hw hn base Y hY hc (reducedFlag (base L.sign) Y)
  have c:=correction_triple L hw hn base Y hy hY ho hc
  have e:=erase_triple L hw hn base Y hY
  simpa only [program,List.append_assoc] using ((d.seq r).seq c).seq e


theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀a∈work L,s.basis a=false) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.r (run (program L) m s).basis=encodeWord 256 (resultValue (s.basis L.sign) Y) ∧
    ∀a,a∉L.r → (run (program L) m s).basis a=s.basis a := by
  have c : ∀a∈L.carry.take 255,s.basis a=false := fun a ha=>hc a (by simp [work,List.mem_of_mem_take ha])
  have t:=program_triple L hw hn s.basis Y hy hY (hc _ (by simp [work]))
    (hc _ (by simp [work])) c s m ⟨hR,hc _ (by simp [work]),fun _ _ _=>rfl⟩
  refine ⟨t.1,t.2.1,?_⟩
  intro a ar
  by_cases ap : a=L.parity
  · subst a;exact t.2.2.1.trans (hc _ (by simp [work])).symm
  · exact t.2.2.2 a ar ap


def sites (L : Layout) : Finset Wire :=
  (L.sign::L.parity::L.one::L.lower::(L.y++L.r++L.carry.take 255)).toFinset

theorem support (L : Layout) (hw : L.Widths) : wires (program L)⊆sites L := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have pp : wires (prep L)⊆sites L := (prep_support (L:=L)).trans (by
    intro a ha
    simp only [sites,List.mem_toFinset,List.mem_cons,List.mem_append] at ha ⊢;tauto)
  have cp : wires (compareLt (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity)⊆sites L := by
    rw [(compareLt_wires (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
      (hw.2.1.trans w.1.symm) (by simp [List.length_take,hw.2.2,w.1])).1]
    intro a ha
    simp only [sites,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,Option.toList_some,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at ha ⊢;tauto
  have rot : wires (rotateLeft L.r)⊆sites L := by
    rw [(rotate_wires L.r).2]
    split_ifs
    · exact Finset.empty_subset _
    · intro a ha
      simp only [sites,List.mem_toFinset,List.mem_cons,List.mem_append] at ha ⊢;tauto
  have sc : wires (signComplement L.ymsb L.r)⊆sites L :=
    (signComplement_wires_subset _ _).trans (by
      intro a ha
      simp only [sites,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton] at ha ⊢;tauto)
  have ad : wires (signedAdd L.sign L.y L.r (L.carry.take 255))⊆sites L := by
    rw [(signedWord_wires L.sign L.y L.r (L.carry.take 255) (w.2.2.1.trans w.2.1.symm)
      (by simp [List.length_take,hw.2.2,w.2.1])).1]
    intro a ha
    simp only [sites,List.mem_toFinset,List.mem_cons,List.mem_append] at ha ⊢;tauto
  have su : wires (mappedSub (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one)⊆sites L := by
    intro a ha
    have h:=List.mem_toFinset.mp (mappedSub_wires_subset _ _ _ _ ha)
    have bit : a∈mappedWires (mappedConstant (some L.parity) 256 p) → a=L.parity := by
      intro hm
      exact (Option.mem_some_iff.mp (mappedConstant_wires (some L.parity) 256 p a hm)).symm
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    simp only [sites,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  have ys : L.ylow.headD L.ymsb∈L.y := by
    cases e : L.ylow with
    | nil => simp [BalancedCleanup.Layout.y,e]
    | cons a xs => simp [BalancedCleanup.Layout.y,e]
  have one (a : Wire) (ha : a∈sites L) : wires [.X a]⊆sites L := by simpa [wires,Instr.wires] using ha
  have two (a b : Wire) (ha : a∈sites L) (hb : b∈sites L) : wires [.CX a b]⊆sites L := by
    simp only [wires,Instr.wires,Finset.union_empty,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨ha,hb⟩
  have sf : L.sign∈sites L := by simp [sites]
  have pf : L.parity∈sites L := by simp [sites]
  have ym : L.ymsb∈sites L := by simp [sites,BalancedCleanup.Layout.y]
  have rm : L.rmsb∈sites L := by simp [sites,BalancedCleanup.Layout.r]
  have rr : L.r0∈sites L := by simp [sites,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have yy : L.ylow.headD L.ymsb∈sites L := by
    simp only [sites,List.mem_toFinset,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ys)))))
  have last : wires [.CX L.r0 L.parity,.CX (L.ylow.headD L.ymsb) L.parity]⊆sites L := by
    change wires ([.CX L.r0 L.parity]++[.CX (L.ylow.headD L.ymsb) L.parity])⊆_
    rw [wires_append]
    exact Finset.union_subset (two _ _ rr pf) (two _ _ yy pf)
  simp only [program,decision,raw,double,correction,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨pp,cp⟩,two _ _ sf pf⟩,pp⟩,⟨⟨⟨two _ _ ym rm,rot⟩,one _ sf⟩,ad⟩,one _ sf⟩,
    ⟨⟨sc,su⟩,sc⟩⟩,last⟩

theorem gateSlots_le (L : Layout) (hw : L.Widths) : Challenge.gateSlots (program L)≤25000 := by
  open Baselines Challenge in
  have w:=BalancedCleanup.widths L.toLayout hw
  have p1:=xorConstant_gateSlots_le L.low (third+1)
  have p2:=maskedConstant_gateSlots_le L.ymsb L.low ((third+1)^^^third)
  have pp : gateSlots (prep L)≤1021 := by
    simp only [prep,gateSlots_append,copyRegister_gateSlots,signComplement_gateSlots,w.2.2.1,w.2.1,hw.2.1,w.1]
    rw [w.1] at p1 p2
    omega
  have cm:=compareLt_gateSlots_le (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity
  have ro:=(rotate_gateSlots_le L.r).2
  have ad:=(signedWord_gateSlots_le L.sign L.y L.r (L.carry.take 255)).1
  have su:=mappedSub_gateSlots_le (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one
  rw [hw.2.1,w.1] at cm
  rw [w.2.1] at ro
  rw [w.2.2.1] at ad
  rw [mappedConstant_length,w.2.1] at su
  simp only [program,decision,raw,double,correction,gateSlots_append,reverse_gateSlots,
    signComplement_gateSlots,w.2.1,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega


theorem physical (L : Layout) (_hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) := by
  have pp : GatePhysical (prep L) :=
    (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _ (prep_proper hn))
  have rev : GatePhysical (prep L).reverse :=
    (RecordedQuantum.physical_embed _).mp (RecordedQuantum.physical_of_proper _
      (properProgram_reverse _ (prep_proper hn)))
  have dnd : (L.parity::L.one::(L.ylow++L.low++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr;intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢;omega
  have ctl : ∀a∈some L.sign,a∉L.parity::L.one::(L.ylow++L.low++L.carry.take 255) := by
    intro a ha;rw [Option.mem_some_iff] at ha;subst a
    intro bad
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.sign
    have pos:=List.count_pos_iff.mpr bad
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at h pos;omega
  have cp:=compareLt_physical (some L.sign) L.ylow L.low (L.carry.take 255) L.one L.parity dnd (fun a ha e=>ctl a ha (by simp [e]))
  have rnd:=(List.nodup_append'.mp (yrND hn)).2.1
  have rot:=(rotate_physical L.r rnd).2
  have dd : (L.sign::(L.y++L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr;intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [List.count_cons,List.count_append] at h ⊢;omega
  have ad:=(signedWords_physical L.sign L.y L.r (L.carry.take 255) dd).1
  have sc:=signComplement_physical L.ymsb L.r (ysignAwayR hn)
  have nd : (L.one::(L.r++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr;intro a
    have h:=List.nodup_iff_count.mp (inventoryND hn) a
    simp only [List.count_cons,List.count_append] at h ⊢;omega
  have src : ∀b∈mappedConstant (some L.parity) 256 p,∀a∈b.wire,a∉L.one::(L.r++L.carry.take 255) := by
    intro b hb a ha
    have mm : a∈mappedWires (mappedConstant (some L.parity) 256 p) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using ha⟩
    have pa:=mappedConstant_wires (some L.parity) 256 p a mm
    rw [Option.mem_some_iff] at pa;subst a
    intro bad
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.parity
    have pos:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos;omega
  have ma:=mappedAdd_physical (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one nd src
  have su : GatePhysical (mappedSub (mappedConstant (some L.parity) 256 p) L.r (L.carry.take 255) L.one) := by
    simp only [mappedSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,ma⟩,notRegister_physical _⟩
  have one (a : Wire) : GatePhysical [.X a] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  have two (a b : Wire) (ne : a≠b) : GatePhysical [.CX a b] := by
    simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using ne
  have sp : L.sign≠L.parity := by
    have h:=List.nodup_iff_count.mp (inventoryND hn) L.sign
    intro e;simp only [List.count_cons,←e,beq_self_eq_true,if_true] at h;omega
  have yp : L.ymsb≠L.rmsb := fun e=>ysignAwayR hn (by simp [BalancedCleanup.Layout.r,←e])
  have rp : L.r0≠L.parity := fun e=>flagAway hn L.parity (by simp)
    (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,←e])
  have head : L.ylow.headD L.ymsb∈L.y := by
    cases e:L.ylow with
    | nil=>simp [BalancedCleanup.Layout.y,e]
    | cons a xs=>simp [BalancedCleanup.Layout.y,e]
  have hp : L.ylow.headD L.ymsb≠L.parity := fun e=>flagAway hn L.parity (by simp)
    (List.mem_append_left _ (List.mem_append_left _ (e ▸ head)))
  have last : GatePhysical [.CX L.r0 L.parity,.CX (L.ylow.headD L.ymsb) L.parity] := by
    change GatePhysical ([.CX L.r0 L.parity]++[.CX (L.ylow.headD L.ymsb) L.parity])
    exact (gatePhysical_append _ _).mpr ⟨two _ _ rp,two _ _ hp⟩
  simp only [program,decision,raw,double,correction,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨pp,cp⟩,two _ _ sp⟩,rev⟩,⟨⟨⟨two _ _ yp,rot⟩,one _⟩,ad⟩,one _⟩,
    ⟨⟨sc,su⟩,sc⟩⟩,last⟩

end ECDSAAdd.Entrant.InverseTailC
namespace ECDSAAdd.Entrant.InverseTailC
open ECDSAAdd Arithmetic BalancedField BalancedCircuit
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem program_ignores_lower (L : Layout) : program {L with lower:=L.one}=program L := rfl

theorem lower_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : L.lower∉wires (program L) := by
  have sub:=support {L with lower:=L.one} hw
  rw [program_ignores_lower] at sub
  intro bad
  have mem:=List.mem_toFinset.mp (sub bad)
  have pos:=List.count_pos_iff.mpr mem
  have count:=List.nodup_iff_count.mp (inventoryND hn) L.lower
  simp only [sites,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.count_cons,List.count_append,beq_self_eq_true,if_true] at pos count
  omega

def last (L : Layout) : Wire:=L.carry.getD 254 0

def borrowSwap (L : Layout) : Equiv.Perm Wire:=Equiv.swap (last L) L.lower

def borrowed (L : Layout) : Program:=renameProgram (borrowSwap L) (program L)

theorem last_mem (L : Layout) (hw : L.Widths) : last L∈L.carry := by
  have idx:254<L.carry.length:=by rw [hw.2.2];omega
  rw [last,List.getD_eq_getElem _ _ idx]
  exact List.getElem_mem _

theorem borrowed_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀a∈work L,s.basis a=false) :
    run (borrowed L) m s=run (program L) m s := by
  have a: last L∈work L := by simp [work,last_mem L hw]
  have b: L.lower∈work L := by simp [work]
  have r:=program_correct L hw hn Y hy s m hR hY hc
  have ar:=(OneBankCore5.work_away L hn _ a).1
  have br:=(OneBankCore5.work_away L hn _ b).1
  have afterA : (run (program L) m s).basis (last L)=false := (r.2.2 _ ar).trans (hc _ a)
  have afterB : (run (program L) m s).basis L.lower=false := (r.2.2 _ br).trans (hc _ b)
  exact FieldFrameOB5.rebind_swap_run (last L) L.lower (program L) s m (hc _ a) (hc _ b) afterA afterB

theorem borrowed_retired (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : last L∉wires (borrowed L) := by
  intro bad
  rw [borrowed,renameProgram_support] at bad
  obtain ⟨a,ha,e⟩:=Finset.mem_image.mp bad
  have b : borrowSwap L L.lower=last L := by simp [borrowSwap]
  have eq : a=L.lower := (borrowSwap L).injective (e.trans b.symm)
  subst a
  exact lower_free L hw hn ha

theorem borrowed_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (borrowed L)=766 ∧ measurementCount (borrowed L)=765 := by
  simpa only [borrowed,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using counts L hw

theorem borrowed_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (borrowed L) :=
  gatePhysical_rename (borrowSwap L) (borrowSwap L).injective _ (physical L hw hn)

theorem borrowed_slots (L : Layout) (hw : L.Widths) : Challenge.gateSlots (borrowed L)≤25000 := by
  simpa only [borrowed,Baselines.rename_gateSlots] using gateSlots_le L hw

end ECDSAAdd.Entrant.InverseTailC

namespace ECDSAAdd.Entrant.InverseTailC
open ECDSAAdd Arithmetic Secp256k1 BalancedField BalancedCircuit
theorem result_eq (B : Bool) (Y : Int) (hy : Centered Y) :
    resultValue B Y=BalancedInverse.result B Y Y := by
  rw [BalancedInverse.result,←centerFp_of_center (resultValue B Y) (result_centered B Y hy)]
  congr 1
  rw [result_cast]
  cases B <;> simp [signedY,Int.cast_sub,Int.cast_mul] <;> ring

theorem inverse_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m m' : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀a∈work L,s.basis a=false) :
    run (program L) m s=run (FifthCarry2.inverse L) m' s := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have c:=constants
  have range : -((2^(256-1):Nat):Int)≤Y ∧ Y<((2^(256-1):Nat):Int) := by
    unfold Centered at hy
    norm_num only [Nat.reduceSub] at c ⊢;omega
  have dr : signedRegValue L.r s.basis=Y := by
    rw [signedRegValue,w.2.1,hR]
    exact decode_encodeWord 256 (by omega) Y range
  have dy : signedRegValue L.y s.basis=Y := by
    rw [signedRegValue,w.2.2.1,hY]
    exact decode_encodeWord 256 (by omega) Y range
  have fresh:=program_correct L hw hn Y hy s m hR hY hc
  have old:=FifthCarry2.inverse_correct L hw hn (s.basis L.sign) Y Y hy hy s m' rfl dr dy hc
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext a
    by_cases ar : a∈L.r
    · exact (regValue_eq_iff L.r _ _).mp
        ((fresh.2.1.trans (congrArg (encodeWord 256) (result_eq _ _ hy))).trans old.2.1.symm) a ar
    · exact (fresh.2.2 a ar).trans (old.2.2.2 a ar).symm

theorem borrowed_half_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (hc : ∀a∈work L,origin a=false) (Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame L.r L.y origin (centerWord Y) (centerWord Y) s.basis) :
    run ([.X L.sign]++borrowed L++[.X L.sign]) m s=run (OneBankCore5.half false L) m s := by
  have aw:=BalancedCircuit.flagAway L hn L.sign (by simp)
  have sr : L.sign∉L.r := fun hh=>aw (by simp [hh])
  have sy : L.sign∉L.y := fun hh=>aw (by simp [hh])
  let u:=run [.X L.sign] m s
  have keep (a : Wire) (ha : a≠L.sign) : u.basis a=s.basis a := by simp [u,run,writeBit,ha]
  have ur : regValue L.r u.basis=encodeWord 256 (centerFp Y) := by
    apply Eq.trans _ h.1
    exact regValue_congr _ _ _ (fun a ha=>keep a (fun e=>sr (e ▸ ha)))
  have uy : regValue L.y u.basis=encodeWord 256 (centerFp Y) := by
    apply Eq.trans _ h.2.1
    exact regValue_congr _ _ _ (fun a ha=>keep a (fun e=>sy (e ▸ ha)))
  have uc : ∀a∈work L,u.basis a=false := by
    intro a ha
    have away:=OneBankCore5.work_away L hn a ha
    have ns : a≠L.sign := fun e=>OneBankCore5.sign_work L hn (e ▸ ha)
    exact (keep a ns).trans ((h.2.2 a away.1 away.2).trans (hc a ha))
  have eq:=(borrowed_eq L hw hn (centerFp Y) (centerFp_bounds Y) u m ur uy uc).trans
    (inverse_eq L hw hn (centerFp Y) (centerFp_bounds Y) u m m ur uy uc)
  change run ([.X L.sign]++borrowed L++[.X L.sign]) m s=
    run ([.X L.sign]++FifthCarry2.inverse L++[.X L.sign]) m s
  simp only [List.append_assoc,run_append,run_take,show measurementCount [.X L.sign]=0 from rfl,List.drop_zero]
  change run [.X L.sign] _ (run (borrowed L) m u)=run [.X L.sign] _ (run (FifthCarry2.inverse L) m u)
  rw [eq]
  rfl



theorem borrowed_half_q6_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (origin : BasisState) (hc : ∀a∈work L,origin a=false) (Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame L.r L.y origin (centerWord Y) (centerWord Y) s.basis) :
    run ([.X L.sign]++borrowed L++[.X L.sign]) m s=run (OwnQ6Core5.half false L) m s := by
  have fresh:=borrowed_half_eq L hw hn origin hc Y s m h
  have old:=OneBankCore5.half_eq false L hw hn origin hc Y Y s m h
  have q6:=OwnQ6Core5.half_eq false L hw hn origin hc Y Y s m h
  have same : run (OneBankCore5.oldHalf false L) m s=run (OwnQ6Core5.oldHalf false L) m s := rfl
  exact fresh.trans (old.trans (same.trans q6.symm))

end ECDSAAdd.Entrant.InverseTailC
end InverseEndpointBorrowed

section EndpointBorrowSupport
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.InverseEndpointC
open ECDSAAdd Arithmetic Secp256k1 BalancedField BalancedCircuit MappedCompressed
attribute [local irreducible] run wires InverseTailC.borrowed List.toFinset

def half (L : Layout) : Program := [.X L.sign]++InverseTailC.borrowed L++[.X L.sign]

def sites (L : Layout) : Finset Wire := InverseTailC.sites L

theorem support (L : Layout) (hw : L.Widths) : wires (half L)⊆sites L := by
  have low : L.lower∈sites L := by simp [sites,InverseTailC.sites]
  have last : InverseTailC.last L∈sites L := by
    have le : 254<(L.carry.take 255).length := by simp [List.length_take,hw.2.2]
    have i : 254<L.carry.length := by rw [hw.2.2];omega
    have mem : InverseTailC.last L∈L.carry.take 255 := by
      rw [InverseTailC.last,List.getD_eq_getElem _ _ i]
      have mem : (L.carry.take 255)[254]'le∈L.carry.take 255 := List.getElem_mem le
      simpa only [List.getElem_take] using mem
    simp [sites,InverseTailC.sites,mem]
  have borrowed : wires (InverseTailC.borrowed L)⊆sites L := by
    rw [InverseTailC.borrowed,renameProgram_support]
    intro q hq
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hq
    have old:=InverseTailC.support L hw ha
    by_cases x : a=InverseTailC.last L
    · subst a;simpa only [InverseTailC.borrowSwap,Equiv.swap_apply_left] using low
    · by_cases y : a=L.lower
      · subst a;simpa only [InverseTailC.borrowSwap,Equiv.swap_apply_right] using last
      · simpa only [InverseTailC.borrowSwap,Equiv.swap_apply_of_ne_of_ne x y] using old
  have sign : L.sign∈sites L := by simp [sites,InverseTailC.sites]
  simpa only [half,wires_append,wires,Instr.wires,Finset.union_empty,
    Finset.union_subset_iff,Finset.singleton_subset_iff] using And.intro (And.intro sign borrowed) sign

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (half L)=766 ∧ measurementCount (half L)=765 := by
  have c:=InverseTailC.borrowed_counts L hw
  simpa only [half,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.zero_add] using c

theorem physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (half L) := by
  have x : GatePhysical [.X L.sign] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨x,InverseTailC.borrowed_physical L hw hn⟩,x⟩

theorem sites_subset (L : Layout) : sites L⊆L.wires.toFinset := by
  intro a h
  have carry : a∈L.carry.take 255 → a∈L.carry := List.mem_of_mem_take
  simp only [sites,InverseTailC.sites,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h ⊢
  tauto

theorem gateSlots_le (L : Layout) (hw : L.Widths) : Challenge.gateSlots (half L)≤25002 := by
  have h:=InverseTailC.borrowed_slots L hw
  have x : Challenge.gateSlots [Instr.X L.sign]=1 := rfl
  simp only [half,Challenge.gateSlots_append,x]
  omega


end ECDSAAdd.Entrant.InverseEndpointC
end EndpointBorrowSupport


section QSiteDirectControls
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectControls
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 BalancedField
abbrev R:= (balancedSharedPorts base (base 2409)).r
abbrev YR:= (balancedSharedPorts base (base 2409)).y

def borrow : Equiv.Perm Wire:=Equiv.swap (base 1540) (base 2409)
def half (divide : Bool) (g:Wire) : Program:=
  renameProgram borrow (OwnQ6Core5.half divide (OneBankCell5.ports base g))
def cell (divide : Bool) (g sw:Wire) : Program:=
  if divide then half true g++swapRegisters sw R YR
    else swapRegisters sw R YR++half false g
 def rawReplay (divide:Bool) : List MixedTranscriptLetter → Program
  | []=>[]
  | l::ls=>if divide then cell true l.1.1 l.1.2++rawReplay true ls
    else rawReplay false ls++cell false l.1.1 l.1.2
 def basePacket (divide:Bool) (j:Nat) : Program:=
  History5.decode base (5*j)++rawReplay divide (Replay5.letters j)++History5.encode base (5*j)
def packet (divide:Bool) (j:Nat) : Program:=renameProgram (shifted (Placement5.pi j)) (basePacket divide j)
def groups (divide:Bool) (j n:Nat) : Program:=PacketSequence.program divide (packet divide) j n
def firstSwap : Program:=swapRegisters (base 1028) R YR
def firstSwapM : Program:=UncompSwap.mswap (base 1028) R YR
def firstBody (divide:Bool) : Program:=
  if divide then firstSwap++rawReplay true Replay5.restLetters
    else rawReplay false Replay5.restLetters++firstSwapM
 def firstPacket (divide:Bool) : Program:=renameProgram (shifted (Placement5.pi 0))
  (History5.decode base 0++firstBody divide++History5.encode base 0)
def endPacket (divide:Bool) : Program:=renameProgram (shifted Placement5.pi0) (half divide (base 510))
def logicalReplay (divide:Bool) : Program:=
  if divide then firstPacket true++groups true 1 101++endPacket true
    else endPacket false++groups false 1 101++firstPacket false
 def replay (divide:Bool) : Program:=renameProgram (OB5.sig 511) (logicalReplay divide)
def center : Program:=renameProgram borrow OwnQ5Endpoint.centerT
def canonical : Program:=renameProgram borrow OwnQ5Endpoint.canonT
def fieldEntry : Program:=replay true++HalfFieldOB5.copyN++canonical
def fieldExit : Program:=center++HalfFieldOB5.copyN++replay false
def hosted (P:Program) : Program:= [.X (base 511)]++renameProgram HostOB5.hostSwap P++[.X (base 511)]
def phase (P:Program) : Program:=
  renameProgram (Equiv.swap (base 1542) (base 721))
    (renameProgram (Equiv.swap (base 1541) (base 719))
      (renameProgram (Equiv.swap (base 1540) (base 720)) (renameProgram Q5Global718.swap P)))
def firstPhase : Program:=phase Q5Global718.firstPhase
 def lastPhase : Program:=phase Q5Global718.lastPhase
 def kernelEntry : Program:=firstPhase++hosted fieldEntry++lastPhase
 def kernelExit : Program:=firstPhase++hosted fieldExit++lastPhase
 def square (L:ControlledPointLayout) : Program:=
  renameProgram (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1539))
    (renameProgram (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537))
      (renameProgram (Equiv.swap (L.core.poolWire 1284) (L.core.poolWire 1538)) (SquareOB5.program L)))


theorem fresh_index (k:Nat) (hk:k<512) : base k∉OneBankCell5.ids.map base := by
  intro h
  obtain ⟨i,hi,e⟩:=List.mem_map.mp h
  have eq:=base_injective e
  subst i
  simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  omega

theorem data_away (i:Nat) (hi:i=1540 ∨ i=2409) : base i∉R ∧ base i∉YR := by
  change base i∉(balancedSharedPorts base (base 2409)).r ∧ base i∉(balancedSharedPorts base (base 2409)).y
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  constructor
  · exact OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)
  · exact OwnPlusHost.not_block i 770 256 (by rcases hi with rfl|rfl <;> omega)

theorem original_half_frame (divide:Bool) (g:Wire) (fresh:g∉OneBankCell5.ids.map base)
    (origin:BasisState) (hc:OneBankCell5.Clean base origin) (X Y:Fp) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y))
      (OwnQ6Core5.half divide (OneBankCell5.ports base g))
      (PairFrame R YR origin (centerWord (if divide then (X+(if origin g then Y else -Y))/2
        else 2*X+(if origin g then -Y else Y))) (centerWord Y)) := by
  let L:=OneBankCell5.ports base g
  have hw:=OneBankCell5.ports_widths base g
  have hn:=OneBankCell5.ports_nodup_injective base g base_injective fresh
  have cl:=OneBankCell5.clean_work base g origin hc
  intro s m h
  rw [OwnQ6Core5.half_eq divide L hw hn origin cl X Y s m h]
  cases divide
  · exact balancedTranscriptDouble_frame L hw hn origin cl X Y s m h
  · exact balancedTranscriptHalf_frame L hw hn origin cl X Y s m h

theorem half_frame (divide:Bool) (g:Wire) (fresh:g∉OneBankCell5.ids.map base)
    (origin:BasisState) (hc:OneBankCell5.Clean base origin) (hz:origin (base 2409)=false) (X Y:Fp) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) (half divide g)
      (PairFrame R YR origin (centerWord (if divide then (X+(if origin g then Y else -Y))/2
        else 2*X+(if origin g then -Y else Y))) (centerWord Y)) := by
  intro s m h
  have old:=original_half_frame divide g fresh origin hc X Y s m h
  have ca:=data_away 1540 (Or.inl rfl)
  have cb:=data_away 2409 (Or.inr rfl)
  have zero:origin (base 1540)=false:=by
    apply OneBankCell5.clean_work base g origin hc
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]
  have a0:s.basis (base 1540)=false:=(h.2.2 _ ca.1 ca.2).trans zero
  have b0:s.basis (base 2409)=false:=(h.2.2 _ cb.1 cb.2).trans hz
  have a1:(run (OwnQ6Core5.half divide (OneBankCell5.ports base g)) m s).basis (base 1540)=false:=
    (old.2.2.2 _ ca.1 ca.2).trans zero
  have b1:(run (OwnQ6Core5.half divide (OneBankCell5.ports base g)) m s).basis (base 2409)=false:=
    (old.2.2.2 _ cb.1 cb.2).trans hz
  have eq:=FieldFrameOB5.rebind_swap_run _ _ _ s m a0 b0 a1 b1
  change run (half divide g) m s=run (OwnQ6Core5.half divide (OneBankCell5.ports base g)) m s at eq
  rw [eq]
  exact old

private theorem swap_frame (c:Wire) (hn:(c::R++YR).Nodup) (origin:BasisState) (A B:Nat) :
    Triple (PairFrame R YR origin A B) (swapRegisters c R YR)
      (PairFrame R YR origin (if origin c then B else A) (if origin c then A else B)) := by
  have width:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  intro s m h
  have v:=swapRegisters_correct c R YR (width.2.1.trans width.2.2.1.symm) hn s m
  have ca:c∉R ∧ c∉YR:=by
    have d:=(List.nodup_cons.mp hn).1
    exact ⟨fun hm=>d (List.mem_append_left _ hm),fun hm=>d (List.mem_append_right _ hm)⟩
  have same:=h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy=>(v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem source_swap_nd (g sw:Wire)
    (hl:BalancedTranscriptLayout (OneBankCell5.ports base (base 2409)) (base 2400) g sw (base 2410)) :
    (sw::R++YR).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_,(List.nodup_cons.mp hl.swapND).2⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · exact (hl.outside sw (by simp [OneBankCell5.ports])).1 h
  · exact (hl.outside sw (by simp [OneBankCell5.ports])).2 h

theorem cell_frame (divide:Bool) (g sw:Wire)
    (fresh:g∉OneBankCell5.ids.map base)
    (hl:BalancedTranscriptLayout (OneBankCell5.ports base (base 2409)) (base 2400) g sw (base 2410))
    (origin:BasisState) (hc:OneBankCell5.Clean base origin) (hz:origin (base 2409)=false) (X Y:Fp) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) (cell divide g sw)
      (PairFrame R YR origin (centerWord (OneBankCell5.payload divide (origin g) (origin sw) (X,Y)).1)
        (centerWord (OneBankCell5.payload divide (origin g) (origin sw) (X,Y)).2)) := by
  have hn:=source_swap_nd g sw hl
  cases divide
  · let A:=if origin sw then Y else X
    let B:=if origin sw then X else Y
    have sf:=swap_frame sw hn origin (centerWord X) (centerWord Y)
    have sf':Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) (swapRegisters sw R YR)
        (PairFrame R YR origin (centerWord A) (centerWord B)):=by
      cases he:origin sw <;> simpa only [A,B,he,Bool.false_eq_true,if_false,if_true] using sf
    have hh:=half_frame false g fresh origin hc hz A B
    have out:PairFrame R YR origin
        (centerWord (OneBankCell5.payload false (origin g) (origin sw) (X,Y)).1)
        (centerWord (OneBankCell5.payload false (origin g) (origin sw) (X,Y)).2)=
        PairFrame R YR origin (centerWord (2*A+(if origin g then -B else B))) (centerWord B):=by
      cases he:origin sw <;> simp only [OneBankCell5.payload,skywalkPayloadUncell,A,B,he,
        Bool.false_eq_true,if_false,if_true]
    change Triple _ _ (PairFrame R YR origin _ _)
    rw [out]
    simpa only [cell,Bool.false_eq_true,if_false] using sf'.seq hh
  · let T:=(X+(if origin g then Y else -Y))/2
    have hh:=half_frame true g fresh origin hc hz X Y
    have sf:=swap_frame sw hn origin (centerWord T) (centerWord Y)
    have out:PairFrame R YR origin
        (centerWord (OneBankCell5.payload true (origin g) (origin sw) (X,Y)).1)
        (centerWord (OneBankCell5.payload true (origin g) (origin sw) (X,Y)).2)=
        PairFrame R YR origin (if origin sw then centerWord Y else centerWord T)
          (if origin sw then centerWord T else centerWord Y):=by
      cases he:origin sw <;> simp only [OneBankCell5.payload,skywalkPayloadCell,T,he,
        Bool.false_eq_true,if_false,if_true]
    change Triple _ _ (PairFrame R YR origin _ _)
    rw [out]
    simpa only [cell,if_true] using hh.seq sf


theorem cell_mixed_frame (divide:Bool) (g sw:Wire) (ig is:Bool)
    (fresh:g∉OneBankCell5.ids.map base)
    (hl:BalancedTranscriptLayout (OneBankCell5.ports base (base 2409)) (base 2400) g sw (base 2410))
    (origin:BasisState) (hc:OneBankCell5.Clean base origin)
    (hb:origin (base 2400)=true) (hz:origin (base 2409)=false) (X Y:Fp) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) (cell divide g sw)
      (PairFrame R YR origin
        (centerWord (OneBankCell5.payload divide (mixedTranscriptBit origin (base 2400) g ig)
          (mixedTranscriptBit origin (base 2400) sw is) (X,Y)).1)
        (centerWord (OneBankCell5.payload divide (mixedTranscriptBit origin (base 2400) g ig)
          (mixedTranscriptBit origin (base 2400) sw is) (X,Y)).2)) := by
  simpa only [mixedTranscriptBit,hb,if_true] using cell_frame divide g sw fresh hl origin hc hz X Y

theorem half_counts (divide:Bool) (g:Wire) :
    toffoliCount (half divide g)=1020 ∧ measurementCount (half divide g)=1021 := by
  have h:=OwnQ6Core5.counts divide (OneBankCell5.ports base g) (OneBankCell5.ports_widths base g)
  simpa only [half,(renameProgram_counts borrow _).1,(renameProgram_counts borrow _).2,
    OwnQ6Core5.half,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    Nat.add_zero,Nat.zero_add] using h

theorem cell_counts (divide:Bool) (g sw:Wire) (hs:(sw::R++YR).Nodup) :
    toffoliCount (cell divide g sw)=1276 ∧ measurementCount (cell divide g sw)=1021 := by
  have w:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  have c:=swapRegisters_resources sw R YR (w.2.1.trans w.2.2.1.symm) hs
  have wr:R.length=256:=w.2.1
  cases divide <;> constructor <;> simp only [cell,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,(half_counts false g).1,(half_counts false g).2,
    (half_counts true g).1,(half_counts true g).2,c.1,c.2.1,wr]

theorem original_support (divide:Bool) (g:Wire) (W:Finset Wire)
    (hi:(base 2409::OneBankCell5.ids.map base).toFinset⊆W) (hg:g∈W) :
    wires (OwnQ6Core5.half divide (OneBankCell5.ports base g))⊆W := by
  have hn:(g::OneBankCell5.ids.map base).toFinset⊆W:=by
    intro q hq
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|h
    · exact hg
    · exact hi (List.mem_toFinset.mpr (List.mem_cons_of_mem _ h))
  have k:=(OwnQ6Core5.support divide (OneBankCell5.ports base g) (OneBankCell5.ports_widths base g)).trans
    (OneBankCell5.ports_wires_sub base g W hn)
  simp only [OwnQ6Core5.half,wires_append,wires,Instr.wires,Finset.union_empty,
    Finset.union_subset_iff,Finset.singleton_subset_iff,OneBankCell5.ports_sign]
  exact ⟨⟨hg,k⟩,hg⟩

theorem half_support (divide:Bool) (g:Wire) (W:Finset Wire)
    (hi:(base 2409::OneBankCell5.ids.map base).toFinset⊆W) (hg:g∈W) :
    wires (half divide g)⊆W := by
  rw [half,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hq
  have old:=original_support divide g W hi hg hx
  by_cases a:x=base 1540
  · subst x
    simpa only [borrow,Equiv.swap_apply_left] using hi (by simp)
  · by_cases b:x=base 2409
    · subst x
      have c:base 1540∈W:=hi (by simp [OneBankCell5.ids])
      simpa only [borrow,Equiv.swap_apply_right] using c
    · simpa only [borrow,Equiv.swap_apply_of_ne_of_ne a b] using old

theorem cell_support (divide:Bool) (g sw:Wire) (W:Finset Wire)
    (hi:(base 2409::OneBankCell5.ids.map base).toFinset⊆W) (hg:g∈W) (hs:sw∈W) :
    wires (cell divide g sw)⊆W := by
  have old:=OneBankCell5.body_support true base (base 2409) sw W hi hs
  simp only [OneBankCell5.body,if_true,wires_append,Finset.union_subset_iff] at old
  have h:=half_support divide g W hi hg
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff]
  · exact ⟨old.2,h⟩
  · exact ⟨h,old.2⟩

theorem half_physical (divide:Bool) (g:Wire) (fresh:g∉OneBankCell5.ids.map base) : GatePhysical (half divide g) := by
  have hw:=OneBankCell5.ports_widths base g
  have hn:=OneBankCell5.ports_nodup_injective base g base_injective fresh
  have k:=OwnQ6Core5.kernel_physical divide _ hw hn
  have x:GatePhysical [.X g]:=by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  apply gatePhysical_rename borrow borrow.injective
  simpa only [OwnQ6Core5.half,gatePhysical_append,OneBankCell5.ports_sign] using And.intro (And.intro x k) x

theorem cell_physical (divide:Bool) (g sw:Wire) (fresh:g∉OneBankCell5.ids.map base)
    (hs:(sw::R++YR).Nodup) : GatePhysical (cell divide g sw) := by
  have h:=half_physical divide g fresh
  have c:=swapRegisters_physical sw R YR hs
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨c,h⟩
  · exact ⟨h,c⟩

open Challenge Baselines

theorem half_slots (divide:Bool) (g:Wire) : gateSlots (half divide g)≤25002 := by
  have h:=OwnQ6Core5.kernel_gateSlots_le divide (OneBankCell5.ports base g) (OneBankCell5.ports_widths base g)
  simp only [half,rename_gateSlots,OwnQ6Core5.half,gateSlots_append,
    gateSlots_cons,gateSlots_nil,instructionSlots]
  cases divide <;> simp only [Bool.false_eq_true,if_false,if_true] at h <;> omega

theorem cell_slots (divide:Bool) (g sw:Wire) : gateSlots (cell divide g sw)≤26000 := by
  have h:=half_slots divide g
  have w: R.length=256:=by simp [R,balancedSharedPorts_r,wireBlock_length]
  have c:=swapRegisters_gateSlots sw R YR
  rw [w] at c
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega


def Fresh (ls:List MixedTranscriptLetter) : Prop:=∀l∈ls,l.1.1∉OneBankCell5.ids.map base

theorem fresh_letter (i:Nat) (hi:i<512) : (tapeLetter i).1.1∉OneBankCell5.ids.map base := by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i hi]
  exact fresh_index i hi

theorem fresh_letters (j:Nat) (hj:j<102) : Fresh (Replay5.letters j) := by
  intro l hl
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
  have h:=List.mem_range.mp hk
  exact fresh_letter (5*j+k) (by omega)

theorem fresh_rest : Fresh Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
  have h:=List.mem_range'_1.mp hk
  exact fresh_letter k (by omega)

theorem firstSwap_frame (origin:BasisState) (hb:origin (base 2400)=true)
    (hn:(base 1028::R++YR).Nodup) (X Y:Fp) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) firstSwap
      (PairFrame R YR origin
        (centerWord (if mixedTranscriptBit origin (base 2400) (base 1028)
          (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then Y else X))
        (centerWord (if mixedTranscriptBit origin (base 2400) (base 1028)
          (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then X else Y))) := by
  unfold firstSwap
  have w:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  intro s m h
  have v:=swapRegisters_correct (base 1028) R YR (w.2.1.trans w.2.2.1.symm) hn s m
  have out:base 1028∉R ∧ base 1028∉YR:=by
    have n:=(List.nodup_cons.mp hn).1
    exact ⟨fun q=>n (List.mem_append_left _ q),fun q=>n (List.mem_append_right _ q)⟩
  have src:=h.2.2 (base 1028) out.1 out.2
  refine ⟨v.1,?_,?_,fun q qr qy=>(v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,src,h.1,h.2.1]
    cases he:origin (base 1028) <;> simp [mixedTranscriptBit,hb,he]
  · rw [v.2.2.2,src,h.1,h.2.1]
    cases he:origin (base 1028) <;> simp [mixedTranscriptBit,hb,he]

theorem firstSwapM_frame (origin:BasisState) (hb:origin (base 2400)=true)
    (hn:(base 1028::R++YR).Nodup) (X Y:Fp)
    (hz:(if mixedTranscriptBit origin (base 2400) (base 1028)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then X else Y)=0) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) firstSwapM
      (PairFrame R YR origin
        (centerWord (if mixedTranscriptBit origin (base 2400) (base 1028)
          (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then Y else X))
        (centerWord (if mixedTranscriptBit origin (base 2400) (base 1028)
          (mixedTranscriptUnitTrace.getD 0 (false,false)).2 then X else Y))) := by
  have w:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  have zero:(if origin (base 1028) then centerWord X else centerWord Y)=0:=by
    simp only [mixedTranscriptBit,hb,if_true] at hz
    cases he:origin (base 1028)
    · simp only [he,Bool.false_eq_true,if_false] at hz ⊢
      rw [hz,UncompSwap.centerWord_zero]
    · simp only [he,if_true] at hz ⊢
      rw [hz,UncompSwap.centerWord_zero]
  have old:=UncompSwap.mswap_pair R YR (base 1028) (w.2.1.trans w.2.2.1.symm) hn origin
    (centerWord X) (centerWord Y) zero
  cases he:origin (base 1028) <;>
    simpa only [firstSwapM,mixedTranscriptBit,hb,he,Bool.false_eq_true,if_false,if_true] using old

end ECDSAAdd.Entrant.QSiteDirectControls
end QSiteDirectControls

section TicketInverseEndpoint
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteInverseDirect
open Arithmetic MappedCompressed Secp256k1 BalancedField QSiteDirectControls
attribute [local irreducible] run wires InverseTailC.borrowed List.toFinset

def raw : Program := InverseEndpointC.half (OneBankCell5.ports base (base 510))
def program : Program := renameProgram borrow raw

theorem raw_frame (origin : BasisState) (hc : OneBankCell5.Clean base origin) (Y : Fp) :
    Triple (PairFrame R YR origin (centerWord Y) (centerWord Y)) raw
      (PairFrame R YR origin (centerWord (2*Y+(if origin (base 510) then -Y else Y))) (centerWord Y)) := by
  let L:=OneBankCell5.ports base (base 510)
  have hn:=OneBankCell5.ports_nodup_injective base (base 510) base_injective (fresh_index 510 (by decide))
  have old:=original_half_frame false (base 510) (fresh_index 510 (by decide)) origin hc Y Y
  intro s m h
  have eq:=InverseTailC.borrowed_half_q6_eq L (OneBankCell5.ports_widths base (base 510)) hn
    origin (OneBankCell5.clean_work base (base 510) origin hc) Y s m h
  change run raw m s=run (OwnQ6Core5.half false L) m s at eq
  rw [eq]
  exact old s m h

theorem frame (origin : BasisState) (hc : OneBankCell5.Clean base origin)
    (hz : origin (base 2409)=false) (Y : Fp) :
    Triple (PairFrame R YR origin (centerWord Y) (centerWord Y)) program
      (PairFrame R YR origin (centerWord (2*Y+(if origin (base 510) then -Y else Y))) (centerWord Y)) := by
  intro s m h
  have old:=raw_frame origin hc Y s m h
  have ca:=QSiteDirectControls.data_away 1540 (Or.inl rfl)
  have cb:=QSiteDirectControls.data_away 2409 (Or.inr rfl)
  have zero:origin (base 1540)=false:=by
    apply OneBankCell5.clean_work base (base 510) origin hc
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]
  have a0:s.basis (base 1540)=false:=(h.2.2 _ ca.1 ca.2).trans zero
  have b0:s.basis (base 2409)=false:=(h.2.2 _ cb.1 cb.2).trans hz
  have a1:(run raw m s).basis (base 1540)=false:=(old.2.2.2 _ ca.1 ca.2).trans zero
  have b1:(run raw m s).basis (base 2409)=false:=(old.2.2.2 _ cb.1 cb.2).trans hz
  have eq:=FieldFrameOB5.rebind_swap_run _ _ _ s m a0 b0 a1 b1
  change run program m s=run raw m s at eq
  rw [eq]
  exact old

theorem raw_support (W : Finset Wire)
    (hi:(base 2409::OneBankCell5.ids.map base).toFinset⊆W) (hg:base 510∈W) :
    wires raw⊆W := by
  have hn:(base 510::OneBankCell5.ids.map base).toFinset⊆W:=by
    intro q hq
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|h
    · exact hg
    · exact hi (List.mem_toFinset.mpr (List.mem_cons_of_mem _ h))
  exact (InverseEndpointC.support _ (OneBankCell5.ports_widths base (base 510))).trans
    ((InverseEndpointC.sites_subset _).trans (OneBankCell5.ports_wires_sub base (base 510) W hn))

theorem support (W : Finset Wire)
    (hi:(base 2409::OneBankCell5.ids.map base).toFinset⊆W) (hg:base 510∈W) :
    wires program⊆W := by
  rw [program,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hq
  have old:=raw_support W hi hg hx
  by_cases a:x=base 1540
  · subst x
    simpa only [borrow,Equiv.swap_apply_left] using hi (by simp)
  · by_cases b:x=base 2409
    · subst x
      have c:base 1540∈W:=hi (by simp [OneBankCell5.ids])
      simpa only [borrow,Equiv.swap_apply_right] using c
    · simpa only [borrow,Equiv.swap_apply_of_ne_of_ne a b] using old

theorem counts : toffoliCount program=766 ∧ measurementCount program=765 := by
  simpa only [program,raw,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using
    InverseEndpointC.counts _ (OneBankCell5.ports_widths base (base 510))

theorem physical : GatePhysical program := by
  apply gatePhysical_rename borrow borrow.injective
  exact InverseEndpointC.physical _ (OneBankCell5.ports_widths base (base 510))
    (OneBankCell5.ports_nodup_injective base (base 510) base_injective (fresh_index 510 (by decide)))

theorem slots : Challenge.gateSlots program≤25002 := by
  simpa only [program,raw,Baselines.rename_gateSlots] using
    InverseEndpointC.gateSlots_le _ (OneBankCell5.ports_widths base (base 510))

theorem raw_free (q : Nat) (hq : q∈[765,766,767,2312,1026,1541,1539,2400,2410,511,2409]) :
    base q∉wires raw := by
  by_cases eq:q=1541
  · subst q
    have nd:=OneBankCell5.ports_nodup_injective base (base 510) base_injective (fresh_index 510 (by decide))
    have no:=InverseTailC.borrowed_retired _ (OneBankCell5.ports_widths base (base 510)) nd
    have e : InverseTailC.last (OneBankCell5.ports base (base 510))=base 1541 := rfl
    rw [e] at no
    simpa only [raw,InverseEndpointC.half,wires_append,wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,OneBankCell5.ports,not_or] using
      And.intro (And.intro (by decide : base 1541≠base 510) no) (by decide : base 1541≠base 510)
  · intro used
    have hs:=InverseEndpointC.support _ (OneBankCell5.ports_widths base (base 510)) used
    have eSites : InverseEndpointC.sites (OneBankCell5.ports base (base 510))=
        (base 510::base 768::base 1027::base 1797::
          (wireBlock base 770 256++wireBlock base 2056 256++
            (wireBlock base 512 253++[base 1540,base 1541]))).toFinset := rfl
    rw [eSites] at hs
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc] at hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    have outside (start len : Nat) (bound : q<start ∨ start+len≤q) :
        base q∉wireBlock base start len := by
      intro mem
      obtain ⟨i,hi,e⟩:=List.mem_map.mp mem
      simp only [List.mem_range'_1] at hi
      have same:=base_injective e
      omega
    rcases hs with e|e|e|e|hy|hr|hc|e|e
    · have same:=base_injective e;omega
    · have same:=base_injective e;omega
    · have same:=base_injective e;omega
    · have same:=base_injective e;omega
    · exact outside 770 256 (by omega) hy
    · exact outside 2056 256 (by omega) hr
    · exact outside 512 253 (by omega) hc
    · have same:=base_injective e;omega
    · have same:=base_injective e;omega

end ECDSAAdd.Entrant.QSiteInverseDirect
end TicketInverseEndpoint



section QSiteTerminalDirect
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteTerminalDirect
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation
open QSiteDirectControls
attribute [local irreducible] wires run TerminalGraph.decoder

def relabel : Equiv.Perm Wire := (Equiv.swap (base 2409) (base 510)).trans borrow
def oldProgram : Program := TerminalGraphEndpoint.half true base (base 2409)
def program : Program := renameProgram relabel oldProgram

def allowed (q : Wire) : Prop := q=base 510 ∨ q=base 2409 ∨ q=base 1027 ∨ q=base 768 ∨
  q=base 1797 ∨ (base 770≤q ∧ q<base 1026) ∨ (base 2056≤q ∧ q<base 2312) ∨
  (base 512≤q ∧ q<base 765)

theorem fixed (q : Wire) (a:q≠base 1540) (b:q≠base 2409) (c:q≠base 510) : relabel q=q := by
  simp only [relabel,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne b c,borrow,
    Equiv.swap_apply_of_ne_of_ne a b]

theorem signal : relabel (base 2409)=base 510 := by decide

theorem data_fixed (q : Wire) (hq:q∈R++YR) : relabel q=q := by
  have a:=data_away 1540 (Or.inl rfl)
  have b:=data_away 2409 (Or.inr rfl)
  have c:base 510∉R ∧ base 510∉YR := by
    rw [R,YR,balancedSharedPorts_r,balancedSharedPorts_y]
    exact ⟨OwnPlusHost.not_block 510 2056 256 (by omega),OwnPlusHost.not_block 510 770 256 (by omega)⟩
  apply fixed
  all_goals intro e;subst q;rcases List.mem_append.mp hq with h|h <;> tauto

theorem block_bounds (q start n : Nat) (h:q∈wireBlock base start n) :
    base start≤q ∧ q<base (start+n) := by
  obtain ⟨i,hi,he⟩:=List.mem_map.mp h
  have bound:=List.mem_range'_1.mp hi
  rw [←he]
  change start + 16 ≤ i + 16 ∧ i + 16 < (start + n) + 16
  exact ⟨Nat.add_le_add_right bound.1 16,Nat.add_lt_add_right bound.2 16⟩

theorem support : ∀q∈wires program,allowed q := by
  have prior:=TerminalGraphSupportOnly.actual_decoder_support.1
  have yr : (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))).y=wireBlock base 770 256 := rfl
  have rr : (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))).r=wireBlock base 2056 256 := rfl
  have cr : (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))).carry=
      wireBlock base 512 253++[base 1540,base 1797] := by
    simp [TerminalGraph.ofBalanced,Q6EndpointCell.ports,List.take_append,wireBlock_length]
  intro q used
  rw [program,renameProgram_support] at used
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp used
  have h:=List.mem_toFinset.mp (prior hw)
  simp only [TerminalGraph.DecoderLayout.wires,yr,rr,cr] at h
  change w∈[base 2409,base 1027,base 768]++wireBlock base 770 256++wireBlock base 2056 256++
    (wireBlock base 512 253++[base 1540,base 1797]) at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
  rcases h with rfl|rfl|rfl|h|h|h|rfl|rfl
  · simp only [allowed,signal];tauto
  · rw [fixed (base 1027) (by decide) (by decide) (by decide)];simp only [allowed];tauto
  · rw [fixed (base 768) (by decide) (by decide) (by decide)];simp only [allowed];tauto
  · have b:=block_bounds w 770 256 h
    obtain ⟨lo,hi⟩:=b
    have n1:w≠base 1540:=by intro e;rw [e] at hi;exact (by decide : ¬(base 1540<base 1026)) hi
    have n2:w≠base 2409:=by intro e;rw [e] at hi;exact (by decide : ¬(base 2409<base 1026)) hi
    have n3:w≠base 510:=by intro e;rw [e] at lo;exact (by decide : ¬(base 770≤base 510)) lo
    rw [fixed w n1 n2 n3]
    right;right;right;right;right;left
    exact ⟨lo,hi⟩
  · have b:=block_bounds w 2056 256 h
    obtain ⟨lo,hi⟩:=b
    have n1:w≠base 1540:=by intro e;rw [e] at lo;exact (by decide : ¬(base 2056≤base 1540)) lo
    have n2:w≠base 2409:=by intro e;rw [e] at hi;exact (by decide : ¬(base 2409<base 2312)) hi
    have n3:w≠base 510:=by intro e;rw [e] at lo;exact (by decide : ¬(base 2056≤base 510)) lo
    rw [fixed w n1 n2 n3]
    right;right;right;right;right;right;left
    exact ⟨lo,hi⟩
  · have b:=block_bounds w 512 253 h
    obtain ⟨lo,hi⟩:=b
    have n1:w≠base 1540:=by intro e;rw [e] at hi;exact (by decide : ¬(base 1540<base 765)) hi
    have n2:w≠base 2409:=by intro e;rw [e] at hi;exact (by decide : ¬(base 2409<base 765)) hi
    have n3:w≠base 510:=by intro e;rw [e] at lo;exact (by decide : ¬(base 512≤base 510)) lo
    rw [fixed w n1 n2 n3]
    right;right;right;right;right;right;right
    exact ⟨lo,hi⟩
  · have e:relabel (base 1540)=base 2409:=by decide
    rw [e];simp only [allowed];tauto
  · rw [fixed (base 1797) (by decide) (by decide) (by decide)];simp only [allowed];tauto

theorem physical : GatePhysical program :=
  gatePhysical_rename _ relabel.injective _ TerminalGraphPhysicalOnly.physical

theorem slots : Challenge.gateSlots program≤23900 := by
  rw [program,Baselines.rename_gateSlots]
  exact TerminalGraphPhysicalOnly.slots

theorem counts : toffoliCount program=512 ∧ measurementCount program=766 := by
  simpa only [program,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,oldProgram,if_true] using
    TerminalGraphEndpoint.half_counts true base (base 2409)

theorem reg_pull (r : List Wire) (hr:∀q∈r,relabel q=q) (s:State) :
    regValue r (pullState relabel s).basis=regValue r s.basis :=
  regValue_congr r _ _ (fun q hq => congrArg s.basis (hr q hq))

theorem away_data (r : List Wire) (hr:∀q∈r,relabel q=q) (q:Wire) (hq:q∉r) : relabel q∉r := by
  intro used
  have e:=relabel.injective (hr (relabel q) used)
  exact hq (e ▸ used)

theorem transport (r y:List Wire) (P:Program) (origin:BasisState) (A B C D:Nat)
    (rf:∀q∈r,relabel q=q) (yf:∀q∈y,relabel q=q)
    (spec:Triple (PairFrame r y (fun q=>origin (relabel q)) A B) P
      (PairFrame r y (fun q=>origin (relabel q)) C D)) :
    Triple (PairFrame r y origin A B) (renameProgram relabel P) (PairFrame r y origin C D) := by
  intro s m hin
  have pin : PairFrame r y (fun q=>origin (relabel q)) A B (pullState relabel s).basis := by
    refine ⟨(reg_pull r rf s).trans hin.1,(reg_pull y yf s).trans hin.2.1,?_⟩
    intro q qr qy
    exact hin.2.2 (relabel q) (away_data r rf q qr) (away_data y yf q qy)
  have old:=spec (pullState relabel s) m pin
  have eq:=run_rename relabel relabel.injective P m s
  simp only [←eq] at old
  refine ⟨old.1,?_,?_,?_⟩
  · exact (reg_pull r rf (run (renameProgram relabel P) m s)).symm.trans old.2.1
  · exact (reg_pull y yf (run (renameProgram relabel P) m s)).symm.trans old.2.2.1
  · intro q qr qy
    obtain ⟨k,rfl⟩:=relabel.surjective q
    have kr:k∉r:=by intro h;exact qr ((rf k h).symm ▸ h)
    have ky:k∉y:=by intro h;exact qy ((yf k h).symm ▸ h)
    exact old.2.2.2 k kr ky

theorem frame (origin : BasisState) (hc : Q6EndpointCell.Clean base origin)
    (hz : origin (base 2409)=false) (X Y : Fp)
    (hend : (X+(if origin (base 510) then Y else -Y))/2=Y) :
    Triple (PairFrame R YR origin (centerWord X) (centerWord Y)) program
      (PairFrame R YR origin (centerWord Y) (centerWord Y)) := by
  let ob:BasisState:=fun q=>origin (relabel q)
  have rfix : ∀q∈R,relabel q=q := fun q h=>data_fixed q (List.mem_append_left _ h)
  have yfix : ∀q∈YR,relabel q=q := fun q h=>data_fixed q (List.mem_append_right _ h)
  have cl : Q6EndpointCell.Clean base ob := by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    change origin (relabel (base i))=false
    by_cases e:i=1540
    · subst i
      simpa only [relabel,Equiv.trans_apply,borrow] using hz
    · have n1:base i≠base 1540:=fun h=>e (base_injective h)
      have nums:=hi
      simp only [Q6EndpointCell.workIds,List.mem_append,List.mem_map,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at nums
      have n2:base i≠base 2409:=by intro h;have:=base_injective h;omega
      have n3:base i≠base 510:=by intro h;have:=base_injective h;omega
      rw [fixed _ n1 n2 n3]
      exact hc _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  apply transport R YR oldProgram origin (centerWord X) (centerWord Y) (centerWord Y) (centerWord Y) rfix yfix
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have hn:=Q6EndpointCell.ports_nodup base (base 2409) cfg.1 (by
    intro h
    obtain ⟨i,hi,eq⟩:=List.mem_map.mp h
    have n:=Q6EndpointCell.ids_bound i hi
    have same:=base_injective eq
    omega)
  have th:=TerminalGraphEndpoint.half_frame true base (base 2409) hn ob cl X Y
    (fun _=>by simpa only [ob,signal] using hend)
  simp only [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] at th
  simpa only [if_true,oldProgram,show (X+(if ob (base 2409) then Y else -Y))/2=Y by simpa only [ob,signal] using hend] using th

end ECDSAAdd.Entrant.QSiteTerminalDirect
end QSiteTerminalDirect

section QSiteDirectReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

structure Context (origin:BasisState) extends OneBankReplay5.Context origin where
  enabled:origin (base 2400)=true

def rawReplay (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then
      QSiteDirectControls.cell true l.1.1 l.1.2++rawReplay true ls
    else rawReplay false ls++
      QSiteDirectControls.cell false l.1.1 l.1.2

def body (divide : Bool) (j : Nat) : Program := rawReplay divide (Replay5.letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++body divide j++History5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstBody (divide : Bool) : Program :=
  if divide then QSiteDirectControls.firstSwap++rawReplay true Replay5.restLetters
  else rawReplay false Replay5.restLetters++QSiteDirectControls.firstSwapM

def baseFirstPacket (divide : Bool) : Program :=
  History5.decode base 0++firstBody divide++History5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  if divide then QSiteTerminalDirect.program else QSiteInverseDirect.program

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def logicalReplay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplay divide)


def fieldSites : Finset Wire := (base 2409::OneBankCell5.ids.map base).toFinset

def readSites (start : Nat) : Finset Wire := fieldSites ∪ {base 2400,base 2410} ∪
  wires (History5.encode base start)

theorem raw_support (divide : Bool) (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (hi : fieldSites⊆W) (_hb : base 2400∈W) (_he : base 2410∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) : wires (rawReplay divide ls)⊆W := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := QSiteDirectControls.cell_support divide l.1.1 l.1.2 W hi
      (controls l (by simp)).1 (controls l (by simp)).2
    have rest := ih (fun k hk => controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.union_subset_iff] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆readSites (5*j) := by
  apply raw_support
  · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · intro l hl
    have c := Replay5.letters_controls j hj l hl
    exact ⟨Finset.mem_union_right _ c.1,Finset.mem_union_right _ c.2⟩

theorem readSites_sub (start : Nat) : readSites start⊆
    History5.groupReadSites base (base 2400) (base 2409) (base 2410) start ∪ {base 2312} := by
  intro q hq
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have hp := (OneBankCell5.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases OneBankCell5.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem body_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (body_support divide j hj).trans (readSites_sub (5*j))

theorem firstBody_support (divide : Bool) : wires (firstBody divide)⊆readSites 0 := by
  let W := readSites 0
  have hi : fieldSites⊆W := fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hb : base 2400∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have he : base 2410∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have hs : base 1028∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 0 (by decide)).2)
  have swap : wires QSiteDirectControls.firstSwap⊆W := by
    have h:=OneBankCell5.body_support true base (base 2409) (base 1028) W hi hs
    simp only [OneBankCell5.body,if_true,wires_append,Finset.union_subset_iff] at h
    exact h.2
  have swapM : wires QSiteDirectControls.firstSwapM⊆W := by
    simpa only [QSiteDirectControls.firstSwapM,QSiteDirectControls.firstSwap,UncompSwap.mswap_wires] using swap
  have rest : wires (rawReplay divide Replay5.restLetters)⊆W := by
    apply raw_support divide Replay5.restLetters W hi hb he
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    have controls := Replay5.history_controls 0 k (by omega)
    simp only [Nat.zero_add] at controls
    simpa only [tapeLetter,tape] using
      (show base k∈W ∧ base (1028+k)∈W from
        ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩)
  cases divide <;> simp only [firstBody,Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff]
  · exact ⟨rest,swapM⟩
  · exact ⟨swap,rest⟩

theorem firstBody_read_support (divide : Bool) :
    wires (firstBody divide)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  (firstBody_support divide).trans (readSites_sub 0)

theorem rawEnd_support (divide:Bool) : wires (rawEnd divide)⊆fieldSites∪{base 2400,base 510,base 2410} := by
  cases divide
  · exact QSiteInverseDirect.support _ Finset.subset_union_left (Finset.mem_union_right _ (by simp))
  · intro q hq
    have mem (i:Nat) (hi:i∈OneBankCell5.ids) : base i∈fieldSites :=
      List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
    have ranged (start n:Nat) (h:base start≤q ∧ q<base (start+n))
        (inside:∀i,start≤ i ∧ i<start+n → i∈OneBankCell5.ids) : q∈fieldSites := by
      obtain ⟨lo,hi⟩:=h
      have low:16≤q:=(Nat.le_add_left 16 start).trans lo
      have e:base (q-16)=q:=Nat.sub_add_cancel low
      rw [←e]
      apply mem
      apply inside
      have l : start+16≤(q-16)+16 := by
        simpa only [Nat.sub_add_cancel low] using lo
      have u : (q-16)+16<(start+n)+16 := by
        simpa only [Nat.sub_add_cancel low] using hi
      exact ⟨Nat.le_of_add_le_add_right l,Nat.lt_of_add_lt_add_right u⟩
    have h:=QSiteTerminalDirect.support q hq
    rcases h with rfl|rfl|rfl|rfl|rfl|h|h|h
    · exact Finset.mem_union_right _ (by simp)
    · exact Finset.mem_union_left _ (by simp [fieldSites])
    · exact Finset.mem_union_left _ (mem _ (by simp [OneBankCell5.ids]))
    · exact Finset.mem_union_left _ (mem _ (by simp [OneBankCell5.ids]))
    · exact Finset.mem_union_left _ (mem _ (by simp [OneBankCell5.ids]))
    · exact Finset.mem_union_left _ (ranged 770 256 h (by
        intro i hi;simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false];omega))
    · exact Finset.mem_union_left _ (ranged 2056 256 h (by
        intro i hi;obtain ⟨lo,hi⟩:=hi;simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false];omega))
    · exact Finset.mem_union_left _ (ranged 512 253 h (by
        intro i hi;simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false];omega))

theorem rawEnd_read_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2312,base 2400,base 510,base 2410} := by
  intro q hq
  rcases Finset.mem_union.mp (rawEnd_support divide hq) with h|h
  · have hp := (OneBankCell5.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases OneBankCell5.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ (by simp [h])
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Finset.mem_union_right _ (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (History5.allEncode base 102)) (wires (rawEnd divide)) := by
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member base 102 q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q member
  have read := rawEnd_read_support divide used
  rcases Finset.mem_union.mp read with read|read
  · exact History5.history_active_away base (base 2409) hn (hp _ (by simp)) (5*j) (by omega) r
      (List.mem_toFinset.mp read)
  · have bound := History5.historyId_bound (5*j) (by omega) r
    have own : History5.historyMap base (5*j) r∈skywalkPoolWires base := by
      exact List.mem_map.mpr ⟨History5.historyId (5*j) r,by simp only [List.mem_range'_1]; omega,rfl⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at read
    rcases read with eq|eq|eq|eq
    · have same := base_injective eq
      omega
    · exact hp _ (by simp) (eq ▸ own)
    · have same := base_injective eq
      have rr := r.isLt
      unfold History5.historyId at same
      split_ifs at same <;> omega

    · exact hp _ (by simp) (eq ▸ own)

theorem letter_layout (origin : BasisState) (ctx : Context origin)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (l : MixedTranscriptLetter) (hl : l∈ls) :
    BalancedTranscriptLayout (OneBankCell5.ports base (base 2409))
      (base 2400) l.1.1 l.1.2 (base 2410) :=
  OneBankCell5.ports_transcript base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) (hf l hl) ctx.ho)
    (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

theorem raw_frame (divide : Bool) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (fresh:QSiteDirectControls.Fresh ls)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawReplay divide ls)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).2)) := by
  have clean := OneBankCell5.clean_of_env base origin ctx.env ctx.parity
  induction ls generalizing X Y with
  | nil =>
    intro s m h
    cases divide <;> simpa only [rawReplay,directionalPayload,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,mixedTranscriptControls,List.map_nil,skywalkPayloadReplay,
      skywalkPayloadReplayInverse,run] using And.intro (Eq.refl s.phase) h
  | cons l ls ih =>
    have layout := letter_layout origin ctx (l::ls) hf l (by simp)
    have tailLayout := fun k hk => hf k (List.mem_cons_of_mem l hk)
    cases divide
    · let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) ls) (X,Y)
      have rest := ih tailLayout (fun l hl=>fresh l (List.mem_cons_of_mem _ hl)) X Y
      have head := QSiteDirectControls.cell_mixed_frame false l.1.1 l.1.2 l.2.1 l.2.2 (fresh l (by simp)) layout origin clean ctx.enabled ctx.hg0 Q.1 Q.2
      simpa only [rawReplay,Bool.false_eq_true,if_false,directionalPayload,Bool.not_false,if_true,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,OneBankCell5.payload,Q,Prod.mk.eta]
        using rest.seq head
    · let Q := skywalkPayloadCell (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1)
        (mixedTranscriptBit origin (base 2400) l.1.2 l.2.2) (X,Y)
      have head := QSiteDirectControls.cell_mixed_frame true l.1.1 l.1.2 l.2.1 l.2.2 (fresh l (by simp)) layout origin clean ctx.enabled ctx.hg0 X Y
      have rest := ih tailLayout (fun l hl=>fresh l (List.mem_cons_of_mem _ hl)) Q.1 Q.2
      simpa only [rawReplay,if_true,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,OneBankCell5.payload,Q,Prod.mk.eta]
        using head.seq rest

theorem rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

theorem first_layout (origin : BasisState) (ctx : Context origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have h := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at h
  exact h

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have raw := raw_frame divide (Replay5.letters j) (Replay5.letters_layouts ctx.hf j hj) (QSiteDirectControls.fresh_letters j hj) origin ctx X Y
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp j hj origin X Y _ _ _ (body_read_support divide j hj) raw s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.groupsPayload divide origin j n (X,Y)).1
        (Replay5.groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun V t => History5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk origin ctx V.1 V.2 t records h⟩)
    j n bound (X,Y) s m input
  exact result.2

theorem firstBody_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.firstPayload divide origin (X,Y)).1)
        (centerWord (Replay5.firstPayload divide origin (X,Y)).2)) := by
  let S := mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  have fullLayout:=OneBankCell5.ports_transcript base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) ctx.hn (first_layout origin ctx) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have nd:=QSiteDirectControls.source_swap_nd (base 0) (base 1028) fullLayout
  let swap:=QSiteDirectControls.firstSwap_frame origin ctx.enabled nd
  cases divide
  · let V := directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X,Y)
    have zero : (if S then V.1 else V.2)=0 := by
      have h := hz rfl
      have k : ∀ (b : Bool) (p : Fp×Fp), (if b then (p.2,p.1) else p).2=(if b then p.1 else p.2) := by
        intro b p; cases b <;> rfl
      simp only [Replay5.firstPayload,Bool.false_eq_true,if_false,k] at h
      exact h
    have swapM:=QSiteDirectControls.firstSwapM_frame origin ctx.enabled nd V.1 V.2 zero
    have rest := raw_frame false Replay5.restLetters (rest_layout ctx.hf) QSiteDirectControls.fresh_rest origin ctx X Y
    have out := rest.seq swapM
    cases hS : S <;> simpa only [firstBody,Replay5.firstPayload,Bool.false_eq_true,
      if_false,Bool.not_false,if_true,S,hS,V] using out
  · have out := (swap X Y).seq (raw_frame true Replay5.restLetters (rest_layout ctx.hf) QSiteDirectControls.fresh_rest
      origin ctx (if S then Y else X) (if S then X else Y))
    cases hS : S <;> simpa only [firstBody,Replay5.firstPayload,if_true,Bool.not_true,
      Bool.false_eq_true,if_false,S,hS] using out

theorem firstPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.firstPayload divide origin (X,Y)).1
        (Replay5.firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin X Y _ _ _ (firstBody_read_support divide)
    (firstBody_frame divide origin ctx X Y hz) s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) (baseFirstPacket divide)
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (_hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y)
    (heq : divide=false → X=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 510 (by decide)) ctx.ho
  rw [mixedTape_base_getD 510 (by decide)] at layout
  have newLayout := OneBankCell5.ports_transcript base (base 2400) (base 510) (base 1538)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  cases divide
  · have same:=heq rfl
    subst X
    have result:=QSiteInverseDirect.frame origin
      (OneBankCell5.clean_of_env base origin ctx.env ctx.parity) ctx.hg0 Y
    simpa only [rawEnd,Replay5.endPayload,Prod.fst,Prod.snd,mixedTranscriptBit,ctx.enabled,if_true,if_false,Bool.false_eq_true] using result
  · have hend : (X+(if origin (base 510) then Y else -Y))/2=Y := by
      simpa only [Replay5.endPayload,if_true,mixedTranscriptBit,ctx.enabled,Prod.fst] using _hend rfl
    have result:=QSiteTerminalDirect.frame origin
      (Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity) ctx.hg0 X Y hend
    simpa only [rawEnd,Replay5.endPayload,Prod.fst,Prod.snd,mixedTranscriptBit,ctx.enabled,if_true,hend] using result


theorem endPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y)
    (heq : divide=false → X=Y) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := History5.encoded_disjoint_step base (base 2409)
    (skywalkShared_integer_nodup base ctx.hn) origin X Y _ _ _ (rawEnd_disjoint divide ctx.hn ctx.hp)
    (rawEnd_frame divide origin ctx X Y hend heq) s m input
  have eq := Replay5.placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload]))
        (fun e => absurd e (by decide)) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false origin ctx Y Y (fun e => absurd e (by decide)) (fun _ => rfl) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  FieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  FieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame origin ctx x hx0 hx trace Y) s m input



















end ECDSAAdd.Entrant.QSiteDirectReplay
end QSiteDirectReplay


section QSiteCumulativePhases
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed ECDSAAdd.Entrant ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q8IntegerHost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk OffsetBorrowedCanonical History5
attribute [local irreducible] wires run Stack5.forward5 stackForwardT NativeFirstDirect.forward StackOB5.forward OB5.sig
def swap : Equiv.Perm Wire := Equiv.swap (base 1540) (base 721)

theorem pull_clean (s : State) (a : s.basis (base 1540)=false)
    (b : s.basis (base 721)=false) : pullState swap s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (swap q)=s.basis q
    by_cases h : q=base 1540
    · subst q; simp [swap,a,b]
    · by_cases h' : q=base 721
      · subst q; simp [swap,a,b]
      · rw [show swap q=q by exact Equiv.swap_apply_of_ne_of_ne h h']

theorem run_eq (P : Program) (s : State) (m : List Bool)
    (a : s.basis (base 1540)=false) (b : s.basis (base 721)=false)
    (c : (run P m s).basis (base 1540)=false)
    (d : (run P m s).basis (base 721)=false) :
    run (renameProgram swap P) m s=run P m s := by
  apply pullState_perm_injective swap
  rw [run_rename swap swap.injective,pull_clean s a b,pull_clean _ c d]


theorem integer721_free : base 721∉OB5.integerSites := by
  intro used
  obtain ⟨i,e,hi⟩ := (OB5.integerSites_mem _).mp used
  have same := base_injective e
  omega

theorem prefix721_free : base 721∉NativeFirstDirect.prefixSites base := by
  intro used
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with ((a|b)|c)|(a|b)
  · exact OwnPlusHost.not_block 721 0 257 (by omega) a
  · exact OwnPlusHost.not_block 721 770 258 (by omega) b
  · exact OwnPlusHost.not_block 721 1540 256 (by omega) c
  · exact (by decide : base 721≠base 1028) a
  · exact (by decide : base 721≠base 1797) b

theorem terminal1540 (x : Nat) (s : State)
    (h : W.CompressedCompactStage5 base x p 512 s.basis) :
    s.basis (base 1540)=false := by
  obtain ⟨raw,stage,eq⟩ := h
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have carry : regValue (wireBlock base 1540 257) raw.basis=0 := fields.2.2.2.2.2.1
  have clean : raw.basis (base 1540)=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have away : base 1540∉wires (History5.encodePrefix base 512) := by
    rw [History5.encodePrefix_512]
    intro used
    have support := History5.allEncode_history_support base 102 (by decide) used
    simp only [List.mem_toFinset,List.mem_append] at support
    rcases support with a|b
    · exact OwnPlusHost.not_block 1540 0 512 (by omega) a
    · exact OwnPlusHost.not_block 1540 1028 512 (by omega) b
  rw [eq,run_preserves_outside _ [] raw _ away]
  exact clean
theorem forward_terminal1540 (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (m2 : List Bool)
    (firstW : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    (run stackForwardT m2 s1).basis (base 1540)=false := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  obtain ⟨t, ht⟩ : ∃t : State,run (Stack5.forward5 base 1 511) m2 s1=t := ⟨_,rfl⟩
  have terminal : W.CompressedCompactStage5 base x p 512 t.basis := by
    have raw := (Stack5.forward_spec base base_pool_nodup StackOB5.historyAbove x p 1 511
      hp0 hx0 hpo hp gap hx cop (by omega) s1 m2 (W.compactStage5_first base x p s1 firstW)).2
    rw [ht] at raw
    exact raw
  have eq : run stackForwardT m2 s1 = pullState (OB5.sig 511) t := by
    rw [←ht]
    exact (stackForwardT_run hn StackOB5.historyAbove x hx0 hx s1 m2 firstW).trans
      (StackOB5.forward_run x hx0 hx s1 m2 firstW)
  have fixed : OB5.sig 511 (base 1540)=base 1540 := by decide +kernel
  rw [eq]
  change t.basis (OB5.sig 511 (base 1540))=false
  rw [fixed]
  exact terminal1540 x _ terminal

theorem history1540_free (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    History5.historyId start q ≠1540 := by
  have h:=History5.historyId_region start hs q
  omega

theorem sig1540 (i : Nat) (hi : i≤511) : OB5.sig i (base 1540)=base 1540 := by
  rw [OB5.sig_base i 1540 hi]
  split_ifs <;> first | omega | rfl
def firstPhase : Program := NativeFirstDirect.forward base ++ (stackForwardT ++ skywalkArithmeticClear base)
attribute [local irreducible] firstPhase

theorem firstPhase721_free : base 721∉wires firstPhase := by
  have native : base 721∉wires (NativeFirstDirect.forward base) := fun h =>
    prefix721_free (List.mem_toFinset.mp ((NativeFirstDirect.prefix_support base).1 h))
  have stack : base 721∉wires stackForwardT := fun h =>
    integer721_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).1 _ (stackForwardT_subset h))
  have clear : base 721∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using ⟨native,stack,clear⟩

theorem input_clean (x y i : Nat) (s : State) (hin : SkywalkArithmeticInput base x y s.basis)
    (hi : i=721 ∨ i=1540) : s.basis (base i)=false := by
  apply hin.2.2 (base i)
  · rcases hi with rfl|rfl <;> decide +kernel
  · exact OwnPlusHost.not_block i 770 256 (by rcases hi with rfl|rfl <;> omega)
  · exact OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem firstPhase1540_clean (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    (run firstPhase m s).basis (base 1540)=false := by
  rw [firstPhase,run_append,run_append]
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s
    (m.take (measurementCount (NativeFirstDirect.forward base))) hin
  have firstW := (W.compactSkywalkStage_one base _ _).mpr first
  have cleaned := forward_terminal1540 hn x hx0 hx _
    ((m.drop (measurementCount (NativeFirstDirect.forward base))).take (measurementCount stackForwardT)) firstW
  have away : base 1540∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  exact (run_preserves_outside _ _ _ _ away).trans cleaned

theorem firstPhase_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap firstPhase) m s=run firstPhase m s := by
  apply run_eq
  · exact input_clean x Y.val 1540 s hin (Or.inr rfl)
  · exact input_clean x Y.val 721 s hin (Or.inl rfl)
  · exact firstPhase1540_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ firstPhase721_free).trans
      (input_clean x Y.val 721 s hin (Or.inl rfl))
def lastPhase : Program := skywalkArithmeticClear base ++ (stackReverseT ++ NativeFirstKnown.inverse base)
attribute [local irreducible] lastPhase

theorem lastPhase721_free : base 721∉wires lastPhase := by
  have native : base 721∉wires (NativeFirstKnown.inverse base) := fun h =>
    prefix721_free (List.mem_toFinset.mp (NativeFirstKnown.inverse_support base h))
  have stack : base 721∉wires stackReverseT := fun h =>
    integer721_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).2 _ (stackReverseT_subset h))
  have clear : base 721∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [lastPhase,wires_append,Finset.mem_union,not_or] using ⟨clear,stack,native⟩

/-- Full arbitrary-record transfer needs only the old complete program's clean
output and the new field implementation's literal omission of1540. It imposes
no new promise on the original caller input. -/
theorem three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1540∉wires F)
    (out1540 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 1540)=false)
    (out721 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 721)=false) :
    run (renameProgram swap lastPhase) mr
      (run F mf (run (renameProgram swap firstPhase) mp s)) =
    run lastPhase mr (run F mf (run firstPhase mp s)) := by
  rw [firstPhase_state_eq hn x Y hx0 hx s mp hin]
  have mid1540 : (run F mf (run firstPhase mp s)).basis (base 1540)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1540_clean hn x Y hx0 hx s mp hin)
  have mid721 : (run F mf (run firstPhase mp s)).basis (base 721)=false :=
    (run_preserves_outside lastPhase mr _ _ lastPhase721_free).symm.trans out721
  exact run_eq lastPhase _ mr mid1540 mid721 out1540 out721

theorem wireFn2_721 (L : ControlledPointLayout) : wireFn2 L (base 721)=L.core.poolWire 721 := by rfl

theorem rename_1540_free (P : Program) (free : base 721∉wires P) :
    base 1540∉wires (renameProgram swap P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,member,eq⟩ := Finset.mem_image.mp used
  have back := congrArg swap eq
  simp only [swap,Equiv.swap_apply_self,Equiv.swap_apply_left] at back
  exact free (back ▸ member)

theorem wireFn2_1540 (L : ControlledPointLayout) : wireFn2 L (base 1540)=L.core.poolWire 1284 := by rfl

theorem final721_charged (L : ControlledPointLayout) : L.core.poolWire 721∈WrapperOB5.sites L := by
  have member : L.core.poolWire 721∈wireBlock L.core.poolWire 718 311 :=
    List.mem_map.mpr ⟨721,by simp only [List.mem_range'_1]; omega,rfl⟩
  simp only [WrapperOB5.sites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto


def q5First : Program := renameProgram Q5Global718.swap firstPhase
def q5Last : Program := renameProgram Q5Global718.swap lastPhase
attribute [local irreducible] q5First q5Last

private theorem q5first_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run q5First m s=run firstPhase m s := by
  have same : firstPhase=Q5Global718.firstPhase := by unfold firstPhase Q5Global718.firstPhase; rfl
  unfold q5First
  rw [same]
  exact Q5Global718.firstPhase_state_eq hn x Y hx0 hx s m hin

theorem q5First721_free : base 721∉wires q5First := by
  unfold q5First
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) firstPhase721_free

theorem q5Last721_free : base 721∉wires q5Last := by
  unfold q5Last
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) lastPhase721_free

theorem q5First_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap q5First) m s=run q5First m s := by
  apply run_eq
  · exact input_clean x Y.val 1540 s hin (Or.inr rfl)
  · exact input_clean x Y.val 721 s hin (Or.inl rfl)
  · rw [q5first_eq hn x Y hx0 hx s m hin]
    exact firstPhase1540_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ q5First721_free).trans
      (input_clean x Y.val 721 s hin (Or.inl rfl))

theorem q5_three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1540∉wires F)
    (out1540 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 1540)=false)
    (out721 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 721)=false) :
    run (renameProgram swap q5Last) mr
      (run F mf (run (renameProgram swap q5First) mp s)) =
    run q5Last mr (run F mf (run q5First mp s)) := by
  rw [q5First_state_eq hn x Y hx0 hx s mp hin]
  have mid1540 : (run F mf (run q5First mp s)).basis (base 1540)=false := by
    rw [run_preserves_outside _ _ _ _ field_free,q5first_eq hn x Y hx0 hx s mp hin]
    exact firstPhase1540_clean hn x Y hx0 hx s mp hin
  have mid721 : (run F mf (run q5First mp s)).basis (base 721)=false :=
    (run_preserves_outside q5Last mr _ _ q5Last721_free).symm.trans out721
  exact run_eq q5Last _ mr mid1540 mid721 out1540 out721

end ECDSAAdd.Entrant.Q8IntegerHost
end QSiteCumulativePhases


section QSiteDirectResources
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectControls
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 BalancedField

theorem swap_counts_all (c:Wire) : toffoliCount (swapRegisters c R YR)=256 ∧ measurementCount (swapRegisters c R YR)=0 := by
  have hR:R.length=256:=by simp [R,balancedSharedPorts_r,wireBlock_length]
  have hY:YR.length=256:=by simp [YR,balancedSharedPorts_y,wireBlock_length]
  have a:=copyRegister_counts none YR R (hY.trans hR.symm)
  have b:=copyRegister_counts (some c) R YR (hR.trans hY.symm)
  simp only [swapRegisters,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true,hR]
  decide

theorem cell_counts_all (divide:Bool) (g sw:Wire) :
    toffoliCount (cell divide g sw)=1276 ∧ measurementCount (cell divide g sw)=1021 := by
  have c:=swap_counts_all sw
  cases divide <;> constructor <;> simp only [cell,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,c.1,c.2,(half_counts false g).1,(half_counts false g).2,
    (half_counts true g).1,(half_counts true g).2]

theorem first_nd (hn:(skywalkSharedWires base).Nodup) : (base 1028::R++YR).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2409) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · exact OwnPlusHost.not_block 1028 2056 256 (by omega) h
  · exact OwnPlusHost.not_block 1028 770 256 (by omega) h


end ECDSAAdd.Entrant.QSiteDirectControls
namespace ECDSAAdd.Entrant.QSiteDirectReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

section Counts

private theorem swap_nodup (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    (base 2410::(OneBankCell5.ports base (base 2409)).r++(OneBankCell5.ports base (base 2409)).y).Nodup := by
  have own : base 2410∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2410) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2410)) nd (base 2410)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2410) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2410∈(balancedSharedPorts base (base 2410)).r := by
      simpa only [OneBankCell5.ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2410∈(balancedSharedPorts base (base 2410)).y := by
      simpa only [OneBankCell5.ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

theorem raw_counts (divide : Bool) (ls : List MixedTranscriptLetter)
    (_hs : (base 2410::(OneBankCell5.ports base (base 2409)).r++(OneBankCell5.ports base (base 2409)).y).Nodup) :
    toffoliCount (rawReplay divide ls)=ls.length*1276 ∧
      measurementCount (rawReplay divide ls)=ls.length*1021 := by
  induction ls with
  | nil => simp [rawReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have c := QSiteDirectControls.cell_counts_all divide l.1.1 l.1.2
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,List.length_cons] at c ih ⊢
    all_goals constructor <;> omega

theorem packet_counts (divide : Bool) (j : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (packet divide j)=6400 ∧ measurementCount (packet divide j)=5111 := by
  have raw := raw_counts divide (Replay5.letters j) (swap_nodup hn ho)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at raw
  have e := History5.encode_counts base (5*j)
  have d := History5.decode_counts base (5*j)
  have renamed := renameProgram_counts (shifted (Placement5.pi j)) (basePacket divide j)
  change toffoliCount (renameProgram _ (basePacket divide j))=_ ∧
    measurementCount (renameProgram _ (basePacket divide j))=_
  rw [renamed.1,renamed.2]
  simp only [basePacket,toffoliCount_append,measurementCount_append,body] at *
  constructor <;> omega


theorem groups_counts (divide : Bool) (j n : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (groups divide j n)=n*6400 ∧ measurementCount (groups divide j n)=n*5111 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_counts divide j hn ho
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append] at head rest ⊢
    all_goals constructor <;> omega


theorem firstPacket_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (firstPacket divide)=(if divide then 5380 else 5124) ∧
      measurementCount (firstPacket divide)=(if divide then 4090 else 4346) := by
  have raw := raw_counts divide Replay5.restLetters (swap_nodup hn ho)
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at raw
  have sw:=QSiteDirectControls.swap_counts_all (base 1028)
  have width:=BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))
  have swM:=UncompSwap.mswap_counts (base 1028) QSiteDirectControls.R QSiteDirectControls.YR
    (width.2.1.trans width.2.2.1.symm)
  have wr:QSiteDirectControls.R.length=256:=width.2.1
  simp only [wr] at swM
  have e := History5.encode_counts base 0
  have d := History5.decode_counts base 0
  have renamed := renameProgram_counts (shifted (Placement5.pi 0)) (baseFirstPacket divide)
  change toffoliCount (renameProgram _ (baseFirstPacket divide))=_ ∧
    measurementCount (renameProgram _ (baseFirstPacket divide))=_
  rw [renamed.1,renamed.2]
  cases divide <;> simp only [baseFirstPacket,firstBody,QSiteDirectControls.firstSwap,QSiteDirectControls.firstSwapM,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at raw ⊢
  all_goals constructor <;> omega


theorem endPacket_counts (divide:Bool) : toffoliCount (endPacket divide)=(if divide then 512 else 766) ∧
    measurementCount (endPacket divide)=(if divide then 766 else 765) := by
  cases divide
  · simpa only [endPacket,rawEnd,if_false,Bool.false_eq_true,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using
      QSiteInverseDirect.counts
  · simpa only [endPacket,rawEnd,if_true,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using QSiteTerminalDirect.counts

theorem logicalReplay_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (logicalReplay divide)=(if divide then 652292 else 652290) ∧
      measurementCount (logicalReplay divide)=(if divide then 521067 else 521322) := by
  have first := firstPacket_counts divide hn ho
  have rest := groups_counts divide 1 101 hn ho
  have last := endPacket_counts divide
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at first rest last ⊢
  all_goals constructor <;> omega


theorem replay_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (replay divide)=(if divide then 652292 else 652290) ∧
      measurementCount (replay divide)=(if divide then 521067 else 521322) := by
  simpa only [replay,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using
    logicalReplay_counts divide hn ho


end Counts

section Physical

theorem raw_physical (divide : Bool) (ls : List MixedTranscriptLetter)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (fresh:QSiteDirectControls.Fresh ls) :
    GatePhysical (rawReplay divide ls) := by
  induction ls with
  | nil => simp [rawReplay,GatePhysical]
  | cons l ls ih =>
    have layout:=OneBankCell5.ports_transcript base (base 2400) l.1.1 l.1.2
      (base 2409) (base 2410) hn
      (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        (hf l (by simp)) ho) (ho _ (by simp)) (ho _ (by simp))
    have cell:=QSiteDirectControls.cell_physical divide l.1.1 l.1.2 (fresh l (by simp))
      (QSiteDirectControls.source_swap_nd l.1.1 l.1.2 layout)
    have rest := ih (fun k hk => hf k (List.mem_cons_of_mem l hk)) (fun k hk=>fresh k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append] at cell rest ⊢
    · exact ⟨rest,cell⟩
    · exact ⟨cell,rest⟩

theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters j)) :
    GatePhysical (packet divide j) := by
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have raw : GatePhysical (body divide j) := raw_physical divide _ hn ho hf (QSiteDirectControls.fresh_letters j hj)
  have p : GatePhysical (basePacket divide j) := by
    simpa only [basePacket,gatePhysical_append] using And.intro (And.intro d raw) e
  exact gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ p

theorem groups_physical (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters k)) :
    GatePhysical (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,GatePhysical]
  | succ n ih =>
    have head := packet_physical divide j (by omega) hn ho (hf j (by omega))
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem firstPacket_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (firstPacket divide) := by
  have ns:=QSiteDirectControls.first_nd hn
  have swap:GatePhysical QSiteDirectControls.firstSwap:=swapRegisters_physical _ _ _ ns
  have swapM:GatePhysical QSiteDirectControls.firstSwapM:=UncompSwap.mswap_physical _ _ _ ns
  have rest := raw_physical divide Replay5.restLetters hn ho (rest_layout hf) QSiteDirectControls.fresh_rest
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have p : GatePhysical (baseFirstPacket divide) := by
    cases divide <;> simp only [baseFirstPacket,firstBody,QSiteDirectControls.firstSwap,QSiteDirectControls.firstSwapM,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨⟨d,⟨rest,swapM⟩⟩,e⟩
    · exact ⟨⟨d,⟨swap,rest⟩⟩,e⟩
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ p

theorem endPacket_physical (divide:Bool) : GatePhysical (endPacket divide) := by
  apply gatePhysical_rename _ (shifted Placement5.pi0).injective
  cases divide
  · exact QSiteInverseDirect.physical
  · exact QSiteTerminalDirect.physical

theorem replay_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (replay divide) := by
  have first := firstPacket_physical divide hn ho hf
  have rest := groups_physical divide 1 101 (by decide) hn ho (Replay5.letters_layouts hf)
  have last := endPacket_physical divide
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by decide))
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,rest⟩,first⟩
  · exact ⟨⟨first,rest⟩,last⟩

end Physical

section Slots
open Challenge Baselines
attribute [local irreducible] gateSlots

theorem raw_gateSlots_le (divide : Bool) (ls : List MixedTranscriptLetter) :
    gateSlots (rawReplay divide ls)≤ls.length*26000 := by
  induction ls with
  | nil => simp [rawReplay]
  | cons l ls ih =>
    have c := QSiteDirectControls.cell_slots divide l.1.1 l.1.2
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append,List.length_cons] at c ih ⊢ <;> omega

theorem packet_gateSlots_le (divide : Bool) (j : Nat) : gateSlots (packet divide j)≤130356 := by
  have raw : gateSlots (body divide j)≤5*26000 := by
    simpa only [Replay5.letters,List.length_map,List.length_range] using
      raw_gateSlots_le divide (Replay5.letters j)
  have codec := History5.codec_slots base (5*j)
  simp only [packet,rename_gateSlots,basePacket,gateSlots_append]
  omega

theorem groups_gateSlots_le (divide : Bool) (j n : Nat) : gateSlots (groups divide j n)≤n*130356 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program]
  | succ n ih =>
    have head := packet_gateSlots_le divide j
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem firstPacket_gateSlots_le (divide:Bool) : gateSlots (firstPacket divide)≤105388 := by
  have w:QSiteDirectControls.R.length=256:=by simp [QSiteDirectControls.R,balancedSharedPorts_r,wireBlock_length]
  have sw:=swapRegisters_gateSlots (base 1028) QSiteDirectControls.R QSiteDirectControls.YR
  rw [w] at sw
  have sm:=UncompSwap.mswap_slots (base 1028) QSiteDirectControls.R QSiteDirectControls.YR (by rfl)
  rw [w] at sm
  have raw:=raw_gateSlots_le divide Replay5.restLetters
  have len:Replay5.restLetters.length=4:=by simp [Replay5.restLetters]
  rw [len] at raw
  have codec:=History5.codec_slots base 0
  cases divide <;> simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    QSiteDirectControls.firstSwap,QSiteDirectControls.firstSwapM,Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem endPacket_gateSlots_le (divide:Bool) : gateSlots (endPacket divide)≤26000 := by
  cases divide
  · have h:=QSiteInverseDirect.slots
    simpa only [endPacket,rawEnd,if_false,Bool.false_eq_true,rename_gateSlots] using h.trans (by decide)
  · simpa only [endPacket,rawEnd,if_true,rename_gateSlots] using QSiteTerminalDirect.slots.trans (by decide)

theorem replay_gateSlots_le (divide : Bool) : gateSlots (replay divide)≤13941000 := by
  have first := firstPacket_gateSlots_le divide
  have rest := groups_gateSlots_le divide 1 101
  have last := endPacket_gateSlots_le divide
  cases divide <;> simp only [replay,rename_gateSlots,logicalReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append]
    at first rest last ⊢ <;> omega

end Slots
end ECDSAAdd.Entrant.QSiteDirectReplay
end QSiteDirectResources


section QSiteFinalIntegerBorrow
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q8FusionPhase
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk CompressedAllocation Q8IntegerHost
def q7First : Program:=renameProgram Q7IntegerHost.swap Q7FusionPhase.q6First
def q7Last : Program:=renameProgram Q7IntegerHost.swap Q7FusionPhase.q6Last
attribute [local irreducible] run wires q7First q7Last

theorem q7First721_free : base 721∉wires q7First := by
  have a:base 721∉wires Q6IntegerHost.q5First := by
    simpa only [Q6IntegerHost.q5First,Q8IntegerHost.q5First,Q6IntegerHost.firstPhase,Q8IntegerHost.firstPhase]
      using Q8IntegerHost.q5First721_free
  have b:base 721∉wires Q7FusionPhase.q6First:=
    OwnPlusHost.rename_avoid Q6IntegerHost.swap _ _ (by decide) a
  simpa only [q7First] using OwnPlusHost.rename_avoid Q7IntegerHost.swap _ _ (by decide) b

theorem q7Last721_free : base 721∉wires q7Last := by
  have a:base 721∉wires Q6IntegerHost.q5Last := by
    simpa only [Q6IntegerHost.q5Last,Q8IntegerHost.q5Last,Q6IntegerHost.lastPhase,Q8IntegerHost.lastPhase]
      using Q8IntegerHost.q5Last721_free
  have b:base 721∉wires Q7FusionPhase.q6Last:=
    OwnPlusHost.rename_avoid Q6IntegerHost.swap _ _ (by decide) a
  simpa only [q7Last] using OwnPlusHost.rename_avoid Q7IntegerHost.swap _ _ (by decide) b

theorem outside_num (i:Nat) (hi:i=721 ∨ i=1540) : base i∉wireBlock base 2056 256:=
  OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem q7First_pool : wires q7First⊆(skywalkPoolWires base).toFinset := by
  unfold q7First
  rw [renameProgram_support]
  intro q hq
  obtain ⟨old,used,rfl⟩:=Finset.mem_image.mp hq
  have member:=Q7FusionPhase.q6First_pool used
  by_cases a:old=base 1542
  · subst old
    apply List.mem_toFinset.mpr
    simpa only [Q7IntegerHost.swap,Equiv.swap_apply_left] using arith_mem base 0 1798 720 (by omega) (by omega)
  · by_cases b:old=base 720
    · subst old
      apply List.mem_toFinset.mpr
      simpa only [Q7IntegerHost.swap,Equiv.swap_apply_right] using arith_mem base 0 1798 1542 (by omega) (by omega)
    · simpa only [Q7IntegerHost.swap,Equiv.swap_apply_of_ne_of_ne a b] using member

theorem firstPhase1540_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    (run q7First m b).basis (base 1540)=false := by
  have agree := Q5FusionPhase.pool_agreement q7First q7First_pool a b m same (base 1540)
    (arith_mem base 0 1798 1540 (by omega) (by omega))
  have canonical:run q7First m a=run Q8IntegerHost.firstPhase m a:=by
    have h:run q7First m a=run Q7IntegerHost.firstPhase m a:=by
      unfold q7First
      rw [Q7FusionPhase.firstPhase_eq_paired hn x Y hx0 hx a a m input (fun _ _=>rfl)]
      unfold Q7FusionPhase.q6First
      rw [Q6IntegerHost.q5First_state_eq hn x Y hx0 hx a m input]
      change run Q7IntegerHost.q5First m a=run Q7IntegerHost.firstPhase m a
      exact Q7IntegerHost.q5first_eq hn x Y hx0 hx a m input
    simpa only [Q7IntegerHost.firstPhase,Q8IntegerHost.firstPhase] using h
  exact agree.trans (canonical ▸ Q8IntegerHost.firstPhase1540_clean hn x Y hx0 hx a m input)

theorem firstPhase_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    run (renameProgram swap q7First) m b=run q7First m b := by
  have clean1540 : b.basis (base 1540)=false :=
    (same _ (outside_num 1540 (Or.inr rfl))).trans (input_clean x Y.val 1540 a input (Or.inr rfl))
  have clean721 : b.basis (base 721)=false :=
    (same _ (outside_num 721 (Or.inl rfl))).trans (input_clean x Y.val 721 a input (Or.inl rfl))
  exact run_eq q7First b m clean1540 clean721
    (firstPhase1540_paired hn x Y hx0 hx a b m input same)
    ((run_preserves_outside _ _ _ _ q7First721_free).trans clean721)

theorem three_states_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (mp mf mr : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1540∉wires F)
    (out1540 : (run q7Last mr (run F mf (run q7First mp b))).basis (base 1540)=false)
    (out721 : (run q7Last mr (run F mf (run q7First mp b))).basis (base 721)=false) :
    run (renameProgram swap q7Last) mr (run F mf (run (renameProgram swap q7First) mp b))=
      run q7Last mr (run F mf (run q7First mp b)) := by
  rw [firstPhase_eq_paired hn x Y hx0 hx a b mp input same]
  have mid1540 : (run F mf (run q7First mp b)).basis (base 1540)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1540_paired hn x Y hx0 hx a b mp input same)
  have mid721 : (run F mf (run q7First mp b)).basis (base 721)=false :=
    (run_preserves_outside q7Last mr _ _ q7Last721_free).symm.trans out721
  exact run_eq q7Last _ mr mid1540 mid721 out1540 out721

def kernel (F : Program) := q7First++(F++q7Last)
def relocated (F : Program) := renameProgram swap q7First++(F++renameProgram swap q7Last)
attribute [local irreducible] kernel relocated

theorem old_shape (F : Program) : kernel F=Q7FusionPhase.relocated F := by
 simp only [kernel,q7First,q7Last,Q7FusionPhase.relocated]

theorem state_eq_of_frame (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1540∉wires F)
    (frame : ∀q,q∉wireBlock base 2056 256 → (run (kernel F) m b).basis q=a.basis q) :
    run (relocated F) m b=run (kernel F) m b := by
  have clean (i : Nat) (hi : i=721∨i=1540) : (run (kernel F) m b).basis (base i)=false :=
    (frame _ (outside_num i hi)).trans (input_clean x Y.val i a input hi)
  have h:=three_states_eq_paired hn x Y hx0 hx a b
    (m.take (measurementCount q7First))
    ((m.drop (measurementCount q7First)).take (measurementCount F))
    ((m.drop (measurementCount q7First)).drop (measurementCount F)) F input same field_free
    (by simpa only [kernel,run_append] using clean 1540 (Or.inr rfl))
    (by simpa only [kernel,run_append] using clean 721 (Or.inl rfl))
  simpa only [kernel,relocated,run_append,(renameProgram_counts swap q7First).2] using h

theorem relocated_1540_free (F : Program) (field_free : base 1540∉wires F) :
    base 1540∉wires (relocated F) := by
  rw [relocated,wires_append,wires_append]
  simpa only [Finset.mem_union,not_or] using
    ⟨rename_1540_free q7First q7First721_free,field_free,rename_1540_free q7Last q7Last721_free⟩

theorem relocated_counts (F : Program) :
    toffoliCount (relocated F)=toffoliCount (kernel F) ∧
    measurementCount (relocated F)=measurementCount (kernel F) := by
  have a:=renameProgram_counts swap q7First
  have b:=renameProgram_counts swap q7Last
  simp only [kernel,relocated,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  trivial

end ECDSAAdd.Entrant.Q8FusionPhase
end QSiteFinalIntegerBorrow

section QSiteDirectFields
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFields
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires
abbrev Context:=QSiteDirectReplay.Context

def fieldE:Program:=QSiteDirectReplay.replay true++(HalfFieldOB5.copyN++QSiteDirectControls.canonical)
def fieldX:Program:=QSiteDirectControls.center++(HalfFieldOB5.copyN++QSiteDirectReplay.replay false)
def hosted (P:Program):Program:=[.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)])
def rawE:Program:=NativeFirstDirect.forward base++stackForwardT++skywalkArithmeticClear base++
  hosted fieldE++skywalkArithmeticClear base++stackReverseT++NativeFirstKnown.inverse base
 def rawX:Program:=NativeFirstDirect.forward base++stackForwardT++skywalkArithmeticClear base++
  hosted fieldX++skywalkArithmeticClear base++stackReverseT++NativeFirstKnown.inverse base

theorem encoder_free (q:Nat) (hq:q=1540 ∨ q=2409 ∨ q=2410 ∨ q=2400):base q∉wires (History5.allEncode base 102):=by
  intro h
  have mem:=History5.allEncode_history_support base 102 (by decide) h
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with a|b
  · exact OwnPlusHost.not_block q 0 512 (by rcases hq with rfl|rfl|rfl|rfl <;> omega) a
  · exact OwnPlusHost.not_block q 1028 512 (by rcases hq with rfl|rfl|rfl|rfl <;> omega) b

theorem field_at (origin:BasisState) (X Y:Fp) (s:State) (q:Nat) (hq:q=1540 ∨ q=2409 ∨ q=2410 ∨ q=2400)
    (hin:FieldFrameOB5.EncodedFieldFrame origin X Y s):s.basis (base q)=origin (base q):=by
  obtain ⟨raw,_,pair,eq⟩:=hin
  have da:base q∉(balancedSharedPorts base (base 2409)).r ∧ base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_r,balancedSharedPorts_y]
    constructor
    · exact OwnPlusHost.not_block q 2056 256 (by rcases hq with rfl|rfl|rfl|rfl <;> omega)
    · exact OwnPlusHost.not_block q 770 256 (by rcases hq with rfl|rfl|rfl|rfl <;> omega)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl|rfl|rfl <;> decide
  have h:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [eq,run_preserves_outside _ _ _ _ (encoder_free q hq)]
    exact pair.2.2 _ da.1 da.2
  simpa only [pullState,fix] using h

theorem canonical_at (origin:BasisState) (X Y:Fp) (s:State) (q:Nat) (hq:q=1540 ∨ q=2409 ∨ q=2410 ∨ q=2400)
    (hin:FieldFrameOB5.EncodedCanonicalFrame origin X Y s):s.basis (base q)=origin (base q):=by
  obtain ⟨raw,_,pair,eq⟩:=hin
  have az:base q∉(skywalkSharedField base).z:=by
    rw [skywalkShared_field_z]
    exact OwnPlusHost.not_block q 2056 257 (by rcases hq with rfl|rfl|rfl|rfl <;> omega)
  have aa:base q∉(skywalkSharedField base).a:=OwnPlusHost.not_block q 770 257
    (by rcases hq with rfl|rfl|rfl|rfl <;> omega)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl|rfl|rfl <;> decide
  have h:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [eq,run_preserves_outside _ _ _ _ (encoder_free q hq)]
    exact pair.2.2 _ az aa
  simpa only [pullState,fix] using h

theorem center_frame (origin:BasisState) (ctx:Context origin)
    (ha:regValue (skywalkSharedField base).a origin=0) (Y:Fp) (s:State) (m:List Bool)
    (hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s):
    (run QSiteDirectControls.center m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 (run QSiteDirectControls.center m s):=by
  have old:=OwnQ5Endpoint.center_frame ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal ctx.parity ha Y s m hin
  have zero:origin (base 1540)=false:=by
    apply OneBankCell5.clean_work base (base 2409) origin (OneBankCell5.clean_of_env base origin ctx.env ctx.parity)
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]
  have a0:s.basis (base 1540)=false:=(canonical_at origin Y 0 s 1540 (Or.inl rfl) hin).trans zero
  have b0:s.basis (base 2409)=false:=(canonical_at origin Y 0 s 2409 (Or.inr (Or.inl rfl)) hin).trans ctx.hg0
  have a1:(run OwnQ5Endpoint.centerT m s).basis (base 1540)=false:=
    (field_at origin _ _ _ 1540 (Or.inl rfl) old.2).trans zero
  have b1:(run OwnQ5Endpoint.centerT m s).basis (base 2409)=false:=
    (field_at origin _ _ _ 2409 (Or.inr (Or.inl rfl)) old.2).trans ctx.hg0
  have eq:=FieldFrameOB5.rebind_swap_run _ _ _ s m a0 b0 a1 b1
  change run QSiteDirectControls.center m s=run OwnQ5Endpoint.centerT m s at eq
  rw [eq]
  exact old

theorem canonical_frame (origin:BasisState) (ctx:Context origin)
    (ha:regValue (skywalkSharedField base).a origin=0) (Y:Fp) (s:State) (m:List Bool)
    (hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s):
    (run QSiteDirectControls.canonical m s).phase=s.phase ∧
      FieldFrameOB5.EncodedCanonicalFrame origin (2*Y) 0 (run QSiteDirectControls.canonical m s):=by
  have old:=OwnQ5Endpoint.canon_frame ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal ctx.parity ha Y s m hin
  have zero:origin (base 1540)=false:=by
    apply OneBankCell5.clean_work base (base 2409) origin (OneBankCell5.clean_of_env base origin ctx.env ctx.parity)
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]
  have a0:s.basis (base 1540)=false:=(field_at origin Y 0 s 1540 (Or.inl rfl) hin).trans zero
  have b0:s.basis (base 2409)=false:=(field_at origin Y 0 s 2409 (Or.inr (Or.inl rfl)) hin).trans ctx.hg0
  have a1:(run OwnQ5Endpoint.canonT m s).basis (base 1540)=false:=
    (canonical_at origin _ _ _ 1540 (Or.inl rfl) old.2).trans zero
  have b1:(run OwnQ5Endpoint.canonT m s).basis (base 2409)=false:=
    (canonical_at origin _ _ _ 2409 (Or.inr (Or.inl rfl)) old.2).trans ctx.hg0
  have eq:=FieldFrameOB5.rebind_swap_run _ _ _ s m a0 b0 a1 b1
  change run QSiteDirectControls.canonical m s=run OwnQ5Endpoint.canonT m s at eq
  rw [eq]
  exact old

theorem three_states (a b c:Program) (P:State → State → Prop)
    (h:∀(s s1 s2 s3:State)(m1 m2 m3:List Bool),run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → P s s3)
    (s:State)(m:List Bool):P s (run (a++(b++c)) m s):=by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ rfl rfl rfl

theorem entry_frame (R C:Program) (origin:BasisState) (ctx:Context origin)
    (x:Nat) (rp:∀(Y:Fp)(s:State)(m:List Bool),FieldFrameOB5.EncodedFieldFrame origin Y 0 s → 
      (run R m s).phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin (Y/(x:Fp)) (Y/(x:Fp)) (run R m s))
    (cp:∀(Y:Fp)(s:State)(m:List Bool),FieldFrameOB5.EncodedFieldFrame origin Y 0 s → 
      (run C m s).phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (2*Y) 0 (run C m s))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s):
    (run (R++(HalfFieldOB5.copyN++C)) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedCanonicalFrame origin (2*(Y/(x:Fp))) 0 (run (R++(HalfFieldOB5.copyN++C)) m s):=by
  have all:=three_states R HalfFieldOB5.copyN C
    (fun a b=>FieldFrameOB5.EncodedFieldFrame origin Y 0 a → b.phase=a.phase ∧
      FieldFrameOB5.EncodedCanonicalFrame origin (2*(Y/(x:Fp))) 0 b) (by
      intro a b c d m1 m2 m3 ab bc cd h
      have h1:=rp Y a m1 h
      rw [ab] at h1
      have h2:=HalfFieldOB5.copy_clear ctx.hn origin (Y/(x:Fp)) b m2 h1.2
      rw [bc] at h2
      have h3:=cp (Y/(x:Fp)) c m3 h2.2
      rw [cd] at h3
      exact ⟨h3.1.trans (h2.1.trans h1.1),h3.2⟩) s m
  exact all hin

theorem exit_frame (C R:Program) (origin:BasisState) (ctx:Context origin) (x:Nat)
    (cp:∀(Y:Fp)(s:State)(m:List Bool),FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s → 
      (run C m s).phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 (run C m s))
    (rp:∀(Y:Fp)(s:State)(m:List Bool),FieldFrameOB5.EncodedFieldFrame origin Y Y s → 
      (run R m s).phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin (Y*(x:Fp)) 0 (run R m s))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s):
    (run (C++(HalfFieldOB5.copyN++R)) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin ((Y/2)*(x:Fp)) 0 (run (C++(HalfFieldOB5.copyN++R)) m s):=by
  have all:=three_states C HalfFieldOB5.copyN R
    (fun a b=>FieldFrameOB5.EncodedCanonicalFrame origin Y 0 a → b.phase=a.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin ((Y/2)*(x:Fp)) 0 b) (by
      intro a b c d m1 m2 m3 ab bc cd h
      have h1:=cp Y a m1 h
      rw [ab] at h1
      have h2:=HalfFieldOB5.copy_fill ctx.hn origin (Y/2) b m2 h1.2
      rw [bc] at h2
      have h3:=rp (Y/2) c m3 h2.2
      rw [cd] at h3
      exact ⟨h3.1.trans (h2.1.trans h1.1),h3.2⟩) s m
  exact all hin


theorem pair_unique (r a:List Wire) (origin:BasisState) (X Y:Nat) (s t:State)
    (hp:s.phase=t.phase) (hs:PairFrame r a origin X Y s.basis) (ht:PairFrame r a origin X Y t.basis):s=t:=by
  apply State.extensionality s t hp
  funext q
  by_cases hr:q∈r
  · exact (regValue_eq_iff r _ _).mp (hs.1.trans ht.1.symm) q hr
  · by_cases ha:q∈a
    · exact (regValue_eq_iff a _ _).mp (hs.2.1.trans ht.2.1.symm) q ha
    · exact (hs.2.2 q hr ha).trans (ht.2.2 q hr ha).symm

theorem field_unique (origin:BasisState) (X Y:Fp) (s t:State) (hp:s.phase=t.phase)
    (hs:FieldFrameOB5.EncodedFieldFrame origin X Y s) (ht:FieldFrameOB5.EncodedFieldFrame origin X Y t):s=t:=by
  obtain ⟨rs,rph,rf,re⟩:=hs
  obtain ⟨rt,tph,tf,te⟩:=ht
  have raw:=pair_unique _ _ _ _ _ rs rt (rph.trans (hp.trans tph.symm)) rf tf
  have h:pullState (OB5.sig 511) s=pullState (OB5.sig 511) t:=by rw [re,te,raw]
  have h2:=congrArg (pullState (OB5.sig 511)) h
  rwa [OB5.pull_invol 511 (by decide),OB5.pull_invol 511 (by decide)] at h2

theorem canonical_unique (origin:BasisState) (X Y:Fp) (s t:State) (hp:s.phase=t.phase)
    (hs:FieldFrameOB5.EncodedCanonicalFrame origin X Y s) (ht:FieldFrameOB5.EncodedCanonicalFrame origin X Y t):s=t:=by
  obtain ⟨rs,rph,rf,re⟩:=hs
  obtain ⟨rt,tph,tf,te⟩:=ht
  have raw:=pair_unique _ _ _ _ _ rs rt (rph.trans (hp.trans tph.symm)) rf tf
  have h:pullState (OB5.sig 511) s=pullState (OB5.sig 511) t:=by rw [re,te,raw]
  have h2:=congrArg (pullState (OB5.sig 511)) h
  rwa [OB5.pull_invol 511 (by decide),OB5.pull_invol 511 (by decide)] at h2

theorem fieldE_spec (origin:BasisState) (ctx:Context origin) (ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s):
    (run fieldE m s).phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (2*(Y/(x:Fp))) 0 (run fieldE m s):=by
  apply entry_frame _ _ origin ctx x _ (canonical_frame origin ctx ha) Y s m hin
  intro Z t r h
  have q:=QSiteDirectReplay.forward_frame origin ctx x hx0 hx trace Z t r h
  simpa only [ctx.enabled,if_true] using q

theorem oldE_spec (origin:BasisState) (ctx:Context origin) (ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s):
    (run EntryFuse.field5 m s).phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (2*(Y/(x:Fp))) 0 (run EntryFuse.field5 m s):=by
  apply entry_frame _ _ origin ctx x _
    (OwnQ5Endpoint.canon_frame ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal ctx.parity ha) Y s m hin
  intro Z t r h
  have q:=OneBankReplay5.forward_frame origin ctx.toContext x hx0 hx trace Z t r h
  simpa only [ctx.enabled,if_true] using q

theorem fieldE_eq (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s):
    run fieldE m s=run EntryFuse.field5 m s:=by
  have n:=fieldE_spec origin ctx ha x hx0 hx trace Y s m hin
  have o:=oldE_spec origin ctx ha x hx0 hx trace Y s m hin
  exact canonical_unique origin _ _ _ _ (n.1.trans o.1.symm) n.2 o.2

theorem fieldX_spec (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s):
    (run fieldX m s).phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin ((Y/2)*(x:Fp)) 0 (run fieldX m s):=by
  apply exit_frame _ _ origin ctx x (center_frame origin ctx ha) _ Y s m hin
  intro Z t r h
  have q:=QSiteDirectReplay.inverse_frame origin ctx x hx0 hx trace Z t r h
  simpa only [ctx.enabled,if_true] using q

theorem oldX_spec (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s):
    (run ExitFuse.exitSegment5 m s).phase=s.phase ∧ FieldFrameOB5.EncodedFieldFrame origin ((Y/2)*(x:Fp)) 0 (run ExitFuse.exitSegment5 m s):=by
  apply exit_frame _ _ origin ctx x
    (OwnQ5Endpoint.center_frame ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal ctx.parity ha) _ Y s m hin
  intro Z t r h
  have q:=OneBankReplay5.inverse_frame origin ctx.toContext x hx0 hx trace Z t r h
  simpa only [ctx.enabled,if_true] using q

theorem fieldX_eq (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s):
    run fieldX m s=run ExitFuse.exitSegment5 m s:=by
  have n:=fieldX_spec origin ctx ha x hx0 hx trace Y s m hin
  have o:=oldX_spec origin ctx ha x hx0 hx trace Y s m hin
  exact field_unique origin _ _ _ _ (n.1.trans o.1.symm) n.2 o.2

end ECDSAAdd.Entrant.QSiteDirectFields
end QSiteDirectFields


section QSitePlacedSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectSupport
open Arithmetic MappedCompressed QSiteDirectReplay
attribute [local irreducible] wires

private def preFrame (i : Nat) : Prop :=
  (i<1542 ∧ i≠769 ∧ i≠511 ∧ i≠1539) ∨ i=1797 ∨ (2056 ≤ i ∧ i ≤ 2312) ∨ i=2400 ∨ i=2409 ∨ i=2410

private theorem sigma_mem (i : Nat) (hi : preFrame i) (safe : ¬Placement5.omitted i) :
    OB5.sig 511 (base i)∈OB5Support.segSites := by
  rw [OB5.sig_base 511 i (by decide)]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  unfold preFrame Placement5.omitted at *
  split_ifs <;> omega

private theorem perm_frame (e : Equiv.Perm Nat)
    (fix : ∀i,¬Placement5.zeroRegion i → e i=i) (i : Nat) (hi : preFrame i) : preFrame (e i) := by
  have bounded (i : Nat) (hi : i<1542) : e i<1542 := by
    by_contra hn
    have outside : ¬Placement5.zeroRegion (e i) := by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega
    have same := e.injective (fix (e i) outside)
    omega
  have no769 (i : Nat) (hi : i≠769) : e i≠769 := by
    intro eq
    have same := e.injective (eq.trans (fix 769 (by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega)).symm)
    exact hi same
  rcases hi with h|h|h|h|h|h
  · have noC (c : Nat) (hc : ¬Placement5.zeroRegion c) (k : Nat) (hk : k≠c) : e k≠c := by
      intro eq
      exact hk (e.injective (eq.trans (fix c hc).symm))
    exact Or.inl ⟨bounded i h.1,no769 i h.2.1,
      noC 511 (by unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega) i h.2.2.1,
      noC 1539 (by unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega) i h.2.2.2⟩
  all_goals
    have outside : ¬Placement5.zeroRegion i := by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega
    rw [fix i outside]
    unfold preFrame
    omega

private theorem pi_mem (j i : Nat) (hj : j<102) (hi : preFrame i)
    (hole : ¬Placement5.holeRegion i) :
    OB5.sig 511 (base (Placement5.pi j i))∈OB5Support.segSites :=
  sigma_mem _ (perm_frame (Placement5.pi j) (fun q hq => Placement5.pi_outside j q hj hq) i hi)
    (Placement5.nonhole_pi_safe j i hj hole)

private theorem pi0_mem (i : Nat) (hi : preFrame i) (hole : ¬Placement5.holeRegion i) :
    OB5.sig 511 (base (Placement5.pi0 i))∈OB5Support.segSites :=
  sigma_mem _ (perm_frame Placement5.pi0 Placement5.pi0_outside i hi)
    (Placement5.nonhole_pi0_safe i hole)

private theorem field_index (i : Nat) (hi : i∈OneBankCell5.ids) :
    preFrame i ∧ ¬Placement5.holeRegion i := by
  simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  unfold preFrame Placement5.holeRegion
  omega

private theorem history_pi_mem (j : Nat) (hj : j<102) (r : Fin 10) :
    OB5.sig 511 (base (Placement5.pi j (History5.historyId (5*j) r)))∈OB5Support.segSites := by
  have bounds := History5.historyId_region (5*j) (by omega) r
  have low : preFrame (History5.historyId (5*j) r) := by
    have hr := r.isLt
    unfold preFrame History5.historyId
    split <;> omega
  by_cases hole : Placement5.holeRegion (History5.historyId (5*j) r)
  · have h : History5.historyId (5*j) r=Placement5.H (2*j) ∨
        History5.historyId (5*j) r=Placement5.H (2*j+1) := by
      have hr := r.isLt
      have he : Placement5.H (2*j)=1030+5*j := by unfold Placement5.H; omega
      have ho : Placement5.H (2*j+1)=1032+5*j := by unfold Placement5.H; omega
      rw [he,ho]
      unfold History5.historyId at hole ⊢
      split_ifs at hole ⊢ <;> unfold Placement5.holeRegion at hole <;> omega
    rcases h with h|h
    · rw [h,Placement5.pi_current_even j hj]
      apply sigma_mem
      · have b := Placement5.H_bound (2*j) (by omega)
        unfold preFrame
        omega
      · have b := Placement5.H_bound (2*j) (by omega)
        unfold Placement5.omitted
        omega
    · rw [h,Placement5.pi_current_odd j hj]
      apply sigma_mem
      · have b := Placement5.H_bound (2*j+1) (by omega)
        unfold preFrame
        omega
      · have b := Placement5.H_bound (2*j+1) (by omega)
        unfold Placement5.omitted
        omega
  · exact pi_mem j _ hj low hole

private theorem read_placed (j : Nat) (hj : j<102) (q : Wire) (hq : q∈readSites (5*j)) :
    OB5.sig 511 (shifted (Placement5.pi j) q)∈OB5Support.segSites := by
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl|h
    · rw [shifted_base]
      exact pi_mem j 2409 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      rw [shifted_base]
      exact pi_mem j i hj (field_index i hi).1 (field_index i hi).2
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · rw [shifted_base]
      exact pi_mem j 2400 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · rw [shifted_base]
      exact pi_mem j 2410 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
  · obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q h
    rw [History5.historyMap,shifted_base]
    exact history_pi_mem j hj r

private theorem stage_placed_support (j : Nat) (hj : j<102) (P : Program)
    (hP : wires P⊆readSites (5*j)) :
    wires (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi j)) P))⊆OB5Support.segSites := by
  rw [renameProgram_support (OB5.sig 511) (renameProgram (shifted (Placement5.pi j)) P)]
  intro q hq
  obtain ⟨middle,hmid,eqSig⟩ := Finset.mem_image.mp hq
  rw [renameProgram_support (shifted (Placement5.pi j)) P] at hmid
  obtain ⟨old,hold,eqPi⟩ := Finset.mem_image.mp hmid
  rw [←eqSig,←eqPi]
  exact read_placed j hj old (hP hold)

private theorem codec_read (start : Nat) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : wires P⊆readSites start := by
  intro q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base start P hp q hq
  exact Finset.mem_union_right _ (History5.history_site_mem base start r)

theorem packet_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (renameProgram (OB5.sig 511) (packet divide j))⊆OB5Support.segSites := by
  apply stage_placed_support j hj
  simp only [basePacket,wires_append,Finset.union_subset_iff]
  exact ⟨⟨codec_read _ _ (Or.inr rfl),body_support divide j hj⟩,codec_read _ _ (Or.inl rfl)⟩

theorem firstPacket_support (divide : Bool) :
    wires (renameProgram (OB5.sig 511) (firstPacket divide))⊆OB5Support.segSites := by
  apply stage_placed_support 0 (by decide)
  simp only [baseFirstPacket,wires_append,Finset.union_subset_iff]
  exact ⟨⟨codec_read _ _ (Or.inr rfl),firstBody_support divide⟩,codec_read _ _ (Or.inl rfl)⟩

theorem endPacket_support (divide : Bool) :
    wires (renameProgram (OB5.sig 511) (endPacket divide))⊆OB5Support.segSites := by
  rw [renameProgram_support (OB5.sig 511) (endPacket divide)]
  intro q hq
  obtain ⟨middle,hmid,eqSig⟩ := Finset.mem_image.mp hq
  rw [endPacket,renameProgram_support (shifted Placement5.pi0) (rawEnd divide)] at hmid
  obtain ⟨old,hold,eqPi⟩ := Finset.mem_image.mp hmid
  rw [←eqSig,←eqPi]
  rcases Finset.mem_union.mp (rawEnd_support divide hold) with h|h
  · rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl|h
    · rw [shifted_base]
      exact pi0_mem 2409 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      rw [shifted_base]
      exact pi0_mem i (field_index i hi).1 (field_index i hi).2
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl
    · rw [shifted_base]
      exact pi0_mem 2400 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · rw [shifted_base]
      exact pi0_mem 510 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)

    · rw [shifted_base]
      exact pi0_mem 2410 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)

theorem groups_support (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    wires (renameProgram (OB5.sig 511) (groups divide j n))⊆OB5Support.segSites := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,renameProgram,wires]
  | succ n ih =>
    have head := packet_support divide j (by omega)
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      FieldRename.rename_append,wires_append,Finset.union_subset_iff] at rest ⊢
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem replay_support (divide : Bool) : wires (replay divide)⊆OB5Support.segSites := by
  have first := firstPacket_support divide
  have middle := groups_support divide 1 101 (by decide)
  have last := endPacket_support divide
  cases divide <;> simp only [replay,logicalReplay,Bool.false_eq_true,if_false,if_true,
    FieldRename.rename_append,wires_append,Finset.union_subset_iff] at first middle last ⊢
  · exact ⟨⟨last,middle⟩,first⟩
  · exact ⟨⟨first,middle⟩,last⟩

end ECDSAAdd.Entrant.QSiteDirectSupport
end QSitePlacedSupport

section QSiteDirectBoundary
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFields
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

theorem converter_support (P:Program) (old:wires P⊆OB5Support.segSites):
    wires (renameProgram QSiteDirectControls.borrow P)⊆OB5Support.segSites:=by
  have mem(i:Nat)(hi:i∈OB5Support.segIndices):base i∈OB5Support.segSites:=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have a:base 1540∈OB5Support.segSites:=mem 1540 (by simp [OB5Support.segIndices])
  have b:base 2409∈OB5Support.segSites:=mem 2409 (by simp [OB5Support.segIndices])
  rw [renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hq
  by_cases xa:x=base 1540
  · subst x; simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_left] using b
  · by_cases xb:x=base 2409
    · subst x; simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_right] using a
    · simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_of_ne_of_ne xa xb] using old hx

theorem fieldE_support:wires fieldE⊆OB5Support.segSites:=by
  simp only [fieldE,wires_append,Finset.union_subset_iff]
  exact ⟨QSiteDirectSupport.replay_support true,HalfFieldOB5Support.copy_support,
    converter_support _ OwnQ5Endpoint.support.2⟩

theorem fieldX_support:wires fieldX⊆OB5Support.segSites:=by
  simp only [fieldX,wires_append,Finset.union_subset_iff]
  exact ⟨converter_support _ OwnQ5Endpoint.support.1,HalfFieldOB5Support.copy_support,
    QSiteDirectSupport.replay_support false⟩

theorem fieldE_free:base 511∉wires fieldE ∧ base 1542∉wires fieldE:=
  ⟨fun h=>OB5Support.seg_host_free.1 (fieldE_support h),fun h=>OB5Support.seg_host_free.2 (fieldE_support h)⟩

theorem fieldX_free:base 511∉wires fieldX ∧ base 1542∉wires fieldX:=
  ⟨fun h=>OB5Support.seg_host_free.1 (fieldX_support h),fun h=>OB5Support.seg_host_free.2 (fieldX_support h)⟩

theorem hosted_E_eq (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedFieldFrame origin Y 0 s)
    (h511:s.basis (base 511)=true)(h1542:s.basis (base 1542)=false):
    run (hosted fieldE) m s=run EntryFuse.hostField5 m s:=by
  have old:=oldE_spec origin ctx ha x hx0 hx trace Y s m hin
  have oldFree:base 511∉wires EntryFuse.field5 ∧ base 1542∉wires EntryFuse.field5:=
    ⟨fun h=>(KernelOB5.seg_free true).1 (EntryFuse.field5_sub.wires_sub h),
      fun h=>(KernelOB5.seg_free true).2 (EntryFuse.field5_sub.wires_sub h)⟩
  have iG:s.basis (base 2409)=false:=(field_at origin Y 0 s 2409 (Or.inr (Or.inl rfl)) hin).trans ctx.hg0
  have iS:s.basis (base 2410)=false:=(field_at origin Y 0 s 2410 (Or.inr (Or.inr (Or.inl rfl))) hin).trans ctx.hs0
  have oG:(run EntryFuse.field5 m s).basis (base 2409)=false:=
    (canonical_at origin _ _ _ 2409 (Or.inr (Or.inl rfl)) old.2).trans ctx.hg0
  have oS:(run EntryFuse.field5 m s).basis (base 2410)=false:=
    (canonical_at origin _ _ _ 2410 (Or.inr (Or.inr (Or.inl rfl))) old.2).trans ctx.hs0
  have eq:run EntryFuse.field5 m s=run fieldE m s:=(fieldE_eq origin ctx ha x hx0 hx trace Y s m hin).symm
  exact (EntryFuse.hosted_pair5 EntryFuse.field5 fieldE s s m m oldFree.1 oldFree.2 fieldE_free.1 fieldE_free.2
    iG h511 iS h1542 iG h511 iS h1542 oG oS eq).symm

theorem hosted_X_eq (origin:BasisState)(ctx:Context origin)(ha:regValue (skywalkSharedField base).a origin=0)
    (x:Nat)(hx0:0<x)(hx:x<p)
    (trace:skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y:Fp)(s:State)(m:List Bool)(hin:FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (h511:s.basis (base 511)=true)(h1542:s.basis (base 1542)=false):
    run (hosted fieldX) m s=run ExitFuse.hostExitSegment5 m s:=by
  have old:=oldX_spec origin ctx ha x hx0 hx trace Y s m hin
  have oldFree:base 511∉wires ExitFuse.exitSegment5 ∧ base 1542∉wires ExitFuse.exitSegment5:=
    ⟨fun h=>(KernelOB5.seg_free false).1 (ExitFuse.exitSegment5_sub.wires_sub h),
      fun h=>(KernelOB5.seg_free false).2 (ExitFuse.exitSegment5_sub.wires_sub h)⟩
  have iG:s.basis (base 2409)=false:=(canonical_at origin Y 0 s 2409 (Or.inr (Or.inl rfl)) hin).trans ctx.hg0
  have iS:s.basis (base 2410)=false:=(canonical_at origin Y 0 s 2410 (Or.inr (Or.inr (Or.inl rfl))) hin).trans ctx.hs0
  have oG:(run ExitFuse.exitSegment5 m s).basis (base 2409)=false:=
    (field_at origin _ _ _ 2409 (Or.inr (Or.inl rfl)) old.2).trans ctx.hg0
  have oS:(run ExitFuse.exitSegment5 m s).basis (base 2410)=false:=
    (field_at origin _ _ _ 2410 (Or.inr (Or.inr (Or.inl rfl))) old.2).trans ctx.hs0
  have eq:run ExitFuse.exitSegment5 m s=run fieldX m s:=(fieldX_eq origin ctx ha x hx0 hx trace Y s m hin).symm
  exact (EntryFuse.hosted_pair5 ExitFuse.exitSegment5 fieldX s s m m oldFree.1 oldFree.2 fieldX_free.1 fieldX_free.2
    iG h511 iS h1542 iG h511 iS h1542 oG oS eq).symm

end ECDSAAdd.Entrant.QSiteDirectFields
end QSiteDirectBoundary


section QSitePreparedStates
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFields
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires compactForward5 compactReverse5 W.compactForward5
  Stack5.forward5 StackOB5.forward stackForwardT NativeFirstDirect.forward NativeFirstKnown.inverse
  skywalkArithmeticClear History5.allEncode History5.encodePrefix SkywalkTrace.trace SkywalkTrace.next
  Nat.iterate mixedTranscriptUnitTrace OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT OneBankReplay5.replay
  OB5.forward OB5.reverse
theorem exit_prepared
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s:State)(m1 m2 m3:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)
    (hg0:s.basis (base 2409)=false)(hs0:s.basis (base 2410)=false)(hb:s.basis (base 2400)=true)
    (v1 v2 v3:State)(h1:run (NativeFirstDirect.forward base) m1 s=v1)
    (h2:run stackForwardT m2 v1=v2)(h3:run (skywalkArithmeticClear base) m3 v2=v3) :
    ∃(origin:BasisState)(_ctx:Context origin),regValue (skywalkSharedField base).a origin=0 ∧
      skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) ∧
      FieldFrameOB5.EncodedCanonicalFrame origin Y 0 v3 ∧ v3.basis (base 511)=true ∧ v3.basis (base 1542)=false := by
  let t2 := run (compactForward5 base 1 511) m2 v1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  rw [h1] at first
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ v1.basis).mpr first
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 v1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp gap hx cop v1 m2 m2 first
  have e2 : v2=pullState (OB5.sig 511) t2 := by
    rw [←h2,stackForwardT_run hn hlo x hx0 hx v1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx v1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : v3=pullState (OB5.sig 511) t3 := by rw [←h3,e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin v1 t2 t3 h1 rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have hben:origin.basis (base 2400)=true:=(facts.controls _ (by simp)).trans hb
  let ctx:Context origin.basis:=⟨⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩,hben⟩
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 v3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) v3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have bits:=EntryFuse.encoded_host_bits5 x hx0 hx origin t3 v3 facts.trace encEq e3
  exact ⟨origin.basis,ctx,facts.sourceZero,facts.trace,placedInput,bits.1,bits.2⟩



theorem pool_three_states (A B C:Program)
    (ha:wires A⊆(skywalkPoolWires base).toFinset)
    (hb:wires B⊆(skywalkPoolWires base).toFinset)(hc:wires C⊆(skywalkPoolWires base).toFinset)
    (s t:State)(m1 m2 m3:List Bool)(ph:s.phase=t.phase)
    (same:∀q,q∉wireBlock base 2056 256 → s.basis q=t.basis q)
    (a1 a2 a3 v1 v2 v3:State)
    (h1a:run A m1 s=a1)(h2a:run B m2 a1=a2)(h3a:run C m3 a2=a3)
    (h1v:run A m1 t=v1)(h2v:run B m2 v1=v2)(h3v:run C m3 v2=v3):
    a3.phase=v3.phase ∧ (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
      (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q):=by
  have h:=EntryFuse.pool_three A B C ha hb hc s t m1 m2 m3 ph same v1 v2 v3 h1v h2v h3v
  simpa only [h1a,h2a,h3a] using h

theorem entry_prepared_steps
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s t:State)(m1 m2 m3 _m4:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)
    (hg0:s.basis (base 2409)=false)(hs0:s.basis (base 2410)=false)(hb:s.basis (base 2400)=true)
    (phase:t.phase=s.phase)(same:∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value:regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (a1 a2 a3:State)
    (ha1:run (NativeFirstDirect.forward base) m1 s=a1)
    (ha2:run stackForwardT m2 a1=a2)(ha3:run (skywalkArithmeticClear base) m3 a2=a3)
    (v1 v2 v3:State)
    (h1:run (NativeFirstDirect.forward base) m1 t=v1)
    (h2:run stackForwardT m2 v1=v2)(h3:run (skywalkArithmeticClear base) m3 v2=v3) :
    ∃(origin:BasisState)(_ctx:Context origin),regValue (skywalkSharedField base).a origin=0 ∧
      skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) ∧
      FieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 v3 ∧ v3.basis (base 511)=true ∧ v3.basis (base 1542)=false := by
  obtain ⟨origin,ctx,ha,tr,cin,b511,b1542⟩:=exit_prepared hn hlo ho hf x Y hx0 hx s m1 m2 m3
    hin hg0 hs0 hb a1 a2 a3 ha1 ha2 ha3
  have paired:=pool_three_states (NativeFirstDirect.forward base) stackForwardT (skywalkArithmeticClear base)
    EntryFuse.first_pool5 EntryFuse.forward_pool5 EntryFuse.clear_pool5 s t m1 m2 m3 phase.symm
    (fun q hq=>(same q hq).symm) a1 a2 a3 v1 v2 v3 ha1 ha2 ha3 h1 h2 h3
  have target:regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2):=
    (regValue_congr _ _ _ paired.2.2).trans value
  have logicalSame:∀q,q∉wireBlock base 2056 256 →
      (pullState (OB5.sig 511) v3).basis q=(pullState (OB5.sig 511) a3).basis q:=by
    intro q hq
    exact (paired.2.1 _ (EntryFuse.sig_num_away q hq)).symm
  have logicalValue:regValue (wireBlock base 2056 256) (pullState (OB5.sig 511) v3).basis=centerWord (Y/2):=by
    apply (regValue_congr _ _ _ ?_).trans target
    intro q hq
    change v3.basis (OB5.sig 511 q)=v3.basis q
    rw [EntryFuse.sig_num_fix q hq]
  have retarget:=EntryFuse.encoded_retarget5 hn origin ctx.parity ctx.env.2.2 Y
    (pullState (OB5.sig 511) a3) (pullState (OB5.sig 511) v3) paired.1.symm logicalSame logicalValue cin
  have aw(i:Nat)(hi:i<2056):base i∉wireBlock base 2056 256:=OwnPlusHost.not_block i 2056 256 (by omega)
  exact ⟨origin,ctx,ha,tr,retarget,((paired.2.1 _ (aw 511 (by omega))).symm.trans b511),
    ((paired.2.1 _ (aw 1542 (by omega))).symm.trans b1542)⟩


theorem entry_prepared
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s t:State)(m1 m2 m3 _m4:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)
    (hg0:s.basis (base 2409)=false)(hs0:s.basis (base 2410)=false)(hb:s.basis (base 2400)=true)
    (phase:t.phase=s.phase)(same:∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value:regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3:State)
    (h1:run (NativeFirstDirect.forward base) m1 t=v1)
    (h2:run stackForwardT m2 v1=v2)(h3:run (skywalkArithmeticClear base) m3 v2=v3) :
    ∃(origin:BasisState)(_ctx:Context origin),regValue (skywalkSharedField base).a origin=0 ∧
      skywalkTapeControls origin (skywalkSharedTape base)=SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) ∧
      FieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 v3 ∧ v3.basis (base 511)=true ∧ v3.basis (base 1542)=false := by
  let a1:=run (NativeFirstDirect.forward base) m1 s
  let a2:=run stackForwardT m2 a1
  let a3:=run (skywalkArithmeticClear base) m3 a2
  exact entry_prepared_steps hn hlo ho hf x Y hx0 hx s t m1 m2 m3 _m4 hin hg0 hs0 hb phase same value
    a1 a2 a3 rfl rfl rfl v1 v2 v3 h1 h2 h3

end ECDSAAdd.Entrant.QSiteDirectFields
end QSitePreparedStates


section QSiteRawContracts
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFields
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires rawE rawX
theorem rawE_enabled
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) (hb:s.basis (base 2400)=true)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run rawE m t) := by
  let P : State → State → Prop := fun initial out =>
    initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) (hosted fieldE) (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hp hs hv
      obtain ⟨origin,ctx,ha,tr,hinF,h511,h1542⟩:=entry_prepared hn hlo ho hf x Y hx0 hx s initial
        m1 m2 m3 m4 hin hg0 hs0 hb hp hs hv v1 v2 v3 h1 h2 h3
      have eq:=hosted_E_eq origin ctx ha x hx0 hx tr (Y/2) v3 m4 hinF h511 h1542
      have old4:run EntryFuse.hostField5 m4 v3=v4:=by rw [←eq];exact h4
      exact EntryFuse.kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 hp hs hv v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 old4 h5 h6 h7) t m
  simpa only [rawE,List.append_assoc] using all phase same value

theorem rawX_enabled
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) (hb:s.basis (base 2400)=true) :
    let v := run rawX m s
    v.phase=s.phase ∧ regValue (wireBlock base 2056 256) v.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → v.basis q=s.basis q := by
  let P : State → State → Prop := fun initial out => initial=s →
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) (hosted fieldX) (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 eq
      subst eq
      let a4 := run (KernelOB5.segH false) [] v3
      let a5 := run (skywalkArithmeticClear base) m5 a4
      let a6 := run (stackReverseT) m6 a5
      let a7 := run (NativeFirstKnown.inverse base) m7 a6
      obtain ⟨origin,ctx,ha,tr,hinF,h511,h1542⟩:=exit_prepared hn hlo ho hf x Y hx0 hx initial
        m1 m2 m3 hin hg0 hs0 hb v1 v2 v3 h1 h2 h3
      have eq:=hosted_X_eq origin ctx ha x hx0 hx tr Y v3 m4 hinF h511 h1542
      have old4:run ExitFuse.hostExitSegment5 m4 v3=v4:=by rw [←eq];exact h4
      exact ExitFuse.exitKernel5_states hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 v1 v2 v3 v4 v5 v6 v7 a4 a5 a6 a7 h1 h2 h3 old4 h5 h6 h7 rfl rfl rfl rfl) s m
  simpa only [rawX,List.append_assoc] using all rfl

theorem rawE_correct
    (away:base 2400∉wires rawE)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run rawE m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := forceControl5 s
  let b := forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := forceControl5_true s
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [forceControl5_true,forceControl5_true]
    · rw [forceControl5_keep t q e,forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong := rawE_enabled hn hlo ho hf x Y hx0 hx a b m input hg hs ab phases paired half
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree := pool_run_agrees rawE (wires rawE) (Finset.Subset.refl _) m t b rfl
    (fun q hq => (forceControl5_keep t q (fun e => away (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run rawE m t).basis q=(run rawE m b).basis q := by
    by_cases used : q∈wires rawE
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e => numAway (e ▸ hq))
  · intro q hq
    by_cases e : q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ away).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (forceControl5_keep s q e))

end ECDSAAdd.Entrant.QSiteDirectFields
end QSiteRawContracts

section QSiteFinalContracts
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFields
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 EntryFuse
attribute [local irreducible] run wires rawE rawX

theorem rawX_correct (away:base 2400∉wires rawX)
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s:State)(m:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)
    (hg0:s.basis (base 2409)=false)(hs0:s.basis (base 2410)=false):
    (run rawX m s).phase=s.phase ∧ regValue (wireBlock base 2056 256) (run rawX m s).basis=
      centerWord (Y*(x:Fp)/2) ∧ ∀q,q∉wireBlock base 2056 256 → (run rawX m s).basis q=s.basis q:=by
  let t:=forceControl5 s
  have keep(q:Wire)(h:q≠base 2400):t.basis q=s.basis q:=forceControl5_keep s q h
  have shared:base 2400∉skywalkSharedWires base:=ho _ (by simp)
  have dx:base 2400∉wireBlock base 770 256:=fun h=>shared (arith_block_subset_shared base 770 256 (by omega) h)
  have dy:base 2400∉wireBlock base 2056 256:=fun h=>shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input:SkywalkArithmeticInput base x Y.val t.basis:=by
    refine ⟨?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq=>keep q (fun e=>dx (e ▸ hq)))).trans hin.1
    · exact (regValue_congr _ _ _ (fun q hq=>keep q (fun e=>dy (e ▸ hq)))).trans hin.2.1
    · intro q hq hdx hdy
      rw [keep q (fun e=>shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have strong:=rawX_enabled hn hlo ho hf x Y hx0 hx t m input
    ((keep _ (by decide)).trans hg0) ((keep _ (by decide)).trans hs0) (forceControl5_true s)
  simp only [forceControl5_true,directSkywalkResult,if_true,skywalkArithmeticResult,Bool.false_eq_true,if_false] at strong
  have agree:=pool_run_agrees rawX (wires rawX) (Finset.Subset.refl _) m s t rfl
    (fun q hq=>(keep q (fun e=>away (e ▸ hq))).symm)
  have sameRun(q:Wire)(hq:q≠base 2400):(run rawX m s).basis q=(run rawX m t).basis q:=by
    by_cases used:q∈wires rawX
    · exact agree.2 q used
    · rw [run_preserves_outside _ _ _ _ used,run_preserves_outside _ _ _ _ used,keep q hq]
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq=>sameRun q (fun e=>dy (e ▸ hq)))).trans strong.2.1
  · intro q hq
    by_cases qb:q=base 2400
    · subst q;exact run_preserves_outside _ _ _ _ away
    · rw [sameRun q qb,strong.2.2 q hq,keep q qb]

def kernelE:Program:=Q8FusionPhase.relocated (hosted fieldE)
def kernelX:Program:=Q8FusionPhase.relocated (hosted fieldX)

abbrev Free (F:Program):Prop:=∀q∈[1026,1541,1542,1540],base q∉wires F

theorem shape6 (F:Program):Q6FusionPhase.kernel F=Q5FusionPhase.relocated F:=by
  simp only [Q6FusionPhase.kernel,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
    Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5FusionPhase.relocated,
    Q5Global718.firstPhase,Q5Global718.lastPhase]

theorem relocate_eq (F:Program)(free:Free F)
    (hn:(skywalkSharedWires base).Nodup)(x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(a b:State)(m:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val a.basis)(same:Q5FusionPhase.Paired a b)
    (frame:∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel F) m b).basis q=a.basis q):
    run (Q8FusionPhase.relocated F) m b=run (Q5FusionPhase.kernel F) m b:=by
  have e5:=Q5FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F hin same (free 1026 (by simp)) frame
  have f6:∀q,q∉wireBlock base 2056 256 → (run (Q6FusionPhase.kernel F) m b).basis q=a.basis q:=by
    rw [shape6,e5]
    exact frame
  have e6:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F hin same (free 1541 (by simp)) f6
  have f7:∀q,q∉wireBlock base 2056 256 → (run (Q7FusionPhase.kernel F) m b).basis q=a.basis q:=by
    rw [Q7FusionPhase.old_shape,e6]
    exact f6
  have e7:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F hin same (free 1542 (by simp)) f7
  have f8:∀q,q∉wireBlock base 2056 256 → (run (Q8FusionPhase.kernel F) m b).basis q=a.basis q:=by
    rw [Q8FusionPhase.old_shape,e7]
    exact f7
  have e8:=Q8FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F hin same (free 1540 (by simp)) f8
  rw [e8,Q8FusionPhase.old_shape,e7,Q7FusionPhase.old_shape,e6,shape6,e5]

theorem rawE_shape:Q5FusionPhase.kernel (hosted fieldE)=rawE:=by
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,rawE,List.append_assoc]
 theorem rawX_shape:Q5FusionPhase.kernel (hosted fieldX)=rawX:=by
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,rawX,List.append_assoc]

theorem kernelE_correct (away:base 2400∉wires rawE)(free:Free (hosted fieldE))
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s t:State)(m:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)(hg:s.basis (base 2409)=false)(hs:s.basis (base 2410)=false)
    (phase:t.phase=s.phase)(same:∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value:regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)):
    (run kernelE m t).phase=s.phase ∧ regValue (wireBlock base 2056 256) (run kernelE m t).basis=
      (skywalkArithmeticResult true x Y).val ∧ ∀q,q∉wireBlock base 2056 256 → (run kernelE m t).basis q=s.basis q:=by
  have old:=rawE_correct away hn hlo ho hf x Y hx0 hx s t m hin hg hs phase same value
  have frame:∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel (hosted fieldE)) m t).basis q=s.basis q:=by
    simpa only [rawE_shape] using old.2.2
  have eq:=relocate_eq (hosted fieldE) free hn x Y hx0 hx s t m hin same frame
  simpa only [kernelE,eq,rawE_shape] using old

theorem kernelX_correct (away:base 2400∉wires rawX)(free:Free (hosted fieldX))
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s:State)(m:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)(hg:s.basis (base 2409)=false)(hs:s.basis (base 2410)=false):
    (run kernelX m s).phase=s.phase ∧ regValue (wireBlock base 2056 256) (run kernelX m s).basis=
      centerWord (Y*(x:Fp)/2) ∧ ∀q,q∉wireBlock base 2056 256 → (run kernelX m s).basis q=s.basis q:=by
  have old:=rawX_correct away hn hlo ho hf x Y hx0 hx s m hin hg hs
  have frame:∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel (hosted fieldX)) m s).basis q=s.basis q:=by
    simpa only [rawX_shape] using old.2.2
  have eq:=relocate_eq (hosted fieldX) free hn x Y hx0 hx s s m hin (fun _ _=>rfl) frame
  simpa only [kernelX,eq,rawX_shape] using old

end ECDSAAdd.Entrant.QSiteDirectFields
end QSiteFinalContracts

section QSiteLiteralSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFree
open Arithmetic MappedCompressed Secp256k1 BalancedField QSiteDirectControls
attribute [local irreducible] wires OwnQ6Core5.kernel

def Bad(q:Nat):Prop:=q∈[765,766,767,2312,1026,1540,1541,1539,2400,2410,511]

theorem bad_cases(q:Nat)(hq:Bad q):q=765 ∨ q=766 ∨ q=767 ∨ q=2312 ∨ q=1026 ∨ q=1540 ∨
    q=1541 ∨ q=1539 ∨ q=2400 ∨ q=2410 ∨ q=511:=by
  simpa only [Bad,List.mem_cons,List.not_mem_nil,or_false] using hq

theorem data_away(q:Nat)(hq:Bad q):base q∉R ∧ base q∉YR:=by
  change base q∉(balancedSharedPorts base (base 2409)).r ∧ base q∉(balancedSharedPorts base (base 2409)).y
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  have h:=bad_cases q hq
  constructor
  · exact OwnPlusHost.not_block q 2056 256 (by rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  · exact OwnPlusHost.not_block q 770 256 (by rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)

theorem original_support(divide:Bool)(g:Wire):
    wires (OwnQ6Core5.half divide (OneBankCell5.ports base g))⊆(g::OneBankCell5.ids.map base).toFinset:=by
  have k:=(OwnQ6Core5.support divide (OneBankCell5.ports base g) (OneBankCell5.ports_widths base g)).trans
    (OneBankCell5.ports_wires_sub base g _ (Finset.Subset.refl _))
  have sg:g∈(g::OneBankCell5.ids.map base).toFinset:=by simp
  simpa only [OwnQ6Core5.half,wires_append,wires,Instr.wires,Finset.union_empty,
    Finset.union_subset_iff,Finset.singleton_subset_iff,OneBankCell5.ports_sign] using And.intro (And.intro sg k) sg

theorem original_free(divide:Bool)(k q:Nat)(hk:k<511)
    (hq:q=765 ∨ q=766 ∨ q=767 ∨ q=2312 ∨ q=1026 ∨ q=1541):
    base q∉wires (OwnQ6Core5.half divide (OneBankCell5.ports base (base k))):=by
  let L:=OneBankCell5.ports base (base k)
  have hw:=OneBankCell5.ports_widths base (base k)
  have hn:=OneBankCell5.ports_nodup_injective base (base k) base_injective (fresh_index k (by omega))
  have core:base q∉wires (OwnQ6Core5.kernel divide L):=by
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    · exact OwnQ6Core5.kernel_unused_free divide L hw hn _ (by simp [L,OneBankCell5.ports])
    · exact OwnQ6Core5.kernel_unused_free divide L hw hn _ (by simp [L,OneBankCell5.ports])
    · exact OwnQ6Core5.kernel_unused_free divide L hw hn _ (by simp [L,OneBankCell5.ports])
    · exact OwnQ6Core5.kernel_unused_free divide L hw hn _ (by simp [L,OneBankCell5.ports])
    · have e:L.carry.getD 255 0=base 1026:=by rfl
      simpa only [e] using OwnQ6Core5.kernel_last_free divide L hw hn
    · have e:L.carry.getD 254 0=base 1541:=by rfl
      simpa only [e] using OwnQ6Core5.kernel_retired_free divide L hw hn
  have ne:base q≠base k:=by
    intro e
    have h:=base_injective e
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have x:base q∉wires [.X (base k)]:=by simpa only [wires,Instr.wires,Finset.union_empty,Finset.mem_singleton] using ne
  simpa only [OwnQ6Core5.half,wires_append,Finset.mem_union,not_or,OneBankCell5.ports_sign] using And.intro (And.intro x core) x

theorem half_free(divide:Bool)(k q:Nat)(hk:k<511)(hq:Bad q):base q∉wires (half divide (base k)):=by
  have bc:=bad_cases q hq
  by_cases hq0:q=1540
  · subst q
    rw [half,renameProgram_support]
    intro h
    obtain ⟨x,hx,e⟩:=Finset.mem_image.mp h
    have b:borrow (base 2409)=base 1540:=by simp [borrow]
    have xe:x=base 2409:=borrow.injective (e.trans b.symm)
    have old:=original_support divide (base k) (xe ▸ hx)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_map] at old
    rcases old with old|⟨i,hi,eq⟩
    · have h:=base_injective old;omega
    · have h:=base_injective eq
      have bound:=OneBankCell5.ids_bound i hi
      omega
  · have fix:borrow (base q)=base q:=by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e;exact hq0 (base_injective e)
      · intro e
        have h:=base_injective e
        rcases bc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    apply OwnPlusHost.rename_avoid borrow _ _ fix
    by_cases scalar:q=765 ∨ q=766 ∨ q=767 ∨ q=2312 ∨ q=1026 ∨ q=1541
    · exact original_free divide k q hk scalar
    · intro used
      have old:=original_support divide (base k) used
      simp only [List.mem_toFinset,List.mem_cons,List.mem_map] at old
      rcases old with eq|⟨i,hi,eq⟩
      · have e:=base_injective eq
        rcases bc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      · have e:=base_injective eq
        subst i
        simp only [OneBankCell5.ids,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hi
        rcases bc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem swap_free(q k:Nat)(hq:Bad q)(hk:k<510):base q∉wires (swapRegisters (base (1028+k)) R YR):=by
  have w: R.length=YR.length:=by rfl
  intro used
  have h:=swapRegisters_wires (base (1028+k)) R YR w used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  rcases h with eq|hr|hy
  · have e:=base_injective eq
    have b:=bad_cases q hq
    rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · exact (data_away q hq).1 hr
  · exact (data_away q hq).2 hy

theorem cell_letter_free(divide:Bool)(q i:Nat)(hq:Bad q)(hi:i<510):
    base q∉wires (cell divide (tapeLetter i).1.1 (tapeLetter i).1.2):=by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i (by omega)]
  have h:=half_free divide i q (by omega) hq
  have s:=swap_free q i hq hi
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,wires_append,Finset.mem_union,not_or]
  · exact ⟨s,h⟩
  · exact ⟨h,s⟩

end ECDSAAdd.Entrant.QSiteDirectFree
end QSiteLiteralSupport

section QSiteReplayOmissions
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFree
open Arithmetic MappedCompressed CompressedAllocation Secp256k1 BalancedField QSiteDirectControls
attribute [local irreducible] wires

theorem codec_free(q start:Nat)(hq:Bad q)(hs:start+5≤510)(P:Program)
    (hp:P=History5.encode base start ∨ P=History5.decode base start):base q∉wires P:=by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base q) used
  have bound:History5.historyId start r<510 ∨ (1028≤History5.historyId start r ∧ History5.historyId start r<1538):=by
    have hr:=r.isLt
    unfold History5.historyId
    split <;> omega
  have e:=base_injective eq
  have b:=bad_cases q hq
  rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem raw_free(divide:Bool)(q:Nat)(hq:Bad q)(ls:List MixedTranscriptLetter)
    (hl:∀l∈ls,∃i,i<510 ∧ l=tapeLetter i):base q∉wires (QSiteDirectReplay.rawReplay divide ls):=by
  induction ls with
  | nil=>simp [QSiteDirectReplay.rawReplay,wires]
  | cons l ls ih=>
    obtain ⟨i,hi,eq⟩:=hl l (by simp)
    have head:=eq ▸ cell_letter_free divide q i hq hi
    have tail:=ih (fun l h=>hl l (List.mem_cons_of_mem _ h))
    cases divide <;> simp only [QSiteDirectReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or]
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem letters_index(j:Nat)(hj:j<102)(l:MixedTranscriptLetter)(hl:l∈Replay5.letters j):
    ∃i,i<510 ∧ l=tapeLetter i:=by
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
  have h:=List.mem_range.mp hk
  exact ⟨5*j+k,by omega,rfl⟩

theorem rest_index(l:MixedTranscriptLetter)(hl:l∈Replay5.restLetters):∃i,i<510 ∧ l=tapeLetter i:=by
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
  have h:=List.mem_range'_1.mp hk
  exact ⟨k,by omega,rfl⟩

theorem perm_fix(q:Nat)(hq:Bad q):¬Placement5.zeroRegion q:=by
  have b:=bad_cases q hq
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem shift_fix(e:Equiv.Perm Nat)(fix:∀q,¬Placement5.zeroRegion q → e q=q)(q:Nat)(hq:Bad q):
    shifted e (base q)=base q:=by
  rw [shifted_base,fix q (perm_fix q hq)]

theorem packet_free(divide:Bool)(j q:Nat)(hj:j<102)(hq:Bad q):
    base q∉wires (QSiteDirectReplay.packet divide j):=by
  apply OwnPlusHost.rename_avoid _ _ _ (shift_fix _ (fun q h=>Placement5.pi_outside j q hj h) q hq)
  simp only [QSiteDirectReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_free q (5*j) hq (by omega) _ (Or.inr rfl),
    raw_free divide q hq _ (letters_index j hj)⟩,codec_free q (5*j) hq (by omega) _ (Or.inl rfl)⟩

theorem first_free(divide:Bool)(q:Nat)(hq:Bad q):base q∉wires (QSiteDirectReplay.firstPacket divide):=by
  have sw:base q∉wires QSiteDirectControls.firstSwap:=swap_free q 0 hq (by decide)
  have sm:base q∉wires QSiteDirectControls.firstSwapM:=by
    simpa only [QSiteDirectControls.firstSwapM,QSiteDirectControls.firstSwap,UncompSwap.mswap_wires] using sw
  have rest:=raw_free divide q hq Replay5.restLetters rest_index
  have body:base q∉wires (QSiteDirectReplay.firstBody divide):=by
    cases divide <;> simp only [QSiteDirectReplay.firstBody,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or]
    · exact ⟨rest,sm⟩
    · exact ⟨sw,rest⟩
  apply OwnPlusHost.rename_avoid _ _ _ (shift_fix _ (fun q h=>Placement5.pi_outside 0 q (by decide) h) q hq)
  simp only [QSiteDirectReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_free q 0 hq (by omega) _ (Or.inr rfl),body⟩,
    codec_free q 0 hq (by omega) _ (Or.inl rfl)⟩

theorem end_free(divide:Bool)(q:Nat)(hq:Bad q):base q∉wires (QSiteDirectReplay.endPacket divide):=by
  apply OwnPlusHost.rename_avoid _ _ _ (shift_fix _ Placement5.pi0_outside q hq)
  cases divide
  · change base q∉wires QSiteInverseDirect.program
    rw [QSiteInverseDirect.program,renameProgram_support]
    intro used
    obtain ⟨x,hx,e⟩:=Finset.mem_image.mp used
    by_cases z:q=1540
    · subst q
      have sw:borrow (base 2409)=base 1540:=by simp [borrow]
      have xe:x=base 2409:=borrow.injective (e.trans sw.symm)
      exact QSiteInverseDirect.raw_free 2409 (by simp) (xe ▸ hx)
    · have bc:=bad_cases q hq
      have ne:base q≠base 1540:=fun e=>z (base_injective e)
      have ne2:base q≠base 2409:=by
        intro e
        have same:=base_injective e
        rcases bc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      have sw:borrow (base q)=base q:=by simp only [borrow,Equiv.swap_apply_of_ne_of_ne ne ne2]
      have xe:x=base q:=borrow.injective (e.trans sw.symm)
      have hm:q∈[765,766,767,2312,1026,1541,1539,2400,2410,511,2409]:=by
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        rcases bc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> tauto
      exact QSiteInverseDirect.raw_free q hm (xe ▸ hx)
  · intro used
    have h:=QSiteTerminalDirect.support (base q) used
    have b:=bad_cases q hq
    rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [QSiteTerminalDirect.allowed,MappedCompressed.base] at h

theorem groups_free(divide:Bool)(j n q:Nat)(hj:j+n≤102)(hq:Bad q):
    base q∉wires (QSiteDirectReplay.groups divide j n):=by
  induction n generalizing j with
  | zero=>simp [QSiteDirectReplay.groups,PacketSequence.program,wires]
  | succ n ih=>
    have h:=packet_free divide j q (by omega) hq
    have r:=ih (j+1) (by omega)
    simp only [QSiteDirectReplay.groups] at r
    cases divide <;> simp only [QSiteDirectReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or]
    · exact ⟨r,h⟩
    · exact ⟨h,r⟩

theorem logical_free(divide:Bool)(q:Nat)(hq:Bad q):base q∉wires (QSiteDirectReplay.logicalReplay divide):=by
  have a:=first_free divide q hq
  have b:=groups_free divide 1 101 q (by decide) hq
  have c:=end_free divide q hq
  cases divide <;> simp only [QSiteDirectReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨c,b⟩,a⟩
  · exact ⟨⟨a,b⟩,c⟩

def FinalBad(q:Nat):Prop:=q∈[765,766,767,2312,1026,1540,1541,1542,2400,2410,511]

theorem replay_free(divide:Bool)(q:Nat)(hq:FinalBad q):base q∉wires (QSiteDirectReplay.replay divide):=by
  by_cases hs:q=1542
  · subst q
    rw [QSiteDirectReplay.replay,renameProgram_support]
    intro h
    obtain ⟨x,hx,e⟩:=Finset.mem_image.mp h
    have back:OB5.sig 511 (base 1539)=base 1542:=by decide
    have xe:x=base 1539:=(OB5.sig_injective 511 (by decide)) (e.trans back.symm)
    exact logical_free divide 1539 (by simp [Bad]) (xe ▸ hx)
  · have old:Bad q:=by
      simp only [FinalBad,Bad,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
      tauto
    have fix:OB5.sig 511 (base q)=base q:=by
      have b:=hq
      simp only [FinalBad,List.mem_cons,List.not_mem_nil,or_false] at b
      rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | decide | exact False.elim (hs rfl)
    exact OwnPlusHost.rename_avoid
      ⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by decide),OB5.sig_invol 511 (by decide)⟩ _ _ fix
      (logical_free divide q old)

end ECDSAAdd.Entrant.QSiteDirectFree
end QSiteReplayOmissions


section QSiteConverterOmissions
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false


namespace ECDSAAdd.Entrant.QSiteDirectFree
open Arithmetic MappedCompressed Secp256k1 BalancedField QSiteDirectControls
attribute [local irreducible] wires

theorem old_meta_free(q:Nat)(hq:q∈[2400,2409,2410]):
    base q∉wires OwnQ5Endpoint.centerT ∧ base q∉wires OwnQ5Endpoint.canonT:=by
  have none:base q∉(HalfField.ids.map base).toFinset:=by
    intro used
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp used)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> omega
  have first:base q∉wires HalfField.centerT ∧ base q∉wires HalfField.canonT:=
    ⟨fun h=>none (HalfField.centerT_sites h),fun h=>none (HalfField.canonT_sites h)⟩
  have f0:HalfFieldOB5.endpointMap (base q)=base q:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> decide +kernel
  have a:base q∉wires HalfFieldOB5.centerT ∧ base q∉wires HalfFieldOB5.canonT:=
    ⟨OwnPlusHost.rename_avoid _ _ _ f0 first.1,OwnPlusHost.rename_avoid _ _ _ f0 first.2⟩
  have f1:OwnPlusEndpoint.swap (base q)=base q:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> decide
  have b:base q∉wires OwnPlusEndpoint.centerT ∧ base q∉wires OwnPlusEndpoint.canonT:=
    ⟨OwnPlusHost.rename_avoid _ _ _ f1 a.1,OwnPlusHost.rename_avoid _ _ _ f1 a.2⟩
  have f2:OwnGuardEndpoint.swap (base q)=base q:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> decide
  have c:base q∉wires OwnGuardEndpoint.centerT ∧ base q∉wires OwnGuardEndpoint.canonT:=
    ⟨OwnPlusHost.rename_avoid _ _ _ f2 b.1,OwnPlusHost.rename_avoid _ _ _ f2 b.2⟩
  have f3:OwnQ4Endpoint.swap (base q)=base q:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> decide
  have d:base q∉wires OwnQ4Endpoint.centerT ∧ base q∉wires OwnQ4Endpoint.canonT:=
    ⟨OwnPlusHost.rename_avoid _ _ _ f3 c.1,OwnPlusHost.rename_avoid _ _ _ f3 c.2⟩
  have f4:OwnQ5Endpoint.swap (base q)=base q:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> decide
  exact ⟨OwnPlusHost.rename_avoid _ _ _ f4 d.1,OwnPlusHost.rename_avoid _ _ _ f4 d.2⟩

theorem old_scalar_free(q:Nat)(hq:q∈[765,766,767,2312,1026]):
    base q∉wires OwnQ5Endpoint.centerT ∧ base q∉wires OwnQ5Endpoint.canonT:=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · have a:=OwnGuardEndpoint.plus_free
    have b:base 765∉wires OwnQ4Endpoint.centerT ∧ base 765∉wires OwnQ4Endpoint.canonT:=
      ⟨OwnPlusHost.rename_avoid OwnQ4Endpoint.swap _ _ (by decide) a.1,
        OwnPlusHost.rename_avoid OwnQ4Endpoint.swap _ _ (by decide) a.2⟩
    exact ⟨OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) b.1,
      OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) b.2⟩
  · have a:=OwnPlusEndpoint.plus_free
    have b:base 766∉wires OwnGuardEndpoint.centerT ∧ base 766∉wires OwnGuardEndpoint.canonT:=
      ⟨OwnPlusHost.rename_avoid OwnGuardEndpoint.swap _ _ (by decide) a.1,
        OwnPlusHost.rename_avoid OwnGuardEndpoint.swap _ _ (by decide) a.2⟩
    have c:base 766∉wires OwnQ4Endpoint.centerT ∧ base 766∉wires OwnQ4Endpoint.canonT:=
      ⟨OwnPlusHost.rename_avoid OwnQ4Endpoint.swap _ _ (by decide) b.1,
        OwnPlusHost.rename_avoid OwnQ4Endpoint.swap _ _ (by decide) b.2⟩
    exact ⟨OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) c.1,
      OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) c.2⟩
  · exact ⟨OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) OwnQ4Endpoint.plus_free.1,
      OwnPlusHost.rename_avoid OwnQ5Endpoint.swap _ _ (by decide) OwnQ4Endpoint.plus_free.2⟩
  · exact OwnQ5Endpoint.parity_free
  · exact OwnQ5Endpoint.plus_free

theorem converters_free(q:Nat)(hq:FinalBad q):
    base q∉wires QSiteDirectControls.center ∧ base q∉wires QSiteDirectControls.canonical:=by
  by_cases special:q=1540
  · subst q
    have avoid(P:Program)(free:base 2409∉wires P):base 1540∉wires (renameProgram borrow P):=by
      rw [renameProgram_support]
      intro used
      obtain ⟨x,hx,e⟩:=Finset.mem_image.mp used
      have back:borrow (base 2409)=base 1540:=by simp [borrow]
      have xe:x=base 2409:=borrow.injective (e.trans back.symm)
      exact free (xe ▸ hx)
    exact ⟨avoid _ (old_meta_free 2409 (by simp)).1,avoid _ (old_meta_free 2409 (by simp)).2⟩
  · have fix:borrow (base q)=base q:=by
      simp only [FinalBad,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | decide | exact False.elim (special rfl)
    have old:base q∉wires OwnQ5Endpoint.centerT ∧ base q∉wires OwnQ5Endpoint.canonT:=by
      by_cases scalar:q∈[765,766,767,2312,1026]
      · exact old_scalar_free q scalar
      · by_cases isMeta:q∈[2400,2410]
        · exact old_meta_free q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at isMeta ⊢; tauto)
        · by_cases retired:q=1541
          · subst q;exact OwnQ6EndpointFree.endpoint_free
          · have none:base q∉OB5Support.segSites:=by
              intro used
              obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp used)
              have eq:=base_injective e
              subst i
              simp only [OB5Support.segIndices,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hi
              simp only [FinalBad,List.mem_cons,List.not_mem_nil,or_false] at hq
              rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
            exact ⟨fun h=>none (OwnQ5Endpoint.support.1 h),fun h=>none (OwnQ5Endpoint.support.2 h)⟩
    exact ⟨OwnPlusHost.rename_avoid borrow _ _ fix old.1,OwnPlusHost.rename_avoid borrow _ _ fix old.2⟩

end ECDSAAdd.Entrant.QSiteDirectFree

end QSiteConverterOmissions

section QSiteAllOmissions
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.QSiteDirectFree
open Arithmetic MappedCompressed Secp256k1 BalancedField QSiteDirectControls QSiteDirectFields
attribute [local irreducible] wires

theorem copy_free(q:Nat)(hq:FinalBad q):base q∉wires HalfFieldOB5.copyN:=by
  have bad:Bad q ∨ q=1542:=by
    simp only [Bad,FinalBad,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have da:base q∉R ∧ base q∉YR:=by
    rcases bad with b|rfl
    · exact data_away q b
    · change base 1542∉(balancedSharedPorts base (base 2409)).r ∧ base 1542∉(balancedSharedPorts base (base 2409)).y
      rw [balancedSharedPorts_r,balancedSharedPorts_y]
      exact ⟨OwnPlusHost.not_block 1542 2056 256 (by omega),OwnPlusHost.not_block 1542 770 256 (by omega)⟩
  have nr:R≠[]:=by
    intro e
    have h:R.length=256:=by simp [R,balancedSharedPorts_r,wireBlock_length]
    rw [e] at h
    contradiction
  have h:=copyRegister_wires none R YR (by rfl)
  simp only [List.isEmpty_iff,nr,if_false,Option.toList_none,List.nil_append] at h
  change base q∉wires (copyRegister none R YR)
  rw [h]
  simpa only [List.mem_toFinset,List.mem_append,not_or] using da

theorem fieldE_free_all(q:Nat)(hq:FinalBad q):base q∉wires QSiteDirectFields.fieldE:=by
  simp only [QSiteDirectFields.fieldE,wires_append,Finset.mem_union,not_or]
  exact ⟨replay_free true q hq,copy_free q hq,(converters_free q hq).2⟩

theorem fieldX_free_all(q:Nat)(hq:FinalBad q):base q∉wires QSiteDirectFields.fieldX:=by
  simp only [QSiteDirectFields.fieldX,wires_append,Finset.mem_union,not_or]
  exact ⟨(converters_free q hq).1,copy_free q hq,replay_free false q hq⟩

theorem hosted_free(P:Program)(all:∀q,FinalBad q → base q∉wires P)(q:Nat)(hq:FinalBad q)(hn:q≠511):
    base q∉wires (QSiteDirectFields.hosted P):=by
  have x:base q∉wires [.X (base 511)]:=by
    simp only [wires,Instr.wires,Finset.union_empty,Finset.mem_singleton]
    intro e;exact hn (base_injective e)
  have middle:base q∉wires (renameProgram HostOB5.hostSwap P):=by
    rw [renameProgram_support]
    intro h
    obtain ⟨a,ha,e⟩:=Finset.mem_image.mp h
    by_cases aS:q=1542
    · subst q
      have back:HostOB5.hostSwap (base 2410)=base 1542:=by decide
      have eq:a=base 2410:=HostOB5.hostSwap_injective (e.trans back.symm)
      exact all 2410 (by simp [FinalBad]) (eq ▸ ha)
    · by_cases bS:q=2410
      · subst q
        have back:HostOB5.hostSwap (base 1542)=base 2410:=by decide
        have eq:a=base 1542:=HostOB5.hostSwap_injective (e.trans back.symm)
        exact all 1542 (by simp [FinalBad]) (eq ▸ ha)
      · have fix:HostOB5.hostSwap (base q)=base q:=by
          simp only [FinalBad,List.mem_cons,List.not_mem_nil,or_false] at hq
          rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            first | decide | exact False.elim (hn rfl) | exact False.elim (aS rfl) | exact False.elim (bS rfl)
        have eq:a=base q:=HostOB5.hostSwap_injective (e.trans fix.symm)
        exact all q hq (eq ▸ ha)
  simpa only [QSiteDirectFields.hosted,wires_append,Finset.mem_union,not_or] using And.intro x (And.intro middle x)

theorem fields_free:QSiteDirectFields.Free (QSiteDirectFields.hosted QSiteDirectFields.fieldE) ∧
    QSiteDirectFields.Free (QSiteDirectFields.hosted QSiteDirectFields.fieldX):=by
  constructor <;> intro q hq
  all_goals
    have final:FinalBad q:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp [FinalBad]
    have ne:q≠511:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> decide
  · exact hosted_free _ fieldE_free_all q final ne
  · exact hosted_free _ fieldX_free_all q final ne

theorem raw_away:base 2400∉wires QSiteDirectFields.rawE ∧ base 2400∉wires QSiteDirectFields.rawX:=by
  have pool:base 2400∉(skywalkPoolWires base).toFinset:=by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [List.mem_range'_1] at hi
    omega
  have first:base 2400∉wires Q5Global718.firstPhase:=fun h=>pool (Q5FusionPhase.firstPhase_pool h)
  have clear:base 2400∉wires (skywalkArithmeticClear base):=fun h=>pool (EntryFuse.clear_pool5 h)
  have rev:base 2400∉wires stackReverseT:=fun h=>pool (ExitFuse.reverse_pool5 h)
  have last:base 2400∉wires (NativeFirstKnown.inverse base):=fun h=>pool (ExitFuse.inverse_pool5 h)
  have e:=hosted_free _ fieldE_free_all 2400 (by simp [FinalBad]) (by decide)
  have x:=hosted_free _ fieldX_free_all 2400 (by simp [FinalBad]) (by decide)
  constructor
  · simp only [Q5Global718.firstPhase,wires_append,Finset.mem_union,not_or] at first
    simp only [QSiteDirectFields.rawE,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨⟨⟨⟨first.1,first.2.1⟩,first.2.2⟩,e⟩,clear⟩,rev⟩,last⟩
  · simp only [Q5Global718.firstPhase,wires_append,Finset.mem_union,not_or] at first
    simp only [QSiteDirectFields.rawX,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨⟨⟨⟨⟨first.1,first.2.1⟩,first.2.2⟩,x⟩,clear⟩,rev⟩,last⟩

end ECDSAAdd.Entrant.QSiteDirectFree
end QSiteAllOmissions


section QSiteFinalKernel
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation BalancedField QSiteDirectFields
attribute [local irreducible] wires run

def chain (P:Program):Program:=
  renameProgram Q8IntegerHost.swap (renameProgram Q7IntegerHost.swap
    (renameProgram Q6IntegerHost.swap (renameProgram Q5Global718.swap P)))

theorem relocated_shape (F:Program):
    Q8FusionPhase.relocated F=chain Q5Global718.firstPhase++(F++chain Q5Global718.lastPhase):=by
  simp only [Q8FusionPhase.relocated,Q8FusionPhase.q7First,Q8FusionPhase.q7Last,Q7FusionPhase.q6First,
    Q7FusionPhase.q6Last,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,Q6IntegerHost.firstPhase,
    Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase,chain]

theorem logical_mem (i:Nat)(hi:i∈OB5Support.logicalIndices):base i∈OB5Support.logicalSites:=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩)

theorem swap_logical (a b:Nat)(ha:a∈OB5Support.logicalIndices)(hb:b∈OB5Support.logicalIndices)
    (P:Program)(hp:wires P⊆OB5Support.logicalSites):
    wires (renameProgram (Equiv.swap (base a) (base b)) P)⊆OB5Support.logicalSites:=by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=base a
  · subst w;simpa only [Equiv.swap_apply_left] using logical_mem b hb
  · by_cases y:w=base b
    · subst w;simpa only [Equiv.swap_apply_right] using logical_mem a ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne x y] using hp used

theorem chain_support (P:Program)(hp:wires P⊆OB5Support.logicalSites):wires (chain P)⊆OB5Support.logicalSites:=by
  have mem(i:Nat)(hi:717≤ i ∧ i<769 ∨ 1540≤ i ∧ i<1798 ∨ i<515 ∨ 770≤ i ∧ i<1285):i∈OB5Support.logicalIndices:=by
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
    omega
  unfold chain
  apply swap_logical 1540 721 (mem _ (by omega)) (mem _ (by omega))
  apply swap_logical 1542 720 (mem _ (by omega)) (mem _ (by omega))
  apply swap_logical 1541 719 (mem _ (by omega)) (mem _ (by omega))
  exact swap_logical 1026 718 (mem _ (by omega)) (mem _ (by omega)) P hp

theorem chain_fix (P:Program)(i:Nat)(h0:i≠1026)(h1:i≠718)(h2:i≠1541)(h3:i≠719)(h4:i≠1542)(h5:i≠720)
    (h6:i≠1540)(h7:i≠721)(free:base i∉wires P):base i∉wires (chain P):=by
  have ne(a:Nat)(hne:i≠a):base i≠base a:=fun e=>hne (base_injective e)
  unfold chain
  apply OwnPlusHost.rename_avoid _ _ _ (Equiv.swap_apply_of_ne_of_ne (ne _ h6) (ne _ h7))
  apply OwnPlusHost.rename_avoid _ _ _ (Equiv.swap_apply_of_ne_of_ne (ne _ h4) (ne _ h5))
  apply OwnPlusHost.rename_avoid _ _ _ (Equiv.swap_apply_of_ne_of_ne (ne _ h2) (ne _ h3))
  exact OwnPlusHost.rename_avoid _ _ _ (Equiv.swap_apply_of_ne_of_ne (ne _ h0) (ne _ h1)) free

theorem phases_old_free (i:Nat)(hi:i∈[2312,766,765,767]):
    base i∉wires Q5Global718.firstPhase ∧ base i∉wires Q5Global718.lastPhase:=by
  have old:base i∉wires (KernelOB5.program true):=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact OwnParityHost.kernel_parity_free true
    · exact OwnPlusFinal.kernel_free true
    · exact OwnGuardFinal.kernel_free true
    · exact OwnMinusFinal.kernel_free true
  rw [OwnQ5Integer.old_shape] at old
  simp only [wires_append,Finset.mem_union,not_or] at old
  exact ⟨old.1.1,old.2⟩

theorem phases_free (i:Nat)(hi:i∈[2312,766,765,767,1026,1541,1542,1540]):
    base i∉wires (chain Q5Global718.firstPhase) ∧ base i∉wires (chain Q5Global718.lastPhase):=by
  have ne(a b:Nat)(h:a≠b):base a≠base b:=fun e=>h (base_injective e)
  have fix(a b c:Nat)(h1:a≠b)(h2:a≠c):Equiv.swap (base b) (base c) (base a)=base a:=
    Equiv.swap_apply_of_ne_of_ne (ne _ _ h1) (ne _ _ h2)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  have q8:=Q8FusionPhase.relocated_1540_free [] (by simp [wires])
  have q7:=Q7FusionPhase.relocated_1542_free [] (by simp [wires])
  have q6:=Q6FusionPhase.relocated_1541_free [] (by simp [wires])
  have q5:=Q5FusionPhase.relocated_1026_free [] (by simp [wires])
  rw [relocated_shape] at q8
  simp only [Q7FusionPhase.relocated,Q6FusionPhase.relocated,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or,
    List.nil_append] at q5 q6 q7 q8
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have o:=phases_old_free 2312 (by simp)
    exact ⟨chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.1,
      chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.2⟩
  · have o:=phases_old_free 766 (by simp)
    exact ⟨chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.1,
      chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.2⟩
  · have o:=phases_old_free 765 (by simp)
    exact ⟨chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.1,
      chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.2⟩
  · have o:=phases_old_free 767 (by simp)
    exact ⟨chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.1,
      chain_fix _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) o.2⟩
  · unfold chain
    constructor
    · exact OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
       (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
        (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q5.1))
    · exact OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
       (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
        (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q5.2))
  · unfold chain
    constructor
    · exact OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
       (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q6.1)
    · exact OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide))
       (OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q6.2)
  · unfold chain
    exact ⟨OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q7.1,
     OwnPlusHost.rename_avoid _ _ _ (fix _ _ _ (by decide) (by decide)) q7.2⟩
  · exact q8

theorem hosted_logical (F:Program)(hF:wires F⊆OB5Support.segSites):wires (hosted F)⊆OB5Support.logicalSites:=by
  have mem(i:Nat)(hi:i∈OB5Support.logicalIndices):base i∈OB5Support.logicalSites:=logical_mem i hi
  have m511:base 511∈OB5Support.logicalSites:=mem 511 (by
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
      List.not_mem_nil,or_false];omega)
  have m1542:base 1542∈OB5Support.logicalSites:=mem 1542 (by
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
      List.not_mem_nil,or_false];omega)
  have x(r:Wire)(hr:r∈wires [Instr.X (base 511)]):r=base 511:=by
    simpa [wires,Instr.wires] using hr
  intro q hq
  simp only [hosted,wires_append,Finset.mem_union] at hq
  rcases hq with h|h|h
  · rw [x q h];exact m511
  · rw [renameProgram_support] at h
    obtain ⟨old,hold,rfl⟩:=Finset.mem_image.mp h
    have hs:=hF hold
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hs)
    unfold HostOB5.hostSwap
    split_ifs with c d e f
    · exact m511
    · exfalso
      have:=base_injective d
      subst this
      simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      omega
    · exact m1542
    · exfalso
      have:=base_injective f
      subst this
      simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      omega
    · apply mem
      have c':i≠2409:=fun h=>c (by rw [h])
      have e':i≠2410:=fun h=>e (by rw [h])
      simp only [OB5Support.segIndices,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
        List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      omega
  · rw [x q h];exact m511

theorem borrow_seg (P:Program)(hp:wires P⊆OB5Support.segSites):
    wires (renameProgram QSiteDirectControls.borrow P)⊆OB5Support.segSites:=by
  have mem(i:Nat)(hi:i=1540 ∨ i=2409):base i∈OB5Support.segSites:=by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
    omega
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=base 1540
  · subst w;simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_left] using mem 2409 (Or.inr rfl)
  · by_cases y:w=base 2409
    · subst w;simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_right] using mem 1540 (Or.inl rfl)
    · simpa only [QSiteDirectControls.borrow,Equiv.swap_apply_of_ne_of_ne x y] using hp used

theorem fieldE_seg:wires fieldE⊆OB5Support.segSites:=by
  simp only [fieldE,wires_append,Finset.union_subset_iff]
  exact ⟨QSiteDirectSupport.replay_support true,HalfFieldOB5Support.copy_support,
    borrow_seg _ OwnQ5Endpoint.support.2⟩

theorem fieldX_seg:wires fieldX⊆OB5Support.segSites:=by
  simp only [fieldX,wires_append,Finset.union_subset_iff]
  exact ⟨borrow_seg _ OwnQ5Endpoint.support.1,HalfFieldOB5Support.copy_support,
    QSiteDirectSupport.replay_support false⟩

theorem old_first_logical:wires Q5Global718.firstPhase⊆OB5Support.logicalSites ∧
    wires Q5Global718.lastPhase⊆OB5Support.logicalSites:=by
  have old:=KernelOB5.program_support_logical true
  rw [OwnQ5Integer.old_shape] at old
  simp only [wires_append,Finset.union_subset_iff] at old
  exact ⟨old.1.1,old.2⟩

theorem relocated_support (F:Program)(hF:wires F⊆OB5Support.logicalSites):
    wires (Q8FusionPhase.relocated F)⊆OB5Support.logicalSites:=by
  rw [relocated_shape]
  simp only [wires_append,Finset.union_subset_iff]
  exact ⟨chain_support _ old_first_logical.1,hF,chain_support _ old_first_logical.2⟩

theorem kernelE_support:wires kernelE⊆OB5Support.logicalSites:=
  relocated_support _ (hosted_logical _ fieldE_seg)
theorem kernelX_support:wires kernelX⊆OB5Support.logicalSites:=
  relocated_support _ (hosted_logical _ fieldX_seg)

theorem relocated_free (F:Program)(all:∀q,QSiteDirectFree.FinalBad q → base q∉wires F)
    (i:Nat)(hi:i∈[2312,766,765,767,1026,1541,1542,1540]):base i∉wires (Q8FusionPhase.relocated (hosted F)):=by
  have p:=phases_free i hi
  have bad:QSiteDirectFree.FinalBad i:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [QSiteDirectFree.FinalBad,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have ne:i≠511:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  have h:=QSiteDirectFree.hosted_free F all i bad ne
  rw [relocated_shape]
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨p.1,h,p.2⟩

theorem kernelE_free(i:Nat)(hi:i∈[2312,766,765,767,1026,1541,1542,1540]):base i∉wires kernelE:=by
  unfold kernelE
  exact relocated_free _ QSiteDirectFree.fieldE_free_all i hi
theorem kernelX_free(i:Nat)(hi:i∈[2312,766,765,767,1026,1541,1542,1540]):base i∉wires kernelX:=by
  unfold kernelX
  exact relocated_free _ QSiteDirectFree.fieldX_free_all i hi

theorem x_counts:toffoliCount [Instr.X (base 511)]=0 ∧ measurementCount [Instr.X (base 511)]=0:=⟨rfl,rfl⟩

end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalKernel


section QSiteFinalResources
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation BalancedField QSiteDirectFields
attribute [local irreducible] wires run toffoliCount measurementCount

theorem relocated_counts (F:Program):
    toffoliCount (Q8FusionPhase.relocated F)=toffoliCount (Q5FusionPhase.kernel F) ∧
    measurementCount (Q8FusionPhase.relocated F)=measurementCount (Q5FusionPhase.kernel F):=by
  have a:=Q8FusionPhase.relocated_counts F
  rw [Q8FusionPhase.old_shape] at a
  have b:=Q7FusionPhase.relocated_counts F
  rw [Q7FusionPhase.old_shape] at b
  have c:=Q6FusionPhase.relocated_counts F
  rw [shape6] at c
  have d:=Q5FusionPhase.relocated_counts F
  exact ⟨a.1.trans (b.1.trans (c.1.trans d.1)),a.2.trans (b.2.trans (c.2.trans d.2))⟩

theorem kernelE_counts:toffoliCount kernelE=1047600 ∧ measurementCount kernelE=719492:=by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have k:=EntryFuse.kernel5_counts
  have r:=QSiteDirectReplay.replay_counts true cfg.1 (cfg.2.1 _ (by simp))
  have o:=OneBankReplay5.replay_counts true cfg.1 (cfg.2.1 _ (by simp))
  have e:=relocated_counts (hosted fieldE)
  have x:=x_counts
  have rn:=renameProgram_counts HostOB5.hostSwap fieldE
  have ro:=renameProgram_counts HostOB5.hostSwap EntryFuse.field5
  have bc:=renameProgram_counts QSiteDirectControls.borrow OwnQ5Endpoint.canonT
  simp only [EntryFuse.kernel5,EntryFuse.hostField5,toffoliCount_append,measurementCount_append,ro.1,ro.2,x.1,x.2] at k
  simp only [EntryFuse.field5,toffoliCount_append,measurementCount_append] at k
  simp only [kernelE,e.1,e.2]
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,hosted,toffoliCount_append,
    measurementCount_append,rn.1,rn.2,x.1,x.2]
  simp only [fieldE,QSiteDirectControls.canonical,toffoliCount_append,measurementCount_append,bc.1,bc.2]
  simp only [if_true] at r o
  constructor <;> omega

theorem kernelX_counts:toffoliCount kernelX=1047598 ∧ measurementCount kernelX=719747:=by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have k:=ExitFuse.exitKernel5_counts
  have r:=QSiteDirectReplay.replay_counts false cfg.1 (cfg.2.1 _ (by simp))
  have o:=OneBankReplay5.replay_counts false cfg.1 (cfg.2.1 _ (by simp))
  have e:=relocated_counts (hosted fieldX)
  have x:=x_counts
  have rn:=renameProgram_counts HostOB5.hostSwap fieldX
  have ro:=renameProgram_counts HostOB5.hostSwap ExitFuse.exitSegment5
  have bc:=renameProgram_counts QSiteDirectControls.borrow OwnQ5Endpoint.centerT
  simp only [ExitFuse.exitKernel5,ExitFuse.hostExitSegment5,toffoliCount_append,measurementCount_append,ro.1,ro.2,x.1,x.2] at k
  simp only [ExitFuse.exitSegment5,toffoliCount_append,measurementCount_append] at k
  simp only [kernelX,e.1,e.2]
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,hosted,toffoliCount_append,
    measurementCount_append,rn.1,rn.2,x.1,x.2]
  simp only [fieldX,QSiteDirectControls.center,toffoliCount_append,measurementCount_append,bc.1,bc.2]
  simp only [Bool.false_eq_true,if_false] at r o
  constructor <;> omega

theorem chain_physical (P:Program)(h:GatePhysical P):GatePhysical (chain P):=by
  unfold chain
  apply gatePhysical_rename _ (Equiv.injective _)
  apply gatePhysical_rename _ (Equiv.injective _)
  apply gatePhysical_rename _ (Equiv.injective _)
  exact gatePhysical_rename _ (Equiv.injective _) _ h

theorem relocated_physical (F:Program)(hF:GatePhysical F):GatePhysical (Q8FusionPhase.relocated F):=by
  have first:=(NativeFirstDirect.programs_physical base base_pool_nodup).1
  have last:=NativeFirstKnown.inverse_physical base base_pool_nodup
  rw [relocated_shape]
  simp only [gatePhysical_append]
  refine ⟨chain_physical _ ?_,hF,chain_physical _ ?_⟩
  · simp only [Q5Global718.firstPhase,gatePhysical_append]
    exact ⟨first,stackForwardT_physical,mappedClear_physical⟩
  · simp only [Q5Global718.lastPhase,gatePhysical_append]
    exact ⟨mappedClear_physical,stackReverseT_physical,last⟩

theorem hosted_physical (F:Program)(hF:GatePhysical F):GatePhysical (hosted F):=by
  have x:GatePhysical [Instr.X (base 511)]:=by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    subst hi
    trivial
  simp only [hosted,gatePhysical_append]
  exact ⟨x,gatePhysical_rename HostOB5.hostSwap HostOB5.hostSwap_injective _ hF,x⟩

theorem kernelE_physical:GatePhysical kernelE:=by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have ep:=OwnQ5Endpoint.endpoint_physical cfg.1
  apply relocated_physical
  apply hosted_physical
  simp only [fieldE,gatePhysical_append]
  exact ⟨QSiteDirectReplay.replay_physical true cfg.1 cfg.2.1 cfg.2.2,ep.2.2,
    gatePhysical_rename _ (Equiv.injective _) _ ep.2.1⟩

theorem kernelX_physical:GatePhysical kernelX:=by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have ep:=OwnQ5Endpoint.endpoint_physical cfg.1
  apply relocated_physical
  apply hosted_physical
  simp only [fieldX,gatePhysical_append]
  exact ⟨gatePhysical_rename _ (Equiv.injective _) _ ep.1,ep.2.2,
    QSiteDirectReplay.replay_physical false cfg.1 cfg.2.1 cfg.2.2⟩

theorem relocated_slots (F:Program)(hF:Challenge.gateSlots F≤14100000):
    Challenge.gateSlots (Q8FusionPhase.relocated (hosted F))≤20500006:=by
  have native:=Baselines.nativeFirst_gateSlots_le base
  have integer:=Stack5.slots_le base base_pool_nodup 1 511 (by omega)
  have f:=StackOB5.forward_counts.2.2
  have r:=StackOB5.reverse_counts.2.2
  have ft:=stackForwardT_metrics.2.2
  have rt:=stackReverseT_metrics.2.2
  have clear:Challenge.gateSlots (skywalkArithmeticClear base)=3:=by
    simp [skywalkArithmeticClear,skywalkTerminalClear,Challenge.gateSlots,Challenge.instructionSlots]
  have gx:Challenge.gateSlots [Instr.X (base 511)]=1:=rfl
  rw [relocated_shape]
  simp only [chain,hosted,Q5Global718.firstPhase,Q5Global718.lastPhase,Challenge.gateSlots_append,
    Baselines.rename_gateSlots,clear,gx]
  omega

theorem kernelE_slots:Challenge.gateSlots kernelE≤20500006:=by
  apply relocated_slots
  have c:=OwnQ5Endpoint.endpoint_gateSlots_le
  have r:=QSiteDirectReplay.replay_gateSlots_le true
  simp only [fieldE,QSiteDirectControls.canonical,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  omega

theorem kernelX_slots:Challenge.gateSlots kernelX≤20500006:=by
  apply relocated_slots
  have c:=OwnQ5Endpoint.endpoint_gateSlots_le
  have r:=QSiteDirectReplay.replay_gateSlots_le false
  simp only [fieldX,QSiteDirectControls.center,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  omega

end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalResources


section QSiteFinalPlaced
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog CompressedAllocation
  CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse QSiteDirectFields LaneA
attribute [local irreducible] run wires kernelE kernelX toffoliCount measurementCount

def arithE (L:ControlledPointLayout):Program:=renameProgram (wireFn2 L) kernelE
def arithX (L:ControlledPointLayout):Program:=renameProgram (wireFn2 L) kernelX

theorem slot_mem_logical (i:Nat)(hi:i∈OB5Support.logicalIndices):base i∈slots.toFinset:=
  ArithmeticOB5.logical_sub_old (logical_mem i hi)

theorem divisor_slots:(wireBlock base 770 256).toFinset⊆slots.toFinset:=by
  intro q hq
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hq)
  simp only [List.mem_range'_1] at hi
  apply slot_mem_logical
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem numerator_slots:(wireBlock base 2056 256).toFinset⊆slots.toFinset:=by
  intro q hq
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hq)
  simp only [List.mem_range'_1] at hi
  apply slot_mem_logical
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  omega

theorem control_slot:base 2400∈slots.toFinset:=by
  apply slot_mem_logical
  simp [OB5Support.logicalIndices]

theorem kernelE_strong
    (hn:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (ho:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x:Nat)(Y:Fp)(hx0:0<x)(hx:x<p)(s t:State)(m:List Bool)
    (hin:SkywalkArithmeticInput base x Y.val s.basis)(hg:s.basis (base 2409)=false)(hs:s.basis (base 2410)=false)
    (phase:t.phase=s.phase)(same:∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value:regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)):
    (run kernelE m t).phase=s.phase ∧ regValue (wireBlock base 2056 256) (run kernelE m t).basis=
      (skywalkArithmeticResult true x Y).val ∧ ∀q,q∉wireBlock base 2056 256 → (run kernelE m t).basis q=s.basis q:=
  kernelE_correct QSiteDirectFree.raw_away.1 QSiteDirectFree.fields_free.1 hn hlo ho hf x Y hx0 hx s t m hin hg hs phase same value

theorem entryTransfer (L:ControlledPointLayout)(f:Wire → Wire)(domain:Finset Wire)
    (injective:∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap:(wireBlock base 770 256).map f=L.point.x)
    (numeratorMap:(wireBlock base 2056 256).map f=L.point.y)
    (sharedWork:∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG:f (base 2409)∈L.dialogPool)(selectorS:f (base 2410)∈L.dialogPool)
    (dxSites:(wireBlock base 770 256).toFinset⊆domain)
    (dySites:(wireBlock base 2056 256).toFinset⊆domain)
    (P:Program)(sites:wires P⊆domain)
    (X:Nat)(Y:Fp)
    (strongP:∀(s t:State)(m:List Bool),SkywalkArithmeticInput base X Y.val s.basis →
      s.basis (base 2409)=false → s.basis (base 2410)=false → t.phase=s.phase →
      (∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q) →
      regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2) →
      (run P m t).phase=s.phase ∧ regValue (wireBlock base 2056 256) (run P m t).basis=
        (skywalkArithmeticResult true X Y).val ∧ ∀q,q∉wireBlock base 2056 256 → (run P m t).basis q=s.basis q)
    (s t:State)(m:List Bool)
    (hx:regValue L.point.x s.basis=X)(hy:regValue L.point.y s.basis=Y.val)
    (clean:regValue L.dialogPool s.basis=0)(phase:t.phase=s.phase)
    (same:∀q,q∉L.point.y → t.basis q=s.basis q)
    (half:regValue L.point.y t.basis=centerWord (Y/2)):
    (run (renameProgram f P) m t).phase=s.phase ∧ regValue L.point.y (run (renameProgram f P) m t).basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → (run (renameProgram f P) m t).basis q=s.basis q:=by
  let a:=laneLogicalInput domain f s
  let b:=laneLogicalInput domain f t
  have aBits(q:Wire)(hq:q∈domain):a.basis q=s.basis (f q):=by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits(q:Wire)(hq:q∈domain):b.basis q=t.basis (f q):=by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero(q:Wire)(hq:f q∈L.dialogPool):a.basis q=false:=by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input:SkywalkArithmeticInput base X Y.val a.basis:=by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [selRegMap f _ a.basis s.basis (fun q hq=>aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [selRegMap f _ a.basis s.basis (fun q hq=>aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used:q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside(q:Wire)(hq:q∈domain)(haway:q∉wireBlock base 2056 256):f q∉L.point.y:=by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩:=List.mem_map.mp bad
    have eq:q=r:=injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired:∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q:=by
    intro q hq
    by_cases used:q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical:regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2):=by
    rw [selRegMap f _ b.basis t.basis (fun q hq=>bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases:b.phase=a.phase:=by change t.phase=s.phase;exact phase
  have strong:=strongP a b m input (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer:=run_rename_pool f domain injective P sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (selRegMap f _ (run P m b).basis
      (run (renameProgram f P) m t).basis
      (fun q hq=>(transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image:q∈domain.image f
    · obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp image
      have away:r∉wireBlock base 2056 256:=by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain P sites m t q image).trans (same q hq)

theorem arithE_correct (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (logicalND:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (logicalAway:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X:Nat)(Y:Fp)(hX0:0<X)(hX:X<p)(s t:State)(m:List Bool)
    (hx:regValue L.point.x s.basis=X)(hy:regValue L.point.y s.basis=Y.val)
    (clean:regValue L.dialogPool s.basis=0)(phase:t.phase=s.phase)
    (same:∀q,q∉L.point.y → t.basis q=s.basis q)
    (half:regValue L.point.y t.basis=centerWord (Y/2)):
    (run (arithE L) m t).phase=s.phase ∧ regValue L.point.y (run (arithE L) m t).basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → (run (arithE L) m t).basis q=s.basis q:=by
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,selectorG,selectorS,_⟩
  exact entryTransfer L (wireFn2 L) slots.toFinset injective divisorMap numeratorMap sharedWork selectorG selectorS
    divisor_slots numerator_slots kernelE (kernelE_support.trans ArithmeticOB5.logical_sub_old) X Y
    (fun a b r h1 h2 h3 h4 h5 h6=>kernelE_strong logicalND hlo logicalAway logicalReplay X Y hX0 hX a b r h1 h2 h3 h4 h5 h6)
    s t m hx hy clean phase same half

theorem arithE_eq (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (logicalND:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (logicalAway:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X:Nat)(Y:Fp)(hX0:0<X)(hX:X<p)(s t:State)(m:List Bool)
    (hx:regValue L.point.x s.basis=X)(hy:regValue L.point.y s.basis=Y.val)
    (clean:regValue L.dialogPool s.basis=0)(phase:t.phase=s.phase)
    (same:∀q,q∉L.point.y → t.basis q=s.basis q)
    (half:regValue L.point.y t.basis=centerWord (Y/2)):
    run (arithE L) m t=run (arithS L false) [] s:=by
  have newer:=arithE_correct L hw hn logicalND hlo logicalAway logicalReplay X Y hX0 hX s t m hx hy clean phase same half
  have older:=arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue:regValue L.point.y (run (arithE L) m t).basis=
      regValue L.point.y (run (arithS L false) [] s).basis:=by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq:q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

theorem arithX_correct (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (X:Nat)(Y:Fp)(B:Bool)(hX0:0<X)(hX:X<p)
    (s:State)(m:List Bool)(hb:s.basis L.core.generic=B)
    (hx:regValue L.point.x s.basis=X)(hy:regValue L.point.y s.basis=Y.val)
    (clean:regValue L.dialogPool s.basis=0):
    let out:=run (arithX L) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=centerWord (skywalkArithmeticResult false X Y/2) ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q:=by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  have cfg:=LaneA.laneLogical_config
  have above:History5.HistoryAbove base:=by intro j hj;simp [base]
  exact exitTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_slots numerator_slots control_slot
    kernelX (kernelX_support.trans ArithmeticOB5.logical_sub_old) cfg.1 above cfg.2.1 cfg.2.2
    X Y B hX0 hX (fun a records input hg hs=>by
      have h:=kernelX_correct QSiteDirectFree.raw_away.2 QSiteDirectFree.fields_free.2 cfg.1 above cfg.2.1 cfg.2.2
        X Y hX0 hX a records input hg hs
      simpa only [skywalkArithmeticResult,Bool.false_eq_true,if_false] using h)
    s m hb hx hy clean

theorem arithX_pair (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (D:Nat)(Y:Fp)(G:Bool)(positive:0<D)(bound:D<p)
    (fixed a c:State)(records:List Bool)
    (fixedG:fixed.basis L.core.generic=G)(fixedX:regValue L.point.x fixed.basis=D)
    (fixedY:regValue L.point.y fixed.basis=Y.val)(fixedClean:regValue L.dialogPool fixed.basis=0)
    (ha:run (arithX L) records fixed=a)(hc:run (arithS L true) [] fixed=c):
    a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord (skywalkArithmeticResult false D Y/2) ∧
      ∀q,q∉L.point.y → a.basis q=c.basis q:=by
  have newer:=arithX_correct L hw hn D Y G positive bound fixed records fixedG fixedX fixedY fixedClean
  have older:=arithS_correct L hw hn true D Y.val bound positive Y.isLt fixed [] fixedX fixedY fixedClean
  rw [ha] at newer
  rw [hc] at older
  exact ⟨newer.1.trans older.1.symm,newer.2.1,fun q hq=>(newer.2.2 q hq).trans (older.2.2 q hq).symm⟩

def divisionQ (L:ControlledPointLayout)(k:Fp):Program:=fusedY L k++arithE L
def exitQ (L:ControlledPointLayout)(cx cy:Fp):Program:=arithX L++(fastConstNeg L cx++fusedExitY L cy)

section Steps
attribute [local irreducible] arithE arithX arithS fusedY fastConstAdd fastConstNeg fusedExitY

theorem divisionQ_step (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (logicalND:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
    (logicalAway:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X Y k:Fp)(G:Bool)(origin:BasisState)(hX:X≠0):
    Triple (PointDialogValues L X Y G origin) (divisionQ L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin):=by
  intro s m v
  let Z:Fp:=Y+(if G then k else 0)
  let n:=measurementCount (fusedY L k)
  let a:=run (fusedY L k) (m.take n) s
  let c:=run (fastConstAdd L L.point.y k) [] s
  have oldAdd:=fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep:=fastStep_addY L hw hn X Y G origin k s [] v
  have canonical:PointDialogValues L X Z G origin c.basis:=oldStep.2
  have fused:=fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase:a.phase=c.phase:=fused.1.trans oldAdd.1.symm
  have same(q:Wire)(hq:q∉L.point.y):a.basis q=c.basis q:=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half:regValue L.point.y a.basis=centerWord (Z/2):=by
    simpa only [v.generic,Z] using fused.2.1
  have hp:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have equal:=arithE_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z hp X.isLt
    c a (m.drop n) canonical.x canonical.y canonical.clean phase same half
  have eqProgram:run (divisionQ L k) m s=run (arithS L false) [] c:=by
    simp only [divisionQ,run_append]
    change run (arithE L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old:=arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

theorem exitQ_step (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (X Y cx cy:Fp)(G:Bool)(origin:BasisState)(hX:X≠0):
    Triple (PointDialogValues L X Y G origin) (exitQ L cx cy)
      (PointDialogValues L (if G then cx-X else X) (Y*X-(if G then cy else 0)) G origin):=by
  have hXpos:0<X.val:=Nat.pos_of_ne_zero (fun hz=>hX ((ZMod.val_eq_zero X).mp hz))
  have old:=arith3F_step L hw hn X Y G origin true hX
  have pair:∀(s:State)(m:List Bool),PointDialogValues L X Y G origin s.basis →
      let a:=run (arithX L) m s
      let c:=run (arithS L true) [] s
      a.phase=c.phase ∧ regValue L.point.y a.basis=centerWord ((Y*X)/2) ∧
        ∀q,q∉L.point.y → a.basis q=c.basis q:=by
    intro s m v
    have p:=arithX_pair L hw hn X.val Y G hXpos X.isLt s _ _ m
      v.generic v.x v.y v.clean rfl rfl
    simpa only [skywalkArithmeticResult,Bool.false_eq_true,if_false,ZMod.natCast_zmod_val] using p
  have h:=exitCompose_genericZ L hw hn (arithX L) (arithS L true)
    X Y (Y*X) cx cy G origin (by simpa only [if_true] using old) pair
  simpa only [exitQ] using h
end Steps

end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalPlaced


section QSiteFinalSquare
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

theorem resident_away (L:ControlledPointLayout)(hn:L.wires.Nodup)
    (q:Wire)(hq:q∈CompressedPointSquare.residents L):q∉L.dialogPool:=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (n:Nat)(hN:n=1537 ∨ n=1538 ∨ n=1539):
    L.core.poolWire n∉wires (OwnDiagAll12Placed.initial L):=by
  have hb:n<2613:=by omega
  rw [OwnDiagAll12Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n hb)
  · have away:=resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n hb)
  · have away:=resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n hb)
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) hb e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) hb e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem swap_pool_fix (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (a b n:Nat)(ha:a<2613)(hb:b<2613)(hnn:n<2613)(hna:n≠a)(hnb:n≠b):
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n:=by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem current_spare_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (n:Nat)(hN:n=1537 ∨ n=1538 ∨ n=1539):
    L.core.poolWire n∉wires (OwnDiagAll12Placed.program L):=by
  have hb:n<2613:=by omega
  have p:L.core.poolWire n∉wires (OwnDiagAll12Placed.plus L):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn 766 1530 n (by omega) (by omega) hb (by omega) (by omega))
      (original_spare_free L hw hn n hN)
  have g:L.core.poolWire n∉wires (OwnDiagAll12Placed.guard L):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn 765 1531 n (by omega) (by omega) hb (by omega) (by omega)) p
  have q:L.core.poolWire n∉wires (OwnDiagAll12Placed.minus L):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn 767 1532 n (by omega) (by omega) hb (by omega) (by omega)) g
  have r:L.core.poolWire n∉wires (OwnDiagAll12Placed.program L):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn 770 1536 n (by omega) (by omega) hb (by omega) (by omega)) q
  exact r

def poolSwap (L:ControlledPointLayout)(a b:Nat):Equiv.Perm Wire:=
  Equiv.swap (L.core.poolWire a) (L.core.poolWire b)

def squareQ (L:ControlledPointLayout):Program:=
  renameProgram (poolSwap L 1286 1539) (renameProgram (poolSwap L 1285 1537)
    (renameProgram (poolSwap L 1284 1538) (OwnDiagAll12Placed.program L)))

abbrev SquareT (L:ControlledPointLayout)(P:Program):Prop:=
  ∀(X Y:Fp)(G:Bool)(baseState:BasisState),
    Triple (PointDialogValues L X Y G baseState) P
      (PointDialogValues L (X-(if G then Y*Y-(OwnDiagAll12Square.sqOff:Fp) else 0)) Y G baseState)

theorem poolSwap_relabel (L:ControlledPointLayout)(hw:L.Widths)(a b:Nat)(ha:a<2613)(hb:b<2613)
    (P:Program)(hP:SquareT L P):SquareT L (renameProgram (poolSwap L a b) P):=by
  intro X Y G baseState s m v
  have old:=hP X Y G baseState s m v
  have pool:∀q∈L.dialogPool,poolSwap L a b q∈L.dialogPool:=by
    intro q hq
    by_cases x:q=L.core.poolWire a
    · subst q;simpa only [poolSwap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw b hb
    · by_cases y:q=L.core.poolWire b
      · subst q;simpa only [poolSwap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw a ha
      · simpa only [poolSwap,Equiv.swap_apply_of_ne_of_ne x y] using hq
  have outside:∀q,q∉L.dialogPool → poolSwap L a b q=q:=by
    intro q hq
    have x:q≠L.core.poolWire a:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw a ha)
    have y:q≠L.core.poolWire b:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw b hb)
    exact Equiv.swap_apply_of_ne_of_ne x y
  have eq:=Square5Placement.pool_relabel_state_eq L (poolSwap L a b) pool outside P s m v.clean old.2.clean
  change _ ∧ _
  rw [eq]
  exact old

theorem squareQ_step (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup):SquareT L (squareQ L):=by
  apply poolSwap_relabel L hw 1286 1539 (by omega) (by omega)
  apply poolSwap_relabel L hw 1285 1537 (by omega) (by omega)
  apply poolSwap_relabel L hw 1284 1538 (by omega) (by omega)
  have h:=OwnDiagAll12Placed.correct L hw hn
  intro X Y G origin
  have v:=h X Y G origin
  have e : X-(if G then Y*Y else 0)+(if G then (OwnDiagAll12Square.sqOff:Fp) else 0)=
      X-(if G then Y*Y-(OwnDiagAll12Square.sqOff:Fp) else 0) := by
    cases G <;> simp <;> ring
  simpa only [e] using v


theorem squareQ_counts (L:ControlledPointLayout):
    toffoliCount (squareQ L)=toffoliCount (OwnDiagAll12Placed.program L) ∧
    measurementCount (squareQ L)=measurementCount (OwnDiagAll12Placed.program L):=by
  have a:=renameProgram_counts (poolSwap L 1286 1539) (renameProgram (poolSwap L 1285 1537)
    (renameProgram (poolSwap L 1284 1538) (OwnDiagAll12Placed.program L)))
  have b:=renameProgram_counts (poolSwap L 1285 1537) (renameProgram (poolSwap L 1284 1538) (OwnDiagAll12Placed.program L))
  have c:=renameProgram_counts (poolSwap L 1284 1538) (OwnDiagAll12Placed.program L)
  exact ⟨a.1.trans (b.1.trans c.1),a.2.trans (b.2.trans c.2)⟩

theorem squareQ_physical (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup):GatePhysical (squareQ L):=by
  apply gatePhysical_rename _ (Equiv.injective _)
  apply gatePhysical_rename _ (Equiv.injective _)
  exact gatePhysical_rename _ (Equiv.injective _) _ (OwnDiagAll12Placed.physical L hw hn)

theorem squareQ_slots (L:ControlledPointLayout)(hw:L.Widths):Challenge.gateSlots (squareQ L)≤8000000:=by
  simp only [squareQ,Baselines.rename_gateSlots]
  exact OwnDiagAll12Placed.slots L hw

theorem poolSwap_support (L:ControlledPointLayout)(a b:Nat)(S:Finset Wire)
    (old:Program)(hold:wires old⊆S)(ha:L.core.poolWire a∈S)(hb:L.core.poolWire b∈S):
    wires (renameProgram (poolSwap L a b) old)⊆S:=by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=L.core.poolWire a
  · subst w;simpa only [poolSwap,Equiv.swap_apply_left] using hb
  · by_cases y:w=L.core.poolWire b
    · subst w;simpa only [poolSwap,Equiv.swap_apply_right] using ha
    · simpa only [poolSwap,Equiv.swap_apply_of_ne_of_ne x y] using hold used

theorem squareQ_support (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup):
    wires (squareQ L)⊆(OB5Support.sites L).toFinset:=by
  have mem(i:Nat)(hi:1284≤ i ∧ i<1541):L.core.poolWire i∈(OB5Support.sites L).toFinset:=
    List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L i (Or.inr (Or.inr (Or.inl hi)))))
  apply poolSwap_support L 1286 1539 _ _ _ (mem _ (by omega)) (mem _ (by omega))
  apply poolSwap_support L 1285 1537 _ _ _ (mem _ (by omega)) (mem _ (by omega))
  exact poolSwap_support L 1284 1538 _ _ (OwnDiagAll12Placed.support L hw hn) (mem _ (by omega)) (mem _ (by omega))

theorem swap_target_free (L:ControlledPointLayout)(a b:Nat)(P:Program)(h:L.core.poolWire b∉wires P):
    L.core.poolWire a∉wires (renameProgram (poolSwap L a b) P):=by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back:poolSwap L a b (L.core.poolWire b)=L.core.poolWire a:=Equiv.swap_apply_right _ _
  have same:old=L.core.poolWire b:=(poolSwap L a b).injective (e.trans back.symm)
  exact h (same ▸ used)

theorem squareQ_new_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (k:Nat)(hk:k∈[1284,1285,1286]):L.core.poolWire k∉wires (squareQ L):=by
  have spare (n:Nat)(hN:n=1537 ∨ n=1538 ∨ n=1539):=current_spare_free L hw hn n hN
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  have mid(a b n:Nat)(h1:a<2613)(h2:b<2613)(h3:n<2613)(h4:n≠a)(h5:n≠b)(P:Program)(hP:L.core.poolWire n∉wires P):
      L.core.poolWire n∉wires (renameProgram (poolSwap L a b) P):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn a b n h1 h2 h3 h4 h5) hP
  unfold squareQ
  rcases hk with rfl|rfl|rfl
  · apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    exact swap_target_free L _ _ _ (spare 1538 (by omega))
  · apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    apply swap_target_free
    apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    exact spare 1537 (by omega)
  · apply swap_target_free
    apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    apply mid _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    exact spare 1539 (by omega)

end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalSquare


section QSiteFinalGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite FiniteHostStack FiniteHostFusion FiniteHostFive
attribute [local irreducible] wires

 def wrapG (L : ControlledPointLayout) (G : Program) : Program :=
  zrep L ++ (clrF L ++ renameProgram (swapF L) G ++ clrF L) ++ zrep L
 theorem finite_not_G (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (G : Program) (hG : wires G⊆(OB5Support.sites L).toFinset) : L.point.finite∉wires G :=
  fun h => fin_not_sites L hw hn (List.mem_toFinset.mp (hG h))
section Geometry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem wrapG_sites (G : Program) (hG : wires G⊆(OB5Support.sites L).toFinset) : wires (wrapG L G) ⊆ (OB5Support.genericSites L).toFinset := by
  have pt (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) :
      q ∈ (OB5Support.genericSites L).toFinset :=
    List.mem_toFinset.mpr (by simp [OB5Support.genericSites, hq])
  have z : wires (zrep L) ⊆ (OB5Support.genericSites L).toFinset := by
    intro q hq
    rcases zrep_wires L q hq with rfl | h
    · exact pt _ (by simp [PointAddLayout.pointWires])
    · exact pt _ (by simp [PointAddLayout.pointWires, h])
  have c : wires (clrF L) ⊆ (OB5Support.genericSites L).toFinset := by
    intro q hq
    rcases clrF_wires L hw q hq with rfl | h | h
    · exact pt _ (by simp [PointAddLayout.pointWires])
    · exact pt _ (by simp [PointAddLayout.pointWires, h])
    · exact OB5Support.raw_sub_generic L (List.mem_toFinset.mpr (finLow_sites L hw 255 (by omega) q h))
  have r : wires (renameProgram (swapF L) (G)) ⊆
      (OB5Support.genericSites L).toFinset := by
    rw [renameProgram_support]
    intro q hq
    obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
    have hf : old ≠ L.point.finite := fun e => finite_not_G L hw hn G hG (e ▸ used)
    by_cases hs : old = finSpare L
    · rw [hs, show swapF L (finSpare L) = L.point.finite by simp [swapF, finSpare_ne L hw hn]]
      exact pt _ (by simp [PointAddLayout.pointWires])
    · rw [swapF_fix L old hf hs]
      exact OB5Support.raw_sub_generic L (hG used)
  simp only [wrapG, wires_append, Finset.union_subset_iff]
  exact ⟨⟨z, ⟨c, r⟩, c⟩, z⟩


theorem spare_not_wrapG (G : Program) (hG : wires G⊆(OB5Support.sites L).toFinset) : finSpare L ∉ wires (wrapG L G) := by
  have sne := finSpare_ne L hw hn
  have spool := finSpare_pool L hw
  have sx : finSpare L ∉ L.point.x := fun h => finPool_not_xy L hn _ spool (List.mem_append_left _ h)
  have slow : finSpare L ∉ L.dialogPool.take 255 := by
    rw [pool_block L hw 255 (by omega)]
    intro h
    obtain ⟨i, hi, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hi
    have := pool_inj L hw hn i 1400 (by omega) (by omega) e
    omega
  have z : finSpare L ∉ wires (zrep L) := by
    intro h; rcases zrep_wires L _ h with e | e
    · exact sne e
    · exact sx e
  have c : finSpare L ∉ wires (clrF L) := by
    intro h; rcases clrF_wires L hw _ h with e | e | e
    · exact sne e
    · exact sx e
    · exact slow e
  have r : finSpare L ∉ wires (renameProgram (swapF L) (G)) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨old, used, e⟩ := Finset.mem_image.mp h
    have : old = L.point.finite := by
      have := congrArg (swapF L) e
      rwa [swapF_invol L hw hn, show swapF L (finSpare L) = L.point.finite by
        simp [swapF, sne]] at this
    exact finite_not_G L hw hn G hG (this ▸ used)
  simp only [wrapG, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨z, ⟨c, r⟩, c⟩, z⟩



end Geometry
theorem wrapG_avoid_of_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : 515≤k ∧ k<2613) (hne : k≠1400) (G : Program)
    (old : L.core.poolWire k∉wires (G)) :
    L.core.poolWire k∉wires (wrapG L G) := by
  let q := L.core.poolWire k
  have nf : q≠L.point.finite := Ne.symm (finRes_ne L hw hn k hk.2 _ (by simp [PointAddLayout.pointWires]))
  have nx : q∉L.point.x := by
    intro h
    have member : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags := by
      simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    exact finRes_ne L hw hn k hk.2 q member rfl
  have nl : q∉L.dialogPool.take 255 := by
    intro h
    exact finLow_ne L hw hn k hk q 255 (by omega) h rfl
  have ns : q≠finSpare L := by
    intro h
    have eq : k=1400 := pool_inj L hw hn k 1400 hk.2 (by omega) h
    exact hne eq
  have fixed : swapF L q=q := swapF_fix L q nf ns
  have z : q∉wires (zrep L) := by
    intro h
    rcases zrep_wires L _ h with h|h
    · exact nf h
    · exact nx h
  have c : q∉wires (clrF L) := by
    intro h
    rcases clrF_wires L hw _ h with h|h|h
    · exact nf h
    · exact nx h
    · exact nl h
  have fast : q∉wires (G) := old
  have renamed : q∉wires (renameProgram (swapF L) (G)) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp h
    have back := congrArg (swapF L) eq
    rw [swapF_invol L hw hn,fixed] at back
    exact fast (back ▸ ha)
  simp only [wrapG,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨z,⟨c,renamed⟩,c⟩,z⟩

theorem wrapG_noDouble (G : Program) (hG : wires G⊆(OB5Support.sites layout).toFinset) : layout.doubleSelect∉wires (wrapG layout G) := by
  intro h
  have use := List.mem_toFinset.mp (wrapG_sites layout layout_widths layout_nodup G hG h)
  simp only [OB5Support.genericSites,List.mem_append,List.mem_singleton] at use
  rcases use with (p|g)|pl
  · have used := List.nodup_iff_count.mp (layout.dialogUsed_nodup layout_nodup) layout.doubleSelect
    have a := List.count_pos_iff.mpr p
    have c : 0 < List.count layout.doubleSelect layout.inPlaceFlags :=
      List.count_pos_iff.mpr (by simp [inPlaceFlags])
    simp only [dialogUsedWires,List.count_append] at used
    omega
  · exact absurd g (by decide)
  · obtain ⟨i,hi,eq⟩ := OB5Support.pool_index layout _ pl
    exact finRes_ne layout layout_widths layout_nodup i (by omega) _
      (finRes_flag layout _ (by simp [inPlaceFlags])) eq


end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalGeometry


section QSiteFinalGeneric
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite

def genericQ (L:ControlledPointLayout)(cx cy:Fp):Program:=
  fastConstAdd L L.point.x (-cx)++divisionQ L (-cy)++
  squareQ L++fastConstAdd L L.point.x (3*cx-(OwnDiagAll12Square.sqOff:Fp))++exitQ L cx cy

section Correct
variable (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
variable (logicalND:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
variable (logicalAway:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
variable (logicalReplay:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
  (mixedTranscriptTape base))
include hw hn logicalND hlo logicalAway logicalReplay
attribute [local irreducible] run arithS squareQ fastConstAdd fastConstNeg divisionQ exitQ

theorem genericQ_true (X Y cx cy:Fp)(origin:BasisState)(hX:X≠cx)
    (hd:cx-genericX X Y cx cy≠0):
    Triple (PointDialogValues L X Y true origin) (genericQ L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin):=by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have h1:=fastStep_addX L hw hn X Y true origin (-cx)
  simp only [if_true,←sub_eq_add_neg] at h1
  have h2:=divisionQ_step L hw hn logicalND hlo logicalAway logicalReplay
    (X-cx) Y (-cy) true origin (sub_ne_zero.mpr hX)
  have ha:(Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at h2
  have h3:=squareQ_step L hw hn (X-cx) a true origin
  simp only [if_true] at h3
  have h4:=fastStep_addX L hw hn ((X-cx)-(a*a-(OwnDiagAll12Square.sqOff:Fp))) a true origin (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  simp only [if_true] at h4
  have hd4:(X-cx)-(a*a-(OwnDiagAll12Square.sqOff:Fp))+(3*cx-(OwnDiagAll12Square.sqOff:Fp))=d:=by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e];ring
  rw [hd4] at h4
  have h5:=exitQ_step L hw hn d a cx cy true origin hd
  simp only [if_true] at h5
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at h5
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h5
  have h:=((((h1.seq h2).seq h3).seq h4).seq h5)
  simpa only [genericQ,List.append_assoc] using h

theorem genericQ_false (X Y cx cy:Fp)(origin:BasisState)(hX:X≠0):
    Triple (PointDialogValues L X Y false origin) (genericQ L cx cy)
      (PointDialogValues L X Y false origin):=by
  have h1:=fastStep_addX L hw hn X Y false origin (-cx)
  have h2:=divisionQ_step L hw hn logicalND hlo logicalAway logicalReplay
    X Y (-cy) false origin hX
  have h3:=squareQ_step L hw hn X (Y/X) false origin
  have h4:=fastStep_addX L hw hn X (Y/X) false origin (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  have h5:=exitQ_step L hw hn X (Y/X) cx cy false origin hX
  have back:Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5
  rw [back] at h5
  have h:=((((h1.seq h2).seq h3).seq h4).seq h5)
  simpa only [genericQ,List.append_assoc] using h
end Correct

def midQ (L:ControlledPointLayout)(cx cy:Fp):Program:=
  clrF L++renameProgram (swapF L) (genericQ L cx cy)++clrF L

def genQ (L:ControlledPointLayout)(cx cy:Fp):Program:=
  zrep L++midQ L cx cy++zrep L

theorem genQ_shape (L:ControlledPointLayout)(cx cy:Fp):genQ L cx cy=wrapG L (genericQ L cx cy):=by
  simp only [genQ,midQ,wrapG]

section WrapCorrect
variable (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
include hw hn

theorem midQ_values (cx cy:Fp)(X Y X' Y':Fp)(G:Bool)(base:BasisState)(fin:Bool)
    (hP:∀base':BasisState,Triple (PointDialogValues L X Y G base') (genericQ L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf:base L.point.finite=fin)
    (h1:decide (X.val≠5)=fin)(h2:decide (X'.val≠5)=fin):
    Triple (PointDialogValues L X Y G base) (midQ L cx cy) (PointDialogValues L X' Y' G base):=by
  have c1:=clrF_step L hw hn X Y G base
  have hb2:(writeBit base L.point.finite (base L.point.finite ^^ decide (X.val≠5)))
      L.point.finite=false:=by
    simp [writeBit,hf,h1]
  have sw:=swapF_values L hw hn (genericQ L cx cy) X Y X' Y' G _ hP hb2
  have c2:=clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val≠5)))
  have hb3:writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val≠5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val≠5)))
        L.point.finite ^^ decide (X'.val≠5))=base:=by
    funext q
    by_cases hq:q=L.point.finite
    · subst hq;simp [writeBit,hf,h1,h2]
    · simp [writeBit,hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2

variable (logicalND:(skywalkSharedWires base).Nodup)(hlo:History5.HistoryAbove base)
variable (logicalAway:∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
variable (logicalReplay:MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
  (mixedTranscriptTape base))
include logicalND hlo logicalAway logicalReplay

theorem genQ_ok {cx cy:Fp}(hc:curve.toAffine.Nonsingular cx cy):GenericOK L hc (genQ L cx cy):=by
  intro R b f hg s m v
  have hp:=(point_holds _ _ _).mp v.point
  have hfinite:L.point.finite∉L.point.x++L.point.y:=finite_not_x L hn
  have outside(q:Wire)(hq:q∉PointAddLayout.pointWires L.point):q∉L.point.x++L.point.y:=by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen:s.basis L.core.generic=f L.core.generic:=v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG:f L.core.generic=false:=by
      cases h:f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values:PointDialogValues L 0 0 false s.basis s.basis:=
      ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _=>rfl⟩
    have hfin:s.basis L.point.finite=false:=hp.1
    have z1:=zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin,finFive_val];rfl)
    have mid:=midQ_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base'=>genericQ_false L hw hn logicalND hlo logicalAway logicalReplay 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2:=zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin,finFive_val];rfl)
    obtain ⟨phase,hv⟩:=((z1.seq mid).seq z2) s m values
    refine ⟨phase,?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
      (fun q hq=>hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin:s.basis L.point.finite=true:=hp.1
    have hx5:decide (x.val≠5)=true:=decide_eq_true (val_ne_five hr)
    cases hG:f L.core.generic with
    | false =>
      have values:PointDialogValues L x y false s.basis s.basis:=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _=>rfl⟩
      have z1:=zrep_step L hw hn x x y false s.basis (by rw [hfin];simp)
      have mid:=midQ_values L hw hn cx cy x y x y false s.basis true
        (fun base'=>genericQ_false L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2:=zrep_step L hw hn x x y false s.basis (by rw [hfin];simp)
      obtain ⟨phase,hv⟩:=((z1.seq mid).seq z2) s m values
      refine ⟨phase,?_⟩
      simp only [Bool.false_eq_true,if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
        (fun q hq=>hv.rest q (outside q hq))
    | true =>
      have he:=hg hG
      have den:=dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5:decide ((genericX x y cx cy).val≠5)=true:=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values:PointDialogValues L x y true s.basis s.basis:=
        ⟨hp.2.1,hp.2.2,hgen.trans hG,v.clean,fun _ _=>rfl⟩
      have z1:=zrep_step L hw hn x x y true s.basis (by rw [hfin];simp)
      have mid:=midQ_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base'=>genericQ_true L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2:=zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin];simp)
      obtain ⟨phase,hv⟩:=((z1.seq mid).seq z2) s m values
      refine ⟨phase,?_⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩)
        (fun q hq=>hv.rest q (outside q hq))

end WrapCorrect
end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalGeneric


section QSiteFinalInventory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
namespace ECDSAAdd.Entrant.QSiteFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite FiniteHostStack FiniteHostFusion FiniteHostFive EntryFuseQ5 QSiteDirectFields
attribute [local irreducible] wires toffoliCount measurementCount arithS arithEntryS arithExitS
  fastConstAdd fastConstNeg fusedY fusedExitY SquareOB5.program squareQ arithE arithX

/-! Physical omission list of the new inventory. -/
abbrev OmitG:List Nat:=[1800,766,765,767,770,1284,1285,1286]

theorem placed_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (P:Program)(hp:wires P⊆OB5Support.logicalSites)(i k:Nat)
    (hi:base i∈OB5Support.logicalSites)(hm:wireFn2 L (base i)=L.core.poolWire k)
    (free:base i∉wires P):L.core.poolWire k∉wires (renameProgram (wireFn2 L) P):=by
  rw [renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩:=Finset.mem_image.mp h
  have mapped:wireFn2 L old=wireFn2 L (base i):=by simpa only [hm] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

theorem kernel_placed_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (P:Program)(hp:wires P⊆OB5Support.logicalSites)
    (free:∀i∈[2312,766,765,767,1026,1541,1542,1540],base i∉wires P)
    (k:Nat)(hk:k∈OmitG):L.core.poolWire k∉wires (renameProgram (wireFn2 L) P):=by
  have logical(i:Nat)(hi:i∈[2312,766,765,767,1026,1541,1542,1540]):base i∈OB5Support.logicalSites:=by
    apply logical_mem
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free L hw hn P hp 2312 1800 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 766 766 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 765 765 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 767 767 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 1026 770 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 1540 1284 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 1541 1285 (logical _ (by simp)) (by rfl) (free _ (by simp))
  · exact placed_free L hw hn P hp 1542 1286 (logical _ (by simp)) (by rfl) (free _ (by simp))

theorem arithE_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(k:Nat)(hk:k∈OmitG):
    L.core.poolWire k∉wires (arithE L):=by
  unfold arithE
  exact kernel_placed_free L hw hn _ kernelE_support kernelE_free k hk
theorem arithX_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(k:Nat)(hk:k∈OmitG):
    L.core.poolWire k∉wires (arithX L):=by
  unfold arithX
  exact kernel_placed_free L hw hn _ kernelX_support kernelX_free k hk

theorem square_old_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (k:Nat)(hk:k∈[1800,766,765,767,770]):L.core.poolWire k∉wires (OwnDiagAll12Placed.program L):=by
  have old:=OwnDiagAll12PlacedQ6.square_free L hw hn k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢;tauto)
  intro used
  apply old
  rw [OwnDiagAll12PlacedQ6.program,renameProgram_support]
  refine Finset.mem_image.mpr ⟨L.core.poolWire k,used,?_⟩
  apply swap_pool_fix L hw hn 1285 1537 k (by omega) (by omega)
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hk;omega

theorem squareQ_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(k:Nat)(hk:k∈OmitG):
    L.core.poolWire k∉wires (squareQ L):=by
  by_cases high:k∈[1284,1285,1286]
  · exact squareQ_new_free L hw hn k high
  have low:k∈[1800,766,765,767,770]:=by
    simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk high ⊢
    omega
  have b:k<2613 ∧ k≠1286 ∧ k≠1539 ∧ k≠1285 ∧ k≠1537 ∧ k≠1284 ∧ k≠1538:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at low
    omega
  have mid(x y:Nat)(h1:x<2613)(h2:y<2613)(h4:k≠x)(h5:k≠y)(P:Program)(hP:L.core.poolWire k∉wires P):
      L.core.poolWire k∉wires (renameProgram (poolSwap L x y) P):=
    OwnPlusHost.rename_avoid _ _ _ (swap_pool_fix L hw hn x y k h1 h2 b.1 h4 h5) hP
  unfold squareQ
  apply mid _ _ (by omega) (by omega) b.2.1 b.2.2.1
  apply mid _ _ (by omega) (by omega) b.2.2.2.1 b.2.2.2.2.1
  apply mid _ _ (by omega) (by omega) b.2.2.2.2.2.1 b.2.2.2.2.2.2
  exact square_old_free L hw hn k low

theorem constant_ports_avoid_large (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)
    (k:Nat)(hk:515≤k ∧ k<2613)(r:List Wire)(hr:r=L.point.x ∨ r=L.point.y):
    L.core.poolWire k∉(L.core.generic::(L.recoveryConstant r).wires).toFinset:=by
  intro hq
  have pool:=L.recoveryConstant_pool hw r
  have inpool(h:(L.core.poolWire k)∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]):
      (L.core.poolWire k)∈L.dialogPool.take 515:=pool ▸ h
  have low(h:(L.core.poolWire k)∈L.dialogPool.take 515):False:=
    finLow_ne L hw hn k (by omega) (L.core.poolWire k) 515 (by omega) h rfl
  have hq':=List.mem_toFinset.mp hq
  have out:(L.recoveryConstant r).out=r:=rfl
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq'
  rw [out] at hq'
  rcases hq' with h|(((h|h)|h)|h|h|h)
  · exact finRes_ne L hw hn k (by omega) L.core.generic (by simp [inPlaceFlags]) h.symm
  · exact low (inpool (by simp [h]))
  · have resident:(L.core.poolWire k)∈PointAddLayout.pointWires L.point:=by
      rcases hr with rfl|rfl <;> simp [PointAddLayout.pointWires,h]
    exact finRes_ne L hw hn k (by omega) (L.core.poolWire k) (finRes_point L _ resident) rfl
  · exact low (inpool (by simp [h]))
  · exact low (inpool (by simp [h]))
  · exact low (inpool (by simp [h]))
  · exact low (inpool (by simp [h]))

theorem add_palette (L:ControlledPointLayout)(hw:L.Widths)(k:Fp):
    wires (fastConstAdd L L.point.x k)⊆(L.core.generic::(L.recoveryConstant L.point.x).wires).toFinset:=by
  simpa only [fastConstAdd] using FastConst.fastAdd_support
    (K:=L.recoveryConstant L.point.x) (g:=L.core.generic) SquareReduction.c k.val
    ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩
theorem neg_palette (L:ControlledPointLayout)(hw:L.Widths)(k:Fp):
    wires (fastConstNeg L k)⊆(L.core.generic::(L.recoveryConstant L.point.x).wires).toFinset:=by
  simpa only [fastConstNeg] using FastConst.fastNeg_support
    (K:=L.recoveryConstant L.point.x) (g:=L.core.generic) p k.val
    ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩

theorem genericQ_free (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(k:Nat)(hk:k∈OmitG)(cx cy:Fp):
    L.core.poolWire k∉wires (genericQ L cx cy):=by
  have bounds:515≤k ∧ k<2613:=by
    simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have x:=constant_ports_avoid_large L hw hn k bounds L.point.x (Or.inl rfl)
  have y:=constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [genericQ,divisionQ,exitQ,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨fun h=>x (add_palette L hw (-cx) h),⟨fun h=>y (fusedY_support L hw (-cy) h),arithE_free L hw hn k hk⟩⟩,
    squareQ_free L hw hn k hk⟩,fun h=>x (add_palette L hw _ h)⟩,
    ⟨arithX_free L hw hn k hk,⟨fun h=>x (neg_palette L hw cx h),fun h=>y (fusedExitY_support L hw cy h)⟩⟩⟩

theorem genericQ_sites (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(cx cy:Fp):
    wires (genericQ L cx cy)⊆(OB5Support.sites L).toFinset:=by
  have ca(k:Fp):=(add_palette L hw k).trans (finConst_sites L hw L.point.x (Or.inl rfl))
  have cn:=(neg_palette L hw cx).trans (finConst_sites L hw L.point.x (Or.inl rfl))
  have fy:=(fusedY_support L hw (-cy)).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  have ey:=(fusedExitY_support L hw cy).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  have ar:wires (arithE L)⊆(OB5Support.sites L).toFinset:=by
    unfold arithE
    exact OB5Support.placed_support_logical L hw _ kernelE_support
  have ax:wires (arithX L)⊆(OB5Support.sites L).toFinset:=by
    unfold arithX
    exact OB5Support.placed_support_logical L hw _ kernelX_support
  simp only [genericQ,divisionQ,exitQ,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨ca _,⟨fy,ar⟩⟩,squareQ_support L hw hn⟩,ca _⟩,⟨ax,⟨cn,ey⟩⟩⟩

theorem genericQ_physical (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(cx cy:Fp):
    GatePhysical (genericQ L cx cy):=by
  have ax(k:Fp):=FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c k.val
  have ng:=FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have fy:=fusedY_physical L hw hn (-cy)
  have ex:=fusedExitY_physical L hw hn cy
  have sq:=squareQ_physical L hw hn
  have di:GatePhysical (arithE L):=by
    unfold arithE
    apply gatePhysical_rename_support (wireFn2 L) kernelE
    · intro a ha b hb eq
      exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelE_support ha)) b
        (ArithmeticOB5.logical_sub_old (kernelE_support hb)) eq
    · exact kernelE_physical
  have mu:GatePhysical (arithX L):=by
    unfold arithX
    apply gatePhysical_rename_support (wireFn2 L) kernelX
    · intro a ha b hb eq
      exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelX_support ha)) b
        (ArithmeticOB5.logical_sub_old (kernelX_support hb)) eq
    · exact kernelX_physical
  simp only [genericQ,divisionQ,exitQ,fastConstAdd,fastConstNeg,gatePhysical_append]
  exact ⟨⟨⟨⟨ax _,⟨fy,di⟩⟩,sq⟩,ax _⟩,⟨mu,⟨ng,ex⟩⟩⟩

theorem genQ_physical (L:ControlledPointLayout)(hw:L.Widths)(hn:L.wires.Nodup)(cx cy:Fp):
    GatePhysical (genQ L cx cy):=by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have r:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (genericQ_physical L hw hn cx cy)
  simp only [genQ,midQ,gatePhysical_append]
  exact ⟨⟨z,⟨c,r⟩,c⟩,z⟩

theorem genericQ_slots (L:ControlledPointLayout)(hw:L.Widths)(cx cy:Fp):gateSlots (genericQ L cx cy)≤49300012:=by
  have ax(r:List Wire)(hr:r.length=256)(k:Fp):=
    FastConst.fastAdd_gateSlots_le (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw r hr)
  have ng:=FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a1:=ax L.point.x hw.inputX (-cx)
  have a3:=ax L.point.x hw.inputX (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  have fy:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement (-cy).val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  have ex:=exit_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement cy.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  have d:gateSlots (arithE L)≤20500006:=by
    simpa only [arithE,Baselines.rename_gateSlots] using kernelE_slots
  have e:gateSlots (arithX L)≤20500006:=by
    simpa only [arithX,Baselines.rename_gateSlots] using kernelX_slots
  have sq:=squareQ_slots L hw
  simp only [genericQ,divisionQ,exitQ,fusedY,fusedExitY,fastConstAdd,fastConstNeg,gateSlots_append]
  omega

theorem genQ_slots (L:ControlledPointLayout)(hw:L.Widths)(cx cy:Fp):gateSlots (genQ L cx cy)≤49306008:=by
  have z:=zrep_gateSlots_le L hw
  have c:=clrF_gateSlots_le L hw
  have f:=genericQ_slots L hw cx cy
  have rs:=rename_gateSlots (swapF L) (genericQ L cx cy)
  simp only [genQ,midQ,gateSlots_append,rs]
  omega

theorem kernelQS_numbers:toffoliCount EntryFuseQ5.kernelQS=1048108 ∧ measurementCount EntryFuseQ5.kernelQS=720767:=by
  have d:=OwnEntryFuseQ5.kernel5S_counts_diff
  have q:=OwnQ5SW.selKernelQ_sel true
  have qt:=q.tc
  have qm:=q.mc
  have c:=OwnQ5Actual.kernel_counts true
  simp only [OwnQ5Runtime.kernelS] at d
  simp only [if_true] at c
  change toffoliCount OwnEntryFuseQ5.kernel5S=1048108 ∧ measurementCount OwnEntryFuseQ5.kernel5S=720767
  constructor <;> omega

theorem exitKernelQS_numbers:toffoliCount ExitFuseQ5.exitKernelQS=1047852 ∧ measurementCount ExitFuseQ5.exitKernelQS=721023:=by
  have d:=ExitFuseQ5.exitKernelQS_counts_diff
  have q:=OwnQ5SW.selKernelQ_sel false
  have qt:=q.tc
  have qm:=q.mc
  have c:=OwnQ5Actual.kernel_counts false
  simp only [OwnQ5Runtime.kernelS] at d
  simp only [Bool.false_eq_true,if_false] at c
  constructor <;> omega

theorem genericQ_counts (L:ControlledPointLayout)(hw:L.Widths)(cx cy:Fp):
    toffoliCount (genericQ L cx cy)+2807=toffoliCount (genericBothF L cx cy) ∧
    measurementCount (genericQ L cx cy)+3809=measurementCount (genericBothF L cx cy):=by
  have k1:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  have k2:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(SquareAQ.offset:Fp))
  have sc:=squareQ_counts L
  have sn:=OwnDiagAll12Placed.counts L hw
  norm_num [OwnDiagLowK.lowkcost2,OwnDiagLowK.lowkcostTPair,OwnDiagLowK.lowkcostTMake,OwnDiagLowK.lowkcostTClear] at sn
  have so:=SquareOB5.counts L hw
  have s : toffoliCount (squareQ L)+2045=toffoliCount (SquareOB5.program L) ∧
      measurementCount (squareQ L)+1258=measurementCount (SquareOB5.program L) := by
    constructor <;> omega
  have ae:=renameProgram_counts (wireFn2 L) kernelE
  have ax:=renameProgram_counts (wireFn2 L) kernelX
  have oe:=renameProgram_counts (wireFn2 L) EntryFuseQ5.kernelQS
  have ox:=renameProgram_counts (wireFn2 L) ExitFuseQ5.exitKernelQS
  have ne:=kernelE_counts
  have nx:=kernelX_counts
  have qe:=kernelQS_numbers
  have qx:=exitKernelQS_numbers
  simp only [genericQ,genericBothF,divisionQ,exitQ,fusedDivisionF,fusedExitF,toffoliCount_append,measurementCount_append]
  simp only [arithE,arithX,arithEntryS,arithExitS,ae.1,ae.2,ax.1,ax.2,oe.1,oe.2,ox.1,ox.2,s.1,s.2]
  constructor <;> omega

theorem genQ_counts (L:ControlledPointLayout)(hw:L.Widths)(cx cy:Fp):
    toffoliCount (genQ L cx cy)+2807=toffoliCount (genBothF L cx cy) ∧
    measurementCount (genQ L cx cy)+3809=measurementCount (genBothF L cx cy):=by
  have g:=genericQ_counts L hw cx cy
  have r:=renameProgram_counts (swapF L) (genericQ L cx cy)
  have r0:=renameProgram_counts (swapF L) (genericBothF L cx cy)
  simp only [genQ,midQ,genBothF,midBothF,toffoliCount_append,measurementCount_append,r.1,r.2,r0.1,r0.2]
  constructor <;> omega

abbrev OmitAll:List Nat:=[1400,1800,766,765,767,1540,770,1284,1285,1286]

theorem omit_sites (k:Nat)(hk:k∈OmitAll):layout.core.poolWire k∈WrapperOB5.sites layout:=by
  simp only [OmitAll,List.mem_cons,List.not_mem_nil,or_false] at hk
  have block(i:Nat)(hi:718≤ i ∧ i<1029):layout.core.poolWire i∈WrapperOB5.sites layout:=by
    simp only [WrapperOB5.sites,List.mem_append,List.mem_singleton,wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inl (Or.inr ⟨i,by omega,rfl⟩))
  have high(i:Nat)(hi:1284≤ i ∧ i<1541):layout.core.poolWire i∈WrapperOB5.sites layout:=by
    simp only [WrapperOB5.sites,List.mem_append,List.mem_singleton,wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inr ⟨i,by omega,rfl⟩)
  have top:layout.core.poolWire 1800∈WrapperOB5.sites layout:=by
    simp only [WrapperOB5.sites,List.mem_append,List.mem_singleton]
    exact Or.inr trivial
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact high _ (by omega)
  · exact top
  · exact block _ (by omega)
  · exact block _ (by omega)
  · exact block _ (by omega)
  · exact high _ (by omega)
  · exact block _ (by omega)
  · exact high _ (by omega)
  · exact high _ (by omega)
  · exact high _ (by omega)

theorem ten_bound (P:Program)(sub:ioWires∪wires P⊆(WrapperOB5.sites layout).toFinset)
    (free:∀k∈OmitAll,layout.core.poolWire k∉wires P):qubits P≤1591:=by
  have lt(k:Nat)(hk:k∈OmitAll):k<2613:=by
    simp only [OmitAll,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have nd:(OmitAll.map layout.core.poolWire).Nodup:=
    List.Nodup.map_on (fun a ha b hb e=>pool_inj layout layout_widths layout_nodup a b (lt a ha) (lt b hb) e)
      (by decide)
  have cardE:(OmitAll.map layout.core.poolWire).toFinset.card=10:=by
    rw [List.toFinset_card_of_nodup nd]
    rfl
  have dis:Disjoint (ioWires∪wires P) (OmitAll.map layout.core.poolWire).toFinset:=by
    rw [Finset.disjoint_right]
    intro q hq
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hq)
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact io_avoids_pool k (lt k hk) h
    · exact free k hk h
  have s:(ioWires∪wires P)∪(OmitAll.map layout.core.poolWire).toFinset⊆(WrapperOB5.sites layout).toFinset:=by
    apply Finset.union_subset sub
    intro q hq
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hq)
    exact List.mem_toFinset.mpr (omit_sites k hk)
  have c:=Finset.card_le_card s
  rw [Finset.card_union_of_disjoint dis,cardE] at c
  have l:=List.toFinset_card_le (WrapperOB5.sites layout)
  rw [WrapperOB5.sites_length layout layout_widths] at l
  change (ioWires∪wires P).card≤1591
  omega

theorem genQ_qubits (C:Point)(cx cy:Fp):qubits (Edges.wrapper layout C cy (genQ layout cx cy))≤1591:=by
  rw [genQ_shape]
  have hG:=genericQ_sites layout layout_widths layout_nodup cx cy
  have supported:=Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup _ hG)
  have sub:=Finset.union_subset FiniteHostStack.io_support_original supported
  have edge(k:Nat)(hk:515≤k ∧ k<2613)
      (old:layout.core.poolWire k∉wires (WrapperOB5.program layout C cy (wrapG layout (genericQ layout cx cy)))):
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout (genericQ layout cx cy))):=by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h|h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted(k:Nat)(hk:k∈OmitG):layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout (genericQ layout cx cy))):=by
    have bounds:515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540:=by
      simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩ bounds.2.2.2.2.1 _
        (genericQ_free layout layout_widths layout_nodup k hk cx cy)) C cy
  apply ten_bound _ sub
  intro k hk
  simp only [OmitAll,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply edge 1400 (by omega)
    exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega) (by omega) (by omega) (by omega) _
      (spare_not_wrapG layout layout_widths layout_nodup _ hG) C cy
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · apply edge 1540 (by omega)
    exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble _ hG) C cy
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)

theorem genQ_sites (cx cy:Fp):wires (genQ layout cx cy)⊆(OB5Support.genericSites layout).toFinset:=by
  rw [genQ_shape]
  exact wrapG_sites layout layout_widths layout_nodup _ (genericQ_sites layout layout_widths layout_nodup cx cy)

end ECDSAAdd.Entrant.QSiteFinal
end QSiteFinalInventory


section QSiteMergedEntry
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

namespace ECDSAAdd.Entrant.QSiteMerged
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk

/-! ### Placement of the merged first tick

The stage kernels `QSiteDirectFields.kernelE` and `kernelX` are `Q8FusionPhase.relocated`
kernels: their first phase is the direct first tick `NativeFirstDirect.forward base`, followed by
the stack and the arithmetic clear, all renamed by the four integer-host relabelings
1026↔718, 1541↔719, 1542↔720 and 1540↔721 (`QSiteFinal.chain`), and then by the layout map
`wireFn2 L`. -/

/-- The four integer-host relabelings, as one wire map. -/
def sig (q : Wire) : Wire :=
  Q8IntegerHost.swap (Q7IntegerHost.swap (Q6IntegerHost.swap (Q5Global718.swap q)))
def pmap (L : ControlledPointLayout) (q : Wire) : Wire := wireFn2 L (sig q)

def sw (i : Nat) : Nat :=
  if i=1026 then 718 else if i=718 then 1026 else if i=1541 then 719 else if i=719 then 1541
  else if i=1542 then 720 else if i=720 then 1542 else if i=1540 then 721 else if i=721 then 1540 else i

theorem swap_base (a b i : Nat) :
    Equiv.swap (base a) (base b) (base i)=base (if i=a then b else if i=b then a else i) := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : i=a
  · subst h1; simp
  · have n1 : base i≠base a := fun e => h1 (base_injective e)
    by_cases h2 : i=b
    · subst h2; simp [n1,h1]
    · have n2 : base i≠base b := fun e => h2 (base_injective e)
      simp [n1,n2,h1,h2]

theorem sig_base (i : Nat) : sig (base i)=base (sw i) := by
  unfold sig
  simp only [Q8IntegerHost.swap,Q7IntegerHost.swap,Q6IntegerHost.swap,Q5Global718.swap,swap_base]
  congr 1
  unfold sw
  split_ifs <;> omega

theorem sig_injective : Function.Injective sig := by
  intro a b h
  unfold sig at h
  exact Q5Global718.swap.injective (Q6IntegerHost.swap.injective
    (Q7IntegerHost.swap.injective (Q8IntegerHost.swap.injective h)))

/-- The label set of the merged circuit. -/
def S : Finset Wire := (E1Merge.mSites base (base 2400)).toFinset

theorem S_cases (q : Wire) (hq : q∈S) : ∃ i, q=base i ∧
    (i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) := by
  simp only [S,E1Merge.mSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h
  all_goals first
    | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
       simp only [List.mem_range'_1] at hi
       exact ⟨i,rfl,by omega⟩)
    | exact ⟨_,h,by omega⟩

/-- Label range of the merged circuit after the scratch relocation `rho`. -/
abbrev Rng (i : Nat) : Prop :=
  i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 722 ∨ i = 723 ∨ i = 2400

theorem sw_slot (i : Nat) (hi : Rng i) : base (sw i)∈slots.toFinset := by
  apply slot_mem
  · unfold live sw; split_ifs <;> omega
  · unfold CompressedAllocation.omitted sw; split_ifs <;> omega

theorem sw_logical (i : Nat) (hi : Rng i) : base (sw i)∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨sw i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw; split_ifs <;> omega

/-! The merged circuit uses label 721 for one of its two scalar products. In the kernels that
label is the image of the vacated host label 1540, so it is moved to the clean pool label 723,
which none of the four relabelings touches. -/
def rho (q : Wire) : Wire := Equiv.swap (base 721) (base 723) q
def rhoN (i : Nat) : Nat := if i=721 then 723 else if i=723 then 721 else i

theorem rho_base (i : Nat) : rho (base i)=base (rhoN i) := by
  unfold rho rhoN
  rw [swap_base]

theorem rho_injective : Function.Injective rho := by
  intro a b h
  unfold rho at h
  exact (Equiv.swap (base 721) (base 723)).injective h

theorem rhoN_range (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) :
    Rng (rhoN i) := by
  unfold Rng rhoN; split_ifs <;> omega

/-- Placement of the merged circuit: relocation, the four relabelings, the layout map. -/
def pmapR (L : ControlledPointLayout) (q : Wire) : Wire := pmap L (rho q)

section Place
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pmap_inj : ∀a∈S,∀b∈S,pmapR L a=pmapR L b → a=b := by
  intro a ha b hb e
  obtain ⟨i,rfl,hi⟩ := S_cases a ha
  obtain ⟨j,rfl,hj⟩ := S_cases b hb
  have pl := placement2 L hw hn
  unfold pmapR pmap at e
  rw [rho_base,rho_base,sig_base,sig_base] at e
  have := pl.injectiveOnSlots _ (sw_slot _ (rhoN_range i hi)) _ (sw_slot _ (rhoN_range j hj)) e
  rw [←sig_base,←sig_base] at this
  have := sig_injective this
  rw [←rho_base,←rho_base] at this
  exact rho_injective this

theorem pmap_x : (wireBlock base 770 256).map (pmapR L)=L.point.x := by
  have pl := placement2 L hw hn
  rw [←pl.divisorMap]
  apply List.map_congr_left
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  unfold pmapR pmap; rw [rho_base,sig_base]
  congr 2; unfold sw rhoN; split_ifs <;> omega

theorem pmap_g : pmapR L (base 2400)=L.core.generic := by
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have : sw (rhoN 2400)=2400 := by unfold sw rhoN; simp
  rw [this]; exact pl.controlMap

theorem pmap_pool (q : Wire) (hq : q∈S) (hx : q∉wireBlock base 770 256) (hg : q≠base 2400) :
    pmapR L q∈L.dialogPool := by
  obtain ⟨i,rfl,hi⟩ := S_cases q hq
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have hx' : ¬(770 ≤ i ∧ i < 1026) := by
    intro h; apply hx; exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  have hg' : i≠2400 := fun e => hg (by rw [e])
  apply pl.sharedWork
  · simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨sw (rhoN i),by unfold sw rhoN; split_ifs <;> omega,rfl⟩
  · exact sw_slot _ (rhoN_range i hi)
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold sw rhoN at this; split_ifs at this <;> omega
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold sw rhoN at this; split_ifs at this <;> omega

end Place


def tickF (L : ControlledPointLayout) : Program := renameProgram (pmapR L) (NativeFirstDirect.forward base)
def entryM (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Merge.merged base (base 2400) k.val)

theorem regValue_pull (f : Wire → Wire) (r : List Wire) (s : BasisState) :
    regValue r (fun q => s (f q))=regValue (r.map f) s := by
  induction r with
  | nil => rfl
  | cons a rs ih =>
    change (if s (f a) then 1 else 0)+2*regValue rs (fun q => s (f q))=
      (if s (f a) then 1 else 0)+2*regValue (rs.map f) s
    rw [ih]

theorem g2400 : base 2400∉skywalkPoolWires base := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := base_injective e; omega

theorem merged_S (k : Nat) : wires (E1Merge.merged base (base 2400) k)⊆S :=
  E1Merge.merged_support base (base 2400) k

theorem prefix_S : (NativeFirstDirect.prefixSites base).toFinset⊆S := by
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  simp only [S,List.mem_toFinset]
  rcases h with ((h|h)|h)|h|h
  · exact E1Merge.blk_mSites base (base 2400) 0 257 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 770 258 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 1540 256 (by omega) q h
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1028 (by omega)
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1797 (by omega)

theorem forward_S : wires (NativeFirstDirect.forward base)⊆S :=
  Finset.Subset.trans (NativeFirstDirect.prefix_support base).1 prefix_S

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

/-- Physical form: the merged entry equals the compare-first constant addition followed by the
renamed direct first tick, on every pair of measurement records. -/
theorem entry_eq (k : Fp) (s : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (entryM L k) m1 s=run (fastConstAdd L L.point.x k++tickF L) m2 s := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Merge.kR base) t.basis=X := by
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- old side
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) hg hx hc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) s=s1 at fca
  obtain ⟨p1,x1,o1⟩ := fca
  let u : State := ⟨t.phase,fun q => if q∈E1Merge.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Merge.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Merge.kR base) u.basis=(X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Merge.kR_x base base_pool_nodup]
    have e1 : regValue (E1Merge.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Merge.kR base := E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Merge.kR base := E1Merge.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1Merge.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (merged_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Merge.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++tickF L) m2 s=
      run (tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryM,newSide.1,eqL,tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryM,newSide.2 a ha,eqL,tickF,oldSide.2 a ha]
    · rw [entryM,run_rename_pool_outside F S _ (merged_S k.val) m1 s q im,tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry


/-! ### Splitting the stage kernels at the first tick -/

theorem rp_append (f : Wire → Wire) (a b : Program) :
    renameProgram f (a++b)=renameProgram f a++renameProgram f b := List.map_append

/-- The kernels' first phase after its direct first tick. -/
def tailP : Program := stackForwardT++skywalkArithmeticClear base

theorem first_eq : Q5Global718.firstPhase=NativeFirstDirect.forward base++tailP := rfl

theorem chain_append (a b : Program) :
    QSiteFinal.chain (a++b)=QSiteFinal.chain a++QSiteFinal.chain b := by
  simp only [QSiteFinal.chain,rp_append]

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L) (QSiteFinal.chain tailP++
    (QSiteDirectFields.hosted QSiteDirectFields.fieldE++QSiteFinal.chain Q5Global718.lastPhase))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L) (QSiteFinal.chain tailP++
    (QSiteDirectFields.hosted QSiteDirectFields.fieldX++QSiteFinal.chain Q5Global718.lastPhase))

/-- Congruence of renamings through a support bound (keeps concrete programs abstract). -/
theorem congr_sub (f g : Wire → Wire) (P : Program) (T : Finset Wire) (hP : wires P ⊆ T)
    (h : ∀ q ∈ T, f q = g q) : renameProgram f P = renameProgram g P :=
  renameProgram_congr_support f g P (fun q hq => h q (hP hq))

/-- The relocation `rho` fixes every label of the direct tick. -/
theorem rho_fix (f : Wire → Wire) :
    renameProgram (fun q => f (rho q)) (NativeFirstDirect.forward base)=
      renameProgram f (NativeFirstDirect.forward base) := by
  apply congr_sub _ _ _ _ (NativeFirstDirect.prefix_support base).1
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  have e : ∃ i, q=base i ∧ (i < 257 ∨ (770 ≤ i ∧ i < 1028) ∨ (1540 ≤ i ∧ i < 1796) ∨ i = 1028 ∨ i = 1797) := by
    rcases h with ((h|h)|h)|h|h
    all_goals first
      | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
         simp only [List.mem_range'_1] at hi
         exact ⟨i,rfl,by omega⟩)
      | exact ⟨_,h,by omega⟩
  obtain ⟨i,rfl,hi⟩ := e
  have b1 : base i≠base 721 := fun h => by have := base_injective h; omega
  have b2 : base i≠base 723 := fun h => by have := base_injective h; omega
  unfold rho
  rw [Equiv.swap_apply_of_ne_of_ne b1 b2]

/-- The kernels' placed first tick is exactly `tickF`. -/
theorem tick_eq (L : ControlledPointLayout) :
    renameProgram (wireFn2 L) (QSiteFinal.chain (NativeFirstDirect.forward base))=tickF L := by
  rw [tickF,show pmapR L=fun q => pmap L (rho q) from rfl,rho_fix]
  simp only [QSiteFinal.chain,renameProgram_comp]
  rfl

theorem entry_split (L : ControlledPointLayout) : QSiteFinal.arithE L=tickF L++restE L := by
  rw [←tick_eq]
  simp only [QSiteFinal.arithE,QSiteDirectFields.kernelE,QSiteFinal.relocated_shape,first_eq,chain_append,
    restE,rp_append,List.append_assoc]

theorem exit_split (L : ControlledPointLayout) : QSiteFinal.arithX L=tickF L++restX L := by
  rw [←tick_eq]
  simp only [QSiteFinal.arithX,QSiteDirectFields.kernelX,QSiteFinal.relocated_shape,first_eq,chain_append,
    restX,rp_append,List.append_assoc]

/-- Replace a prefix whose final state agrees with an old prefix on every record. -/
theorem tri_transfer {P Q : BasisState → Prop} {A B R : Program}
    (h : ∀s : State,P s.basis → ∀ m1 m2 : List Bool,run A m1 s=run B m2 s)
    (t : Triple P (B++R) Q) : Triple P (A++R) Q := by
  intro s m hs
  have := t s (List.replicate (measurementCount B) false++m.drop (measurementCount A)) hs
  rw [run_append] at this ⊢
  have e1 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).take
      (measurementCount B)=List.replicate (measurementCount B) false := by simp
  have e2 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).drop
      (measurementCount B)=m.drop (measurementCount A) := by simp
  rw [e1,e2] at this
  rw [h s hs (m.take (measurementCount A)) (List.replicate (measurementCount B) false)]
  exact this

section Entry1
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem lay (q : Wire) :
    (q∈L.point.x → q∉L.point.y) ∧ (q∈L.dialogPool → q∉L.point.x ∧ q∉L.point.y) ∧
    (q=L.core.generic → q∉L.point.x ∧ q∉L.point.y) := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  refine ⟨fun hx hy => ?_,fun hp => ⟨fun hx => ?_,fun hy => ?_⟩,fun hg => ⟨fun hx => ?_,fun hy => ?_⟩⟩
  all_goals
    first
    | (have h1 := List.count_pos_iff.mpr hx; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)

/-- The y-side fused offset commutes with the x-side constant addition, so the merged x entry
can run after it. -/
theorem entry1_eq (k ky : Fp) (s : State) (X : Nat) (hX : X<p) (Y : Fp) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (hg : s.basis L.core.generic=G) (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s := by
  have xy (q : Wire) (h : q∈L.point.x) : q∉L.point.y := (lay L hw hn q).1 h
  have px (q : Wire) (h : q∈L.dialogPool) : q∉L.point.x := ((lay L hw hn q).2.1 h).1
  have py (q : Wire) (h : q∈L.dialogPool) : q∉L.point.y := ((lay L hw hn q).2.1 h).2
  have gx : L.core.generic∉L.point.x := ((lay L hw hn _).2.2 rfl).1
  have gy : L.core.generic∉L.point.y := ((lay L hw hn _).2.2 rfl).2
  -- left: fusedY then merged entry
  have fy := EntryFuse.fusedY_correct L hw hn Y ky s (m1.take (measurementCount (EntryFuse.fusedY L ky))) hy hc
  generalize hsy : run (EntryFuse.fusedY L ky) (m1.take (measurementCount (EntryFuse.fusedY L ky))) s=sy at fy
  obtain ⟨py1,py2,py3⟩ := fy
  have syx : regValue L.point.x sy.basis=X := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (xy q hq)),hx]
  have syg : sy.basis L.core.generic=G := (py3 _ gy).trans hg
  have syc : regValue L.dialogPool sy.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (py q hq)),hc]
  -- commutation of the two constant steps
  have comm (r0 r1 r2 : List Bool) : run (fastConstAdd L L.point.x k) r0 sy=
      run (EntryFuse.fusedY L ky) r2 (run (fastConstAdd L L.point.x k) r1 s) := by
    have fa := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX sy r0 syg syx syc
    have fc := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s r1 hg hx hc
    generalize ha : run (fastConstAdd L L.point.x k) r0 sy=a at fa
    generalize hcc : run (fastConstAdd L L.point.x k) r1 s=c at fc
    obtain ⟨a1,a2,a3⟩ := fa
    obtain ⟨c1,c2,c3⟩ := fc
    have cy : regValue L.point.y c.basis=Y.val := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (fun h => xy q h hq)),hy]
    have cc : regValue L.dialogPool c.basis=0 := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (px q hq)),hc]
    have fb := EntryFuse.fusedY_correct L hw hn Y ky c r2 cy cc
    generalize hb : run (EntryFuse.fusedY L ky) r2 c=b at fb
    obtain ⟨b1,b2,b3⟩ := fb
    have cg : c.basis L.core.generic=s.basis L.core.generic := c3 _ gx
    apply State.extensionality
    · rw [a1,b1,c1,py1]
    · funext q
      by_cases qx : q∈L.point.x
      · have e : regValue L.point.x a.basis=regValue L.point.x b.basis := by
          rw [a2,regValue_congr _ _ c.basis (fun q hq => b3 q (xy q hq)),c2]
        exact (regValue_eq_iff _ _ _).mp e q qx
      by_cases qy : q∈L.point.y
      · have e : regValue L.point.y a.basis=regValue L.point.y b.basis := by
          rw [regValue_congr _ _ sy.basis (fun q hq => a3 q (fun h => xy q h hq)),py2,b2,cg]
        exact (regValue_eq_iff _ _ _).mp e q qy
      rw [a3 q qx,b3 q qy,c3 q qx,py3 q qy]
  -- assemble
  let nA := measurementCount (fastConstAdd L L.point.x k)
  let nY := measurementCount (EntryFuse.fusedY L ky)
  let M := List.replicate nA false++m2.drop (nA+nY)
  have lhs : run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (tickF L) (m2.drop (nA+nY)) (run (fastConstAdd L L.point.x k) (List.replicate nA false) sy) := by
    rw [run_append,hsy,entry_eq L hw hn k sy X hX G syx syg syc _ M,run_append]
    have t1 : M.take nA=List.replicate nA false := List.take_left' (by simp)
    have t2 : M.drop nA=m2.drop (nA+nY) := List.drop_left' (by simp)
    rw [t1,t2]
  have rhs : run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s=
      run (tickF L) (m2.drop (nA+nY)) (run (EntryFuse.fusedY L ky) ((m2.take (nA+nY)).drop nA)
        (run (fastConstAdd L L.point.x k) ((m2.take (nA+nY)).take nA) s)) := by
    rw [run_append,run_append,measurementCount_append]
  rw [lhs,rhs,comm]

end Entry1


/-! ### The generic body with both constant additions absorbed into the first ticks -/

section Generic
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse

def genericM (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  EntryFuse.fusedY L (-cy)++entryM L (-cx)++restE L++QSiteFinal.squareQ L++
  entryM L (3*cx-(OwnDiagAll12Square.sqOff:Fp))++restX L++(fastConstNeg L cx++ExitFuse.fusedExitY L cy)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
    (mixedTranscriptTape base))
include hw hn logicalND hlo logicalAway logicalReplay
attribute [local irreducible] run fastConstAdd fastConstNeg ExitFuse.fusedExitY EntryFuse.fusedY

theorem prefix1 (X Y cx cy : Fp) (G : Bool) (origin : BasisState) (hX : X+(if G then -cx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin)
      (EntryFuse.fusedY L (-cy)++entryM L (-cx)++restE L)
      (PointDialogValues L (X+(if G then -cx else 0))
        ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) G origin) := by
  have h1 := fastStep_addX L hw hn X Y G origin (-cx)
  have h2 := QSiteFinal.divisionQ_step L hw hn logicalND hlo logicalAway logicalReplay
    (X+(if G then -cx else 0)) Y (-cy) G origin hX
  have h12 := h1.seq h2
  rw [QSiteFinal.divisionQ,entry_split,
    show fastConstAdd L L.point.x (-cx)++(EntryFuse.fusedY L (-cy)++(tickF L++restE L))=
      (fastConstAdd L L.point.x (-cx)++EntryFuse.fusedY L (-cy)++tickF L)++restE L by
      simp only [List.append_assoc]] at h12
  exact tri_transfer (fun s hs m1 m2 => entry1_eq L hw hn (-cx) (-cy) s X.val X.isLt Y G
    hs.x hs.y hs.generic hs.clean m1 m2) h12

omit logicalND hlo logicalAway logicalReplay in
theorem suffix2 (X Y k cx cy : Fp) (G : Bool) (origin : BasisState) (hX : X+(if G then k else 0)≠0) :
    Triple (PointDialogValues L X Y G origin)
      (entryM L k++(restX L++(fastConstNeg L cx++ExitFuse.fusedExitY L cy)))
      (PointDialogValues L (if G then cx-(X+(if G then k else 0)) else X+(if G then k else 0))
        (Y*(X+(if G then k else 0))-(if G then cy else 0)) G origin) := by
  have h4 := fastStep_addX L hw hn X Y G origin k
  have h5 := QSiteFinal.exitQ_step L hw hn (X+(if G then k else 0)) Y cx cy G origin hX
  have h45 := h4.seq h5
  rw [QSiteFinal.exitQ,exit_split,
    show fastConstAdd L L.point.x k++((tickF L++restX L)++(fastConstNeg L cx++ExitFuse.fusedExitY L cy))=
      (fastConstAdd L L.point.x k++tickF L)++(restX L++(fastConstNeg L cx++ExitFuse.fusedExitY L cy)) by
      simp only [List.append_assoc]] at h45
  exact tri_transfer (fun s hs m1 m2 => entry_eq L hw hn k s X.val X.isLt G hs.x hs.generic hs.clean m1 m2) h45

theorem genericM_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (genericM L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h12 := prefix1 L hw hn logicalND hlo logicalAway logicalReplay X Y cx cy true origin
    (by simp only [if_true,←sub_eq_add_neg]; exact sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,←sub_eq_add_neg,ha] at h12
  have h3 := QSiteFinal.squareQ_step L hw hn (X-cx) a true origin
  simp only [if_true] at h3
  have hd4 : (X-cx)-(a*a-(OwnDiagAll12Square.sqOff:Fp))+(3*cx-(OwnDiagAll12Square.sqOff:Fp))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]; ring
  have h45 := suffix2 L hw hn ((X-cx)-(a*a-(OwnDiagAll12Square.sqOff:Fp))) a
    (3*cx-(OwnDiagAll12Square.sqOff:Fp)) cx cy true origin (by simp only [if_true]; rw [hd4]; exact hd)
  simp only [if_true] at h45
  rw [hd4] at h45
  rw [show cx-d=genericX X Y cx cy by dsimp [d]; ring] at h45
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h45
  have h := (h12.seq h3).seq h45
  simpa only [genericM,List.append_assoc] using h

theorem genericM_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (genericM L cx cy)
      (PointDialogValues L X Y false origin) := by
  have h12 := prefix1 L hw hn logicalND hlo logicalAway logicalReplay X Y cx cy false origin
    (by simpa using hX)
  have h3 := QSiteFinal.squareQ_step L hw hn X (Y/X) false origin
  have h45 := suffix2 L hw hn X (Y/X) (3*cx-(OwnDiagAll12Square.sqOff:Fp)) cx cy false origin
    (by simpa using hX)
  have back : Y/X*X=Y := div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h12 h3 h45
  rw [back] at h45
  have h := (h12.seq h3).seq h45
  simpa only [genericM,List.append_assoc] using h

end Generic


/-! ### The wrapped body -/

section Wrap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite FiniteHostStack FiniteHostFusion FiniteHostFive QSiteFinal

def genM (L : ControlledPointLayout) (cx cy : Fp) : Program := QSiteFinal.wrapG L (genericM L cx cy)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem midM_values (Gp : Program) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') Gp
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (clrF L ++ renameProgram (swapF L) Gp ++ clrF L)
      (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn Gp X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2

variable (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
    (mixedTranscriptTape base))
include logicalND hlo logicalAway logicalReplay

theorem genM_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genM L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midM_values L hw hn (genericM L cx cy) 5 0 5 0 false s.basis false
      (fun base' => genericM_false L hw hn logicalND hlo logicalAway logicalReplay 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midM_values L hw hn (genericM L cx cy) x y x y false s.basis true
        (fun base' => genericM_false L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midM_values L hw hn (genericM L cx cy) x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => genericM_true L hw hn logicalND hlo logicalAway logicalReplay x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ←genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Wrap


/-! ### Resources -/

section Res
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite FiniteHostStack FiniteHostFusion FiniteHostFive QSiteFinal QSiteDirectFields

attribute [local irreducible] wires E1Merge.merged NativeFirstDirect.forward

/-- The logical program under the four integer-host relabelings. -/
def sigP (P : Program) : Program :=
  renameProgram Q8IntegerHost.swap (renameProgram Q7IntegerHost.swap
    (renameProgram Q6IntegerHost.swap (renameProgram Q5Global718.swap P)))

/-- The merged circuit after the scratch relocation. -/
def rhoP (P : Program) : Program := renameProgram rho P

theorem entryM_eq (L : ControlledPointLayout) (k : Fp) :
    entryM L k=renameProgram (wireFn2 L) (sigP (rhoP (E1Merge.merged base (base 2400) k.val))) := by
  simp only [entryM,sigP,rhoP,renameProgram_comp]
  rfl

theorem sigP_wires (P : Program) (q : Wire) (hq : q∈wires (sigP P)) : ∃a∈wires P,q=sig a := by
  simp only [sigP,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨b,⟨c,⟨d,⟨a,ha,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hq
  exact ⟨a,ha,rfl⟩

theorem rhoP_wires (P : Program) (q : Wire) (hq : q∈wires (rhoP P)) : ∃a∈wires P,q=rho a := by
  simp only [rhoP,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,ha,rfl⟩ := hq
  exact ⟨a,ha,rfl⟩

/-- Every label of the placed merged circuit, before the layout map. -/
theorem merged_labels (k : Nat) (q : Wire)
    (hq : q∈wires (sigP (rhoP (E1Merge.merged base (base 2400) k)))) :
    ∃ j, q=base (sw (rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j = 721 ∨ j = 722 ∨ j = 2400) := by
  obtain ⟨a,ha,e⟩ := sigP_wires _ q hq
  obtain ⟨b,hb,e2⟩ := rhoP_wires _ a ha
  obtain ⟨j,ej,hj⟩ := S_cases b (Finset.mem_of_subset (merged_S k) hb)
  refine ⟨j,?_,hj⟩
  rw [e,e2,ej,rho_base,sig_base]

theorem logicalM (k : Nat) :
    wires (sigP (rhoP (E1Merge.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨j,rfl,hj⟩ := merged_labels k q hq
  exact sw_logical _ (rhoN_range j hj)

theorem entryM_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryM L k)=1026 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Merge.merged base (base 2400) k.val)
  have c := E1Merge.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

theorem entryM_slots (L : ControlledPointLayout) (k : Fp) : gateSlots (entryM L k)≤25000 := by
  simpa only [entryM,Baselines.rename_gateSlots] using E1Merge.merged_slots base (base 2400) k.val

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem entryM_sites (k : Fp) : wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

include hn

theorem sw_avoid (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨ j = 721 ∨ j = 722 ∨ j = 2400) :
    sw (rhoN j)∉[2312,766,765,767,1026,1541,1542,1540] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  unfold sw rhoN; split_ifs <;> omega

theorem merged_omits (k : Fp) (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542,1540]) :
    base i∉wires (sigP (rhoP (E1Merge.merged base (base 2400) k.val))) := by
  intro h
  obtain ⟨j,e,hj⟩ := merged_labels k.val (base i) h
  have := base_injective e
  exact sw_avoid L hw hn j hj (this ▸ hi)

theorem entryM_free (k : Fp) (kk : Nat) (hk : kk∈OmitG) : L.core.poolWire kk∉wires (entryM L k) := by
  rw [entryM_eq]
  exact kernel_placed_free L hw hn _ (logicalM k.val) (merged_omits L hw hn k) kk hk

theorem entryM_physical (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1Merge.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (Finset.mem_of_subset (merged_S k.val) ha) b
      (Finset.mem_of_subset (merged_S k.val) hb) e)
    (E1Merge.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem restE_sub : wires (restE L)⊆wires (arithE L) := by
  rw [entry_split,wires_append]; exact Finset.subset_union_right
theorem restX_sub : wires (restX L)⊆wires (arithX L) := by
  rw [exit_split,wires_append]; exact Finset.subset_union_right

theorem genericM_free (k : Nat) (hk : k∈OmitG) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericM L cx cy) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have x := constant_ports_avoid_large L hw hn k bounds L.point.x (Or.inl rfl)
  have y := constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [genericM,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨fun h => y (fusedY_support L hw (-cy) h),entryM_free L hw hn _ k hk⟩,
    fun h => arithE_free L hw hn k hk (restE_sub L hw hn h)⟩,squareQ_free L hw hn k hk⟩,
    entryM_free L hw hn _ k hk⟩,fun h => arithX_free L hw hn k hk (restX_sub L hw hn h)⟩,
    ⟨fun h => x (neg_palette L hw cx h),fun h => y (fusedExitY_support L hw cy h)⟩⟩

theorem genericM_sites (cx cy : Fp) : wires (genericM L cx cy)⊆(OB5Support.sites L).toFinset := by
  have cn := (neg_palette L hw cx).trans (finConst_sites L hw L.point.x (Or.inl rfl))
  have fy := (fusedY_support L hw (-cy)).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  have ey := (fusedExitY_support L hw cy).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  have ar : wires (arithE L)⊆(OB5Support.sites L).toFinset := by
    unfold arithE
    exact OB5Support.placed_support_logical L hw _ kernelE_support
  have ax : wires (arithX L)⊆(OB5Support.sites L).toFinset := by
    unfold arithX
    exact OB5Support.placed_support_logical L hw _ kernelX_support
  simp only [genericM,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨fy,entryM_sites L hw _⟩,(restE_sub L hw hn).trans ar⟩,squareQ_support L hw hn⟩,
    entryM_sites L hw _⟩,(restX_sub L hw hn).trans ax⟩,⟨cn,ey⟩⟩

theorem genericM_physical (cx cy : Fp) : GatePhysical (genericM L cx cy) := by
  have ng := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have fy := fusedY_physical L hw hn (-cy)
  have ex := fusedExitY_physical L hw hn cy
  have sq := squareQ_physical L hw hn
  have di : GatePhysical (arithE L) := by
    unfold arithE
    apply gatePhysical_rename_support (wireFn2 L) kernelE
    · intro a ha b hb eq
      exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelE_support ha)) b
        (ArithmeticOB5.logical_sub_old (kernelE_support hb)) eq
    · exact kernelE_physical
  have mu : GatePhysical (arithX L) := by
    unfold arithX
    apply gatePhysical_rename_support (wireFn2 L) kernelX
    · intro a ha b hb eq
      exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelX_support ha)) b
        (ArithmeticOB5.logical_sub_old (kernelX_support hb)) eq
    · exact kernelX_physical
  rw [entry_split,gatePhysical_append] at di
  rw [exit_split,gatePhysical_append] at mu
  simp only [genericM,fastConstNeg,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨fy,entryM_physical L hw hn _⟩,di.2⟩,sq⟩,entryM_physical L hw hn _⟩,mu.2⟩,⟨ng,ex⟩⟩

theorem genM_physical (cx cy : Fp) : GatePhysical (genM L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have r := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (genericM_physical L hw hn cx cy)
  simp only [genM,wrapG,gatePhysical_append]
  exact ⟨⟨z,⟨c,r⟩,c⟩,z⟩

omit hn in
theorem genericM_slots (cx cy : Fp) : gateSlots (genericM L cx cy)≤49320000 := by
  have ng := FastConst.fastNeg_gateSlots_le (g:=L.core.generic) 256 p cx.val
    (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have fy := entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement (-cy).val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  have ex := exit_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement cy.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  have d : gateSlots (arithE L)≤20500006 := by
    simpa only [arithE,Baselines.rename_gateSlots] using kernelE_slots
  have e : gateSlots (arithX L)≤20500006 := by
    simpa only [arithX,Baselines.rename_gateSlots] using kernelX_slots
  rw [entry_split,gateSlots_append] at d
  rw [exit_split,gateSlots_append] at e
  have sq := squareQ_slots L hw
  have m1 := entryM_slots L (-cx)
  have m2 := entryM_slots L (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  simp only [genericM,fusedY,fusedExitY,fastConstNeg,gateSlots_append]
  omega

omit hn in
theorem genM_slots (cx cy : Fp) : gateSlots (genM L cx cy)≤49326000 := by
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  have f := genericM_slots L hw cx cy
  have rs := rename_gateSlots (swapF L) (genericM L cx cy)
  simp only [genM,wrapG,gateSlots_append,rs]
  omega

omit hn in
theorem genericM_counts (cx cy : Fp) :
    toffoliCount (genericM L cx cy)+496=toffoliCount (genericQ L cx cy) ∧
    measurementCount (genericM L cx cy)+496=measurementCount (genericQ L cx cy) := by
  have k1 := fastConstAdd_counts L hw L.point.x (Or.inl rfl) (-cx)
  have k2 := fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  have e1 := entryM_counts L (-cx)
  have e2 := entryM_counts L (3*cx-(OwnDiagAll12Square.sqOff:Fp))
  have t := tickF_counts L
  simp only [genericM,genericQ,divisionQ,exitQ,entry_split,exit_split,toffoliCount_append,measurementCount_append]
  constructor <;> omega

omit hn in
theorem genM_counts (cx cy : Fp) :
    toffoliCount (genM L cx cy)+496=toffoliCount (genQ L cx cy) ∧
    measurementCount (genM L cx cy)+496=measurementCount (genQ L cx cy) := by
  have g := genericM_counts L hw cx cy
  have r := renameProgram_counts (swapF L) (genericM L cx cy)
  have r' := renameProgram_counts (swapF L) (genericQ L cx cy)
  rw [genQ_shape]
  simp only [genM,wrapG,toffoliCount_append,measurementCount_append,r.1,r.2,r'.1,r'.2]
  constructor <;> omega

end Res

section Inventory
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse ExitFuse
  EntryFuseFinite ExitFuseFinite FiniteHostStack FiniteHostFusion FiniteHostFive QSiteFinal

theorem genM_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genM layout cx cy))≤1591 := by
  rw [genM]
  have hG := genericM_sites layout layout_widths layout_nodup cx cy
  have supported := Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup _ hG)
  have sub := Finset.union_subset FiniteHostStack.io_support_original supported
  have edge (k : Nat) (hk : 515≤k ∧ k<2613)
      (old : layout.core.poolWire k∉wires (WrapperOB5.program layout C cy (wrapG layout (genericM layout cx cy)))) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout (genericM layout cx cy))) := by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h|h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted (k : Nat) (hk : k∈OmitG) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout (genericM layout cx cy))) := by
    have bounds : 515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540 := by
      simp only [OmitG,List.mem_cons,List.not_mem_nil,or_false] at hk
      omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩ bounds.2.2.2.2.1 _
        (genericM_free layout layout_widths layout_nodup k hk cx cy)) C cy
  apply ten_bound _ sub
  intro k hk
  simp only [OmitAll,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply edge 1400 (by omega)
    exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega) (by omega) (by omega) (by omega) _
      (spare_not_wrapG layout layout_widths layout_nodup _ hG) C cy
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · apply edge 1540 (by omega)
    exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble _ hG) C cy
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)
  · exact omitted _ (by simp)

theorem genM_sites (cx cy : Fp) : wires (genM layout cx cy)⊆(OB5Support.genericSites layout).toFinset := by
  rw [genM]
  exact wrapG_sites layout layout_widths layout_nodup _ (genericM_sites layout layout_widths layout_nodup cx cy)

end Inventory

end ECDSAAdd.Entrant.QSiteMerged
end QSiteMergedEntry



section QSiteFinalCertificate
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines EntryFuseFinite ExitFuseFinite QSiteFinal

/-- Infinity emits no gates; finite addition uses the direct-record generic block. -/
def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      OwnDHWrapper.wrapper layout C cy (QSiteMerged.genM layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2151856, 1496697, 1591, 50000004⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, run, ← WeierstrassCurve.Affine.Point.zero_def, add_zero, ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have cfg := MappedCompressed.LaneA.laneLogical_config
    have above : History5.HistoryAbove MappedCompressed.base := by intro j hj; simp [MappedCompressed.base]
    have hG := QSiteMerged.genM_sites cx cy
    exact fixed_correct _ b R _
      (OwnDHWrapper.full_spec layout layout_widths layout_nodup R hc b _
        (QSiteMerged.genM_ok layout layout_widths layout_nodup cfg.1 above cfg.2.1 cfg.2.2 hc) hG)
      ((OwnDHWrapper.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151856 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have h := (OwnDHWrapper.wrapper_counts layout layout_widths
      (QSiteMerged.genM layout cx cy) hc).1
    have g := (SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf := (genF_counts layout layout_widths cx cy).1
    have gd := (genBothF_counts_diff layout layout_widths cx cy).1
    have ge := (EntryFuseFinite.genFFused_counts_diff layout layout_widths cx cy).1
    have gq := (genQ_counts layout layout_widths cx cy).1
    have gm := (QSiteMerged.genM_counts layout layout_widths cx cy).1
    change toffoliCount (OwnDHWrapper.wrapper layout (.some hc) cy (QSiteMerged.genM layout cx cy)) ≤ _
    omega

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1496697 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have h := (OwnDHWrapper.wrapper_counts layout layout_widths
      (QSiteMerged.genM layout cx cy) hc).2
    have g := (SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf := (genF_counts layout layout_widths cx cy).2
    have gd := (genBothF_counts_diff layout layout_widths cx cy).2
    have ge := (EntryFuseFinite.genFFused_counts_diff layout layout_widths cx cy).2
    have gq := (genQ_counts layout layout_widths cx cy).2
    have gm := (QSiteMerged.genM_counts layout layout_widths cx cy).2
    change measurementCount (OwnDHWrapper.wrapper layout (.some hc) cy (QSiteMerged.genM layout cx cy)) ≤ _
    omega

set_option linter.constructorNameAsVariable false in
/-- Static support: the one-bank inventory without pool sites 1400, 1800, 766, 765, 767, 1540, 770, 1284, 1285, 1286. -/
theorem program_qubits (C : Point) : qubits (program C) ≤ 1591 := by
  cases C with
  | zero =>
    change qubits [] ≤ 1591
    rw [qubits_empty]
    decide
  | @some cx cy hc =>
    have sub:=OwnDHWrapper.wrapper_subset layout (.some hc) cy (QSiteMerged.genM layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) sub)).trans (QSiteMerged.genM_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc =>
    exact OwnDHWrapper.wrapper_physical layout layout_widths layout_nodup _ cy _
      (QSiteMerged.genM_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50000004 := by
  cases C with
  | zero => simp [program, gateSlots]
  | @some cx cy hc =>
    have h := OwnDHWrapper.wrapper_slots layout layout_widths (.some hc) cy
      (QSiteMerged.genM layout cx cy)
    have g := QSiteMerged.genM_slots layout layout_widths cx cy
    change gateSlots (OwnDHWrapper.wrapper layout (.some hc) cy (QSiteMerged.genM layout cx cy)) ≤ _
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1496697
    rw [normalize_measurements]
    exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1591
    rw [normalize_qubits]
    exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50000004
    rw [normalize_slots]
    exact program_gateSlots C

end ECDSAAdd.Entrant
end QSiteFinalCertificate
