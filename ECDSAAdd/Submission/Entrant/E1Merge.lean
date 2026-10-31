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

