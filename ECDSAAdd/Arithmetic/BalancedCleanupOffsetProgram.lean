import ECDSAAdd.Arithmetic.BalancedFieldCircuitProgram
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProgram
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedCircuit BalancedField

/-- Rejected cost-screen layout. Its extra full carry bank violates the
776-site field-kernel envelope. This module is not selected by production. -/
structure Layout extends toCircuit : BalancedCircuit.Layout where
  offsetCarry : List Wire

def Layout.wires (L : Layout) := L.toCircuit.wires++L.offsetCarry
def Layout.Widths (L : Layout) := L.toCircuit.Widths ∧ L.offsetCarry.length=256

def offset : Nat := (BalancedCircuit.sparseF-1)/2

/-- J has bit1 clear, so J+2*Lower is read without a constant register. -/
def offsetBits (L : Layout) : List MappedBit := (List.range 256).map fun i =>
  if i=1 then {wire:=some L.lower,flip:=false}
  else {wire:=none,flip:=offset.testBit i}

/-- Temporarily form each sum bit, compare it, and restore it while unwinding.
The offset and comparator prefixes occupy separate full clean carry banks.
Functional correctness, including all measured phase corrections, is pending. -/
def chain : List MappedBit → List Wire → List Wire → List Wire → List Wire →
    Wire → Wire → Wire → Program
  | b::bits,a::as,y::ys,c::cs,d::ds,cinC,cinB,target =>
      mappedMajority b y cinC c++mappedSum b y cinC++[.X y]++
      majority a y cinB d++chain bits as ys cs ds c d target++
      eraseCarry a y cinB d++[.X y]++mappedSum b y cinC++mappedEraseCarry b y cinC c
  | [],[],[],[],[],_,cinB,target => flipBelow none cinB target
  | _,_,_,_,_,_,_,_ => []

/-- Magnitude is doubled by a Clifford rotation. Only the source comparison
word receives the signed-to-unsigned top-bit bias. -/
def view (L : Layout) : Program :=
  rotateLeft L.r++[.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]++
  signComplement L.sign L.y++signComplement L.lower L.y++[.X L.ymsb]

/-- Actual isolated emission. The comparator carry-in is Cout=1 and the
constant carry-in is One=0. No finite comparison window appears. -/
def program (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toCircuit.toLayout++view L++[.X L.cout]++
  chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
  [.X L.cout]++(view L).reverse++(BalancedCleanup.prepareSign L.toCircuit.toLayout).reverse

theorem chain_counts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (cinC cinB target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (chain bits xs ys cs ds cinC cinB target)=2*ys.length ∧
    measurementCount (chain bits xs ys cs ds cinC cinB target)=2*ys.length := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have b := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have x := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have c := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have d := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simp [chain,flipBelow,toffoliCount,measurementCount]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons x xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            have h := ih bits xs cs ds c d (by simpa using hb) (by simpa using hx)
              (by simpa using hc) (by simpa using hd)
            rcases mappedBit_counts b y cinC c with ⟨mt,mm,et,em,st,sm⟩
            have majT : toffoliCount (majority x y cinB d)=1 := rfl
            have am : measurementCount (majority x y cinB d)=0 := rfl
            have dt : toffoliCount (eraseCarry x y cinB d)=0 := rfl
            have dm : measurementCount (eraseCarry x y cinB d)=1 := rfl
            simp only [chain,toffoliCount_append,measurementCount_append,mt,mm,et,em,
              st,sm,majT,am,dt,dm,h.1,h.2]
            simp [toffoliCount,measurementCount,List.length_cons]
            all_goals omega

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=512 ∧ measurementCount (program L)=512 := by
  have w := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have h := chain_counts (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity
    (by simp [offsetBits,w.2.1]) (by omega) (by omega) (by omega)
  have r := rotate_counts L.r
  have c1 := signComplement_counts L.sign L.y
  have c2 := signComplement_counts L.lower L.y
  have c3 := signComplement_counts L.lower L.r
  simp only [program,view,BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,r.2.2.1,r.2.2.2,c1.1,c1.2,c2.1,c2.2,
    c3.1,c3.2,h.1,h.2,w.2.1]
  norm_num [toffoliCount,measurementCount]

theorem declaredSites (L : Layout) (hw : L.Widths) : L.wires.length=1032 := by
  rw [Layout.wires,List.length_append,BalancedCircuit.declaredSites L.toCircuit hw.1,hw.2]

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.counts
