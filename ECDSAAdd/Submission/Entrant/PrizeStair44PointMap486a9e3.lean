import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Framework.CleanWireRebind
import ECDSAAdd.Framework.WireRenameComposition
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.DeadCarry
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.PrizeStairArchiveEnter09fd522f
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Submission.Entrant.StairArchiveIntegerColumns
import ECDSAAdd.Submission.Entrant.StairSideA

section

namespace ECDSAAdd.Entrant.Stair44PointMap

def chain : List (Wire × Wire) → Equiv.Perm Wire
  | [] => Equiv.refl Wire
  | (a,b)::xs => (Equiv.swap a b).trans (chain xs)

def earlyPairs : List (Wire × Wire) :=
  [(4835,4615),(4836,4616),(4837,4617),(4838,4618),(4839,4619)]
def yPairs : List (Wire × Wire) :=
  [(4615,4915),(4616,4916),(4617,4917),(4618,4918),(4619,4919)]
def outer : Equiv.Perm Wire := chain earlyPairs
def duringY : Equiv.Perm Wire := (chain yPairs).trans outer

def encode (P : Program) := renameProgram outer P
def encodeY (P : Program) := renameProgram duringY P

theorem clean_chain (pairs : List (Wire × Wire)) (f : Wire → Wire) (actual logical : State)
    (clean : ∀ t∈pairs, logical.basis t.1=false ∧ logical.basis t.2=false) :
    pullState (f ∘ chain pairs) actual = logical ↔ pullState f actual = logical := by
  induction pairs generalizing f with
  | nil => rfl
  | cons ab xs ih =>
    obtain ⟨a,b⟩ := ab
    have flags := clean (a,b) List.mem_cons_self
    let g := f ∘ chain xs
    change pullState (g ∘ Equiv.swap a b) actual = logical ↔ pullState f actual = logical
    constructor
    · intro h
      have twice : (Equiv.swap a b : Wire → Wire) ∘ Equiv.swap a b = id := by
        funext q; exact Equiv.swap_apply_self a b q
      have e := cleanWireRebind _ actual logical _ _ h flags.1 flags.2
      have old : pullState g actual = logical := by simpa only [Function.comp_assoc,twice,Function.comp_id] using e
      exact (ih f (fun t ht => clean t (List.mem_cons_of_mem _ ht))).mp old
    · intro h
      have old := (ih f (fun t ht => clean t (List.mem_cons_of_mem _ ht))).mpr h
      exact cleanWireRebind g actual logical a b old flags.1 flags.2

def YClean (s : State) : Prop := ∀ ab∈yPairs, s.basis ab.1=false ∧ s.basis ab.2=false

attribute [local irreducible] outer chain yPairs

theorem switchY (actual logical : State) (zero : YClean logical) :
    pullState duringY actual = logical ↔ pullState outer actual = logical :=
  clean_chain yPairs outer actual logical zero

theorem y_round (P : Program) (actual logical : State) (m : List Bool)
    (input : pullState outer actual = logical) (before : YClean logical) (after : YClean (run P m logical)) :
    pullState outer (run (encodeY P) m actual) = run P m logical := by
  apply (switchY _ _ after).mp
  rw [encodeY,run_rename _ duringY.injective, (switchY actual logical before).mpr input]

def retired := [4835,4836,4837,4838,4839]
def early := [4615,4616,4617,4618,4619]
def spare := [4915,4916,4917,4918,4919]

theorem outer_free (P : Program) (cold : ∀ w∈early,w∉wires P) :
    ∀ q∈retired, q∉wires (encode P) := by
  intro q hq used
  rw [encode,renameProgram_support] at used
  obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp used
  have inv := congrArg outer.symm eq
  rw [Equiv.symm_apply_apply] at inv
  exact cold w (inv ▸ (by decide +kernel : ∀ z∈retired,outer.symm z∈early) q hq) hw

theorem y_free (P : Program) (cold : ∀ w∈spare,w∉wires P) :
    ∀ q∈retired, q∉wires (encodeY P) := by
  intro q hq used
  rw [encodeY,renameProgram_support] at used
  obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp used
  have inv := congrArg duringY.symm eq
  rw [Equiv.symm_apply_apply] at inv
  exact cold w (inv ▸ (by decide +kernel : ∀ z∈retired,duringY.symm z∈spare) q hq) hw

def duringX : Equiv.Perm Wire := outer.trans (Equiv.swap 4616 4629)
def xOld : Equiv.Perm Wire := Equiv.swap 4836 4629
def integerFirst : Equiv.Perm Wire := chain [(4835,4615),(4837,4616),(4836,4629)]

private theorem equal_codes (a b : Equiv.Perm Wire) (xs zeroSites : List Wire)
    (table : ∀ q∈xs, a.symm q=b.symm q ∨ a.symm q∈zeroSites ∧ b.symm q∈zeroSites)
    (off : ∀q,q∉xs → a.symm q=b.symm q) (s : State)
    (zero : ∀q∈zeroSites,s.basis q=false) :
    pullState a.symm s = pullState b.symm s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (a.symm q) = s.basis (b.symm q)
    by_cases inside : q∈xs
    · rcases table q inside with eq|⟨ca,cb⟩
      · rw [eq]
      · rw [zero _ ca,zero _ cb]
    · rw [off q inside]

def switchX (P : Program) := renameProgram duringX P

theorem x_free (P : Program) (cold : ∀ w∈early,w∉wires P) :
    ∀ q∈retired, q∉wires (switchX P) := by
  intro q hq used
  rw [switchX,renameProgram_support] at used
  obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp used
  have inv := congrArg duringX.symm eq
  rw [Equiv.symm_apply_apply] at inv
  exact cold w (inv ▸ (by decide +kernel : ∀z∈retired,duringX.symm z∈early) q hq) hw

def changed := [4835,4836,4837,4838,4839,4615,4616,4617,4618,4619,4629]
def firstClean := [4835,4837,4838,4839,4615,4616,4617,4618,4619,4629]

private theorem mapoff (q : Wire) (hq : q∉changed) :
    duringX.symm q=q ∧ outer.symm q=q ∧ integerFirst.symm q=q ∧ xOld.symm q=q := by
  simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  rcases hq with ⟨a,b,c,d,e,f,g,h,i,j,k⟩
  simp [duringX,outer,integerFirst,xOld,chain,earlyPairs,Equiv.swap_apply_def, a,b,c,d,e,f,g,h,i,j,k]

theorem at_x_input (s : State) (zero : ∀q∈([4836,4629] : List Wire),s.basis q=false) :
    pullState outer.symm s = pullState duringX.symm s :=
  equal_codes outer duringX changed [4836,4629] (by decide +kernel)
    (fun _ h => (mapoff _ h).2.1.trans (mapoff _ h).1.symm) s zero

theorem at_x_output (s : State) (zero : ∀q∈firstClean,s.basis q=false) :
    pullState duringX.symm s = pullState integerFirst.symm s :=
  equal_codes duringX integerFirst changed firstClean (by decide +kernel)
    (fun _ h => (mapoff _ h).1.trans (mapoff _ h).2.2.1.symm) s zero

theorem square_to_integer (s : State)
    (zero : ∀q∈([4835,4837,4615,4616] : List Wire),s.basis q=false) :
    pullState xOld.symm s = pullState integerFirst.symm s :=
  equal_codes xOld integerFirst changed [4835,4837,4615,4616] (by decide +kernel)
    (fun _ h => (mapoff _ h).2.2.2.trans (mapoff _ h).2.2.1.symm) s zero

end ECDSAAdd.Entrant.Stair44PointMap

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates
open Arithmetic RecordedQuantum Challenge
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

private instance prizeStairArchiveIntegerLoad00 (i : Instr) : Decidable (PhysicalInstr (.gate i)) := by
  cases i <;> simp only [PhysicalInstr, ProperGate] <;> infer_instance

private instance prizeStairArchiveIntegerLoad01 (p : Program) : Decidable (GatePhysical p) := by
  unfold GatePhysical
  infer_instance

def integer_load0Block0 : Program := [
  .X 39,
  .CX 6 40,
  .CX 7 41,
  .CX 8 41,
  .CX 9 41,
  .CCX 40 41 42,
  .CX 9 41,
  .CX 8 41,
  .CX 7 41,
  .CX 6 40,
  .CX 4 40,
  .CX 5 40,
  .CX 8 40,
  .CX 6 41,
  .CX 8 41,
  .CX 9 41,
  .CX 42 41,
  .CCX 40 41 43,
  .CX 42 41,
  .CX 9 41,
  .CX 8 41,
  .CX 6 41,
  .CX 8 40,
  .CX 5 40,
  .CX 4 40,
  .CX 5 40,
  .CX 8 40,
  .CX 9 40,
  .CX 42 40,
  .CX 6 41,
  .CX 8 41,
  .CX 9 41,
  .CX 42 41,
  .CCX 40 41 44,
  .CX 42 41,
  .CX 9 41,
  .CX 8 41,
  .CX 6 41,
  .CX 42 40,
  .CX 9 40,
  .CX 8 40,
  .CX 5 40,
  .CX 0 40,
  .CX 0 41,
  .CX 2 41,
  .CCX 40 41 45,
  .CX 2 41,
  .CX 0 41
]

private theorem integer_load0Block0Ok : GatePhysical integer_load0Block0 ∧ toffoliCount integer_load0Block0 = 4 ∧ measurementCount integer_load0Block0 = 0 ∧ gateSlots integer_load0Block0 = 48 := by decide +kernel

def integer_load0Block1 : Program := [
  .CX 0 40,
  .CX 1 40,
  .CX 2 40,
  .CX 3 40,
  .CX 45 41,
  .CCX 40 41 46,
  .CX 45 41,
  .CX 3 40,
  .CX 2 40,
  .CX 1 40,
  .CX 0 40,
  .CX 45 40,
  .CX 1 41,
  .CX 4 41,
  .CX 5 41,
  .CX 6 41,
  .CX 43 41,
  .CX 45 41,
  .CX 46 41,
  .CCX 40 41 47,
  .CX 46 41,
  .CX 45 41,
  .CX 43 41,
  .CX 6 41,
  .CX 5 41,
  .CX 4 41,
  .CX 1 41,
  .CX 45 40,
  .CX 0 40,
  .CX 0 40,
  .CX 2 40,
  .CX 4 40,
  .CX 8 40,
  .CX 9 40,
  .CX 42 40,
  .CX 43 40,
  .CX 44 40,
  .CX 0 41,
  .CX 45 41,
  .CCX 40 41 48,
  .CX 45 41,
  .CX 0 41,
  .CX 44 40,
  .CX 43 40,
  .CX 42 40,
  .CX 9 40,
  .CX 8 40,
  .CX 4 40
]

private theorem integer_load0Block1Ok : GatePhysical integer_load0Block1 ∧ toffoliCount integer_load0Block1 = 3 ∧ measurementCount integer_load0Block1 = 0 ∧ gateSlots integer_load0Block1 = 48 := by decide +kernel

def integer_load0Block2 : Program := [
  .CX 2 40,
  .CX 0 40,
  .CX 0 40,
  .CX 45 40,
  .CX 2 41,
  .CX 3 41,
  .CX 4 41,
  .CX 5 41,
  .CX 6 41,
  .CX 7 41,
  .CX 8 41,
  .CX 42 41,
  .CX 43 41,
  .CX 46 41,
  .CCX 40 41 49,
  .CX 46 41,
  .CX 43 41,
  .CX 42 41,
  .CX 8 41,
  .CX 7 41,
  .CX 6 41,
  .CX 5 41,
  .CX 4 41,
  .CX 3 41,
  .CX 2 41,
  .CX 45 40,
  .CX 0 40,
  .CX 16 40,
  .CX 17 41,
  .CX 18 41,
  .CX 19 41,
  .CCX 40 41 50,
  .CX 19 41,
  .CX 18 41,
  .CX 17 41,
  .CX 16 40,
  .CX 14 40,
  .CX 15 40,
  .CX 18 40,
  .CX 16 41,
  .CX 18 41,
  .CX 19 41,
  .CX 50 41,
  .CCX 40 41 51,
  .CX 50 41,
  .CX 19 41,
  .CX 18 41,
  .CX 16 41
]

private theorem integer_load0Block2Ok : GatePhysical integer_load0Block2 ∧ toffoliCount integer_load0Block2 = 3 ∧ measurementCount integer_load0Block2 = 0 ∧ gateSlots integer_load0Block2 = 48 := by decide +kernel

def integer_load0Block3 : Program := [
  .CX 18 40,
  .CX 15 40,
  .CX 14 40,
  .CX 15 40,
  .CX 18 40,
  .CX 19 40,
  .CX 50 40,
  .CX 16 41,
  .CX 18 41,
  .CX 19 41,
  .CX 50 41,
  .CCX 40 41 52,
  .CX 50 41,
  .CX 19 41,
  .CX 18 41,
  .CX 16 41,
  .CX 50 40,
  .CX 19 40,
  .CX 18 40,
  .CX 15 40,
  .CX 10 40,
  .CX 10 41,
  .CX 12 41,
  .CCX 40 41 53,
  .CX 12 41,
  .CX 10 41,
  .CX 10 40,
  .CX 11 40,
  .CX 12 40,
  .CX 13 40,
  .CX 53 41,
  .CCX 40 41 54,
  .CX 53 41,
  .CX 13 40,
  .CX 12 40,
  .CX 11 40,
  .CX 10 40,
  .CX 53 40,
  .CX 11 41,
  .CX 14 41,
  .CX 15 41,
  .CX 16 41,
  .CX 51 41,
  .CX 53 41,
  .CX 54 41,
  .CCX 40 41 55,
  .CX 54 41,
  .CX 53 41
]

private theorem integer_load0Block3Ok : GatePhysical integer_load0Block3 ∧ toffoliCount integer_load0Block3 = 4 ∧ measurementCount integer_load0Block3 = 0 ∧ gateSlots integer_load0Block3 = 48 := by decide +kernel

def integer_load0Block4 : Program := [
  .CX 51 41,
  .CX 16 41,
  .CX 15 41,
  .CX 14 41,
  .CX 11 41,
  .CX 53 40,
  .CX 10 40,
  .CX 10 40,
  .CX 12 40,
  .CX 14 40,
  .CX 18 40,
  .CX 19 40,
  .CX 50 40,
  .CX 51 40,
  .CX 52 40,
  .CX 10 41,
  .CX 53 41,
  .CCX 40 41 56,
  .CX 53 41,
  .CX 10 41,
  .CX 52 40,
  .CX 51 40,
  .CX 50 40,
  .CX 19 40,
  .CX 18 40,
  .CX 14 40,
  .CX 12 40,
  .CX 10 40,
  .CX 10 40,
  .CX 53 40,
  .CX 12 41,
  .CX 13 41,
  .CX 14 41,
  .CX 15 41,
  .CX 16 41,
  .CX 17 41,
  .CX 18 41,
  .CX 50 41,
  .CX 51 41,
  .CX 54 41,
  .CCX 40 41 57,
  .CX 54 41,
  .CX 51 41,
  .CX 50 41,
  .CX 18 41,
  .CX 17 41,
  .CX 16 41,
  .CX 15 41
]

private theorem integer_load0Block4Ok : GatePhysical integer_load0Block4 ∧ toffoliCount integer_load0Block4 = 2 ∧ measurementCount integer_load0Block4 = 0 ∧ gateSlots integer_load0Block4 = 48 := by decide +kernel

def integer_load0Block5 : Program := [
  .CX 14 41,
  .CX 13 41,
  .CX 12 41,
  .CX 53 40,
  .CX 10 40,
  .CX 21 40,
  .CX 22 41,
  .CCX 40 41 58,
  .CX 22 41,
  .CX 21 40,
  .CX 0 40,
  .CX 22 41,
  .CCX 40 41 59,
  .CX 22 41,
  .CX 0 40,
  .CX 2 40,
  .CX 22 41,
  .CCX 40 41 60,
  .CX 22 41,
  .CX 2 40,
  .CX 12 40,
  .CX 21 41,
  .CCX 40 41 61,
  .CX 21 41,
  .CX 12 40,
  .CX 22 40,
  .CX 12 41,
  .CX 61 41,
  .CCX 40 41 62,
  .CX 61 41,
  .CX 12 41,
  .CX 22 40,
  .CX 8 40,
  .CX 21 41,
  .CCX 40 41 63,
  .CX 21 41,
  .CX 8 40,
  .CX 22 40,
  .CX 8 41,
  .CX 63 41,
  .CCX 40 41 64,
  .CX 63 41,
  .CX 8 41,
  .CX 22 40,
  .CX 4 40,
  .CX 21 41,
  .CCX 40 41 65,
  .CX 21 41
]

private theorem integer_load0Block5Ok : GatePhysical integer_load0Block5 ∧ toffoliCount integer_load0Block5 = 8 ∧ measurementCount integer_load0Block5 = 0 ∧ gateSlots integer_load0Block5 = 48 := by decide +kernel

def integer_load0Block6 : Program := [
  .CX 4 40,
  .CX 22 40,
  .CX 4 41,
  .CX 6 41,
  .CX 65 41,
  .CCX 40 41 66,
  .CX 65 41,
  .CX 6 41,
  .CX 4 41,
  .CX 22 40,
  .CX 6 40,
  .CX 21 41,
  .CCX 40 41 67,
  .CX 21 41,
  .CX 6 40,
  .CX 22 40,
  .CX 4 41,
  .CX 6 41,
  .CX 67 41,
  .CCX 40 41 68,
  .CX 67 41,
  .CX 6 41,
  .CX 4 41,
  .CX 22 40,
  .CX 10 40,
  .CX 21 41,
  .CCX 40 41 69,
  .CX 21 41,
  .CX 10 40,
  .CX 22 40,
  .CX 69 41,
  .CCX 40 41 70,
  .CX 69 41,
  .CX 22 40,
  .CX 22 40,
  .CX 0 41,
  .CX 65 41,
  .CCX 40 41 71,
  .CX 65 41,
  .CX 0 41,
  .CX 22 40,
  .CX 59 72,
  .CX 60 72,
  .CX 66 72,
  .CX 68 72,
  .CX 71 72,
  .CX 20 40,
  .CX 4 41
]

private theorem integer_load0Block6Ok : GatePhysical integer_load0Block6 ∧ toffoliCount integer_load0Block6 = 6 ∧ measurementCount integer_load0Block6 = 0 ∧ gateSlots integer_load0Block6 = 48 := by decide +kernel

def integer_load0Block7 : Program := [
  .CX 5 41,
  .CX 6 41,
  .CX 22 41,
  .CX 43 41,
  .CX 47 41,
  .CX 58 41,
  .CCX 40 41 73,
  .CX 58 41,
  .CX 47 41,
  .CX 43 41,
  .CX 22 41,
  .CX 6 41,
  .CX 5 41,
  .CX 4 41,
  .CX 20 40,
  .CX 20 40,
  .CX 4 41,
  .CX 9 41,
  .CX 42 41,
  .CX 44 41,
  .CX 59 41,
  .CCX 40 41 74,
  .CX 59 41,
  .CX 44 41,
  .CX 42 41,
  .CX 9 41,
  .CX 4 41,
  .CX 20 40,
  .CX 20 40,
  .CX 5 41,
  .CX 9 41,
  .CX 42 41,
  .CX 43 41,
  .CX 60 41,
  .CCX 40 41 75,
  .CX 60 41,
  .CX 43 41,
  .CX 42 41,
  .CX 9 41,
  .CX 5 41,
  .CX 20 40,
  .CX 20 40,
  .CX 0 41,
  .CX 4 41,
  .CX 8 41,
  .CX 9 41,
  .CX 42 41,
  .CX 43 41
]

private theorem integer_load0Block7Ok : GatePhysical integer_load0Block7 ∧ toffoliCount integer_load0Block7 = 3 ∧ measurementCount integer_load0Block7 = 0 ∧ gateSlots integer_load0Block7 = 48 := by decide +kernel

def integer_load0Block8 : Program := [
  .CX 44 41,
  .CX 45 41,
  .CX 48 41,
  .CX 62 41,
  .CCX 40 41 76,
  .CX 62 41,
  .CX 48 41,
  .CX 45 41,
  .CX 44 41,
  .CX 43 41,
  .CX 42 41,
  .CX 9 41,
  .CX 8 41,
  .CX 4 41,
  .CX 0 41,
  .CX 20 40,
  .CX 20 40,
  .CX 4 41,
  .CX 5 41,
  .CX 6 41,
  .CX 7 41,
  .CX 8 41,
  .CX 22 41,
  .CX 42 41,
  .CX 43 41,
  .CX 49 41,
  .CX 64 41,
  .CCX 40 41 77,
  .CX 64 41,
  .CX 49 41,
  .CX 43 41,
  .CX 42 41,
  .CX 22 41,
  .CX 8 41,
  .CX 7 41,
  .CX 6 41,
  .CX 5 41,
  .CX 4 41,
  .CX 20 40,
  .CX 20 40,
  .CX 0 41,
  .CX 2 41,
  .CX 3 41,
  .CX 6 41,
  .CX 45 41,
  .CX 46 41,
  .CX 49 41,
  .CX 66 41
]

private theorem integer_load0Block8Ok : GatePhysical integer_load0Block8 ∧ toffoliCount integer_load0Block8 = 2 ∧ measurementCount integer_load0Block8 = 0 ∧ gateSlots integer_load0Block8 = 48 := by decide +kernel

def integer_load0Block9 : Program := [
  .CCX 40 41 78,
  .CX 66 41,
  .CX 49 41,
  .CX 46 41,
  .CX 45 41,
  .CX 6 41,
  .CX 3 41,
  .CX 2 41,
  .CX 0 41,
  .CX 20 40,
  .CX 20 40,
  .CX 0 41,
  .CX 1 41,
  .CX 4 41,
  .CX 46 41,
  .CX 47 41,
  .CX 68 41,
  .CCX 40 41 79,
  .CX 68 41,
  .CX 47 41,
  .CX 46 41,
  .CX 4 41,
  .CX 1 41,
  .CX 0 41,
  .CX 20 40,
  .CX 20 40,
  .CX 0 41,
  .CX 2 41,
  .CX 10 41,
  .CX 48 41,
  .CX 70 41,
  .CCX 40 41 80,
  .CX 70 41,
  .CX 48 41,
  .CX 10 41,
  .CX 2 41,
  .CX 0 41,
  .CX 20 40,
  .CX 20 40,
  .CX 8 41,
  .CX 14 41,
  .CX 15 41,
  .CX 16 41,
  .CX 51 41,
  .CX 55 41,
  .CX 64 41,
  .CCX 40 41 81,
  .CX 64 41
]

private theorem integer_load0Block9Ok : GatePhysical integer_load0Block9 ∧ toffoliCount integer_load0Block9 = 4 ∧ measurementCount integer_load0Block9 = 0 ∧ gateSlots integer_load0Block9 = 48 := by decide +kernel

def integer_load0Block10 : Program := [
  .CX 55 41,
  .CX 51 41,
  .CX 16 41,
  .CX 15 41,
  .CX 14 41,
  .CX 8 41,
  .CX 20 40,
  .CX 20 40,
  .CX 12 41,
  .CX 14 41,
  .CX 19 41,
  .CX 50 41,
  .CX 52 41,
  .CX 62 41,
  .CCX 40 41 82,
  .CX 62 41,
  .CX 52 41,
  .CX 50 41,
  .CX 19 41,
  .CX 14 41,
  .CX 12 41,
  .CX 20 40,
  .CX 20 40,
  .CX 0 41,
  .CX 15 41,
  .CX 19 41,
  .CX 50 41,
  .CX 51 41,
  .CX 71 41,
  .CCX 40 41 83,
  .CX 71 41,
  .CX 51 41,
  .CX 50 41,
  .CX 19 41,
  .CX 15 41,
  .CX 0 41,
  .CX 20 40,
  .CX 20 40,
  .CX 2 41,
  .CX 10 41,
  .CX 14 41,
  .CX 18 41,
  .CX 19 41,
  .CX 50 41,
  .CX 51 41,
  .CX 52 41,
  .CX 53 41,
  .CX 56 41
]

private theorem integer_load0Block10Ok : GatePhysical integer_load0Block10 ∧ toffoliCount integer_load0Block10 = 2 ∧ measurementCount integer_load0Block10 = 0 ∧ gateSlots integer_load0Block10 = 48 := by decide +kernel

def integer_load0Block11 : Program := [
  .CX 72 41,
  .CCX 40 41 84,
  .CX 72 41,
  .CX 56 41,
  .CX 53 41,
  .CX 52 41,
  .CX 51 41,
  .CX 50 41,
  .CX 19 41,
  .CX 18 41,
  .CX 14 41,
  .CX 10 41,
  .CX 2 41,
  .CX 20 40,
  .CX 20 40,
  .CX 14 41,
  .CX 15 41,
  .CX 16 41,
  .CX 17 41,
  .CX 18 41,
  .CX 21 41,
  .CX 50 41,
  .CX 51 41,
  .CX 57 41,
  .CX 70 41,
  .CCX 40 41 85,
  .CX 70 41,
  .CX 57 41,
  .CX 51 41,
  .CX 50 41,
  .CX 21 41,
  .CX 18 41,
  .CX 17 41,
  .CX 16 41,
  .CX 15 41,
  .CX 14 41,
  .CX 20 40,
  .CX 20 40,
  .CX 10 41,
  .CX 12 41,
  .CX 13 41,
  .CX 14 41,
  .CX 53 41,
  .CX 54 41,
  .CX 57 41,
  .CCX 40 41 86,
  .CX 57 41,
  .CX 54 41
]

private theorem integer_load0Block11Ok : GatePhysical integer_load0Block11 ∧ toffoliCount integer_load0Block11 = 3 ∧ measurementCount integer_load0Block11 = 0 ∧ gateSlots integer_load0Block11 = 48 := by decide +kernel

def integer_load0Block12 : Program := [
  .CX 53 41,
  .CX 14 41,
  .CX 13 41,
  .CX 12 41,
  .CX 10 41,
  .CX 20 40,
  .CX 20 40,
  .CX 10 41,
  .CX 11 41,
  .CX 16 41,
  .CX 54 41,
  .CX 55 41,
  .CCX 40 41 87,
  .CX 55 41,
  .CX 54 41,
  .CX 16 41,
  .CX 11 41,
  .CX 10 41,
  .CX 20 40,
  .CX 20 40,
  .CX 10 41,
  .CX 12 41,
  .CX 18 41,
  .CX 56 41,
  .CCX 40 41 88,
  .CX 56 41,
  .CX 18 41,
  .CX 12 41,
  .CX 10 41,
  .CX 20 40,
  .CX 4 23,
  .CX 5 23,
  .CX 6 23,
  .CX 39 23,
  .CX 43 23,
  .CX 47 23,
  .CX 73 23,
  .CX 4 24,
  .CX 9 24,
  .CX 20 24,
  .CX 42 24,
  .CX 44 24,
  .CX 74 24,
  .CX 5 25,
  .CX 9 25,
  .CX 20 25,
  .CX 42 25,
  .CX 43 25
]

private theorem integer_load0Block12Ok : GatePhysical integer_load0Block12 ∧ toffoliCount integer_load0Block12 = 2 ∧ measurementCount integer_load0Block12 = 0 ∧ gateSlots integer_load0Block12 = 48 := by decide +kernel

def integer_load0Block13 : Program := [
  .CX 75 25,
  .CX 0 26,
  .CX 4 26,
  .CX 8 26,
  .CX 9 26,
  .CX 20 26,
  .CX 42 26,
  .CX 43 26,
  .CX 44 26,
  .CX 45 26,
  .CX 48 26,
  .CX 76 26,
  .CX 4 27,
  .CX 5 27,
  .CX 6 27,
  .CX 7 27,
  .CX 8 27,
  .CX 42 27,
  .CX 43 27,
  .CX 49 27,
  .CX 77 27,
  .CX 0 28,
  .CX 2 28,
  .CX 3 28,
  .CX 39 28,
  .CX 45 28,
  .CX 46 28,
  .CX 49 28,
  .CX 78 28,
  .CX 0 29,
  .CX 1 29,
  .CX 20 29,
  .CX 46 29,
  .CX 47 29,
  .CX 79 29,
  .CX 0 30,
  .CX 2 30,
  .CX 20 30,
  .CX 48 30,
  .CX 80 30,
  .CX 14 31,
  .CX 15 31,
  .CX 16 31,
  .CX 39 31,
  .CX 51 31,
  .CX 55 31,
  .CX 81 31,
  .CX 14 32
]

private theorem integer_load0Block13Ok : GatePhysical integer_load0Block13 ∧ toffoliCount integer_load0Block13 = 0 ∧ measurementCount integer_load0Block13 = 0 ∧ gateSlots integer_load0Block13 = 48 := by decide +kernel

def integer_load0Block14 : Program := [
  .CX 19 32,
  .CX 20 32,
  .CX 50 32,
  .CX 52 32,
  .CX 82 32,
  .CX 15 33,
  .CX 19 33,
  .CX 20 33,
  .CX 50 33,
  .CX 51 33,
  .CX 83 33,
  .CX 10 34,
  .CX 14 34,
  .CX 18 34,
  .CX 19 34,
  .CX 20 34,
  .CX 50 34,
  .CX 51 34,
  .CX 52 34,
  .CX 53 34,
  .CX 56 34,
  .CX 84 34,
  .CX 14 35,
  .CX 15 35,
  .CX 16 35,
  .CX 17 35,
  .CX 18 35,
  .CX 50 35,
  .CX 51 35,
  .CX 57 35,
  .CX 85 35,
  .CX 10 36,
  .CX 12 36,
  .CX 13 36,
  .CX 39 36,
  .CX 53 36,
  .CX 54 36,
  .CX 57 36,
  .CX 86 36,
  .CX 10 37,
  .CX 11 37,
  .CX 20 37,
  .CX 54 37,
  .CX 55 37,
  .CX 87 37,
  .CX 10 38,
  .CX 12 38,
  .CX 20 38
]

private theorem integer_load0Block14Ok : GatePhysical integer_load0Block14 ∧ toffoliCount integer_load0Block14 = 0 ∧ measurementCount integer_load0Block14 = 0 ∧ gateSlots integer_load0Block14 = 48 := by decide +kernel

def integer_load0Block15 : Program := [
  .CX 56 38,
  .CX 88 38,
  .CX 23 40,
  .CX 24 41,
  .CCX 40 41 89,
  .CX 24 41,
  .CX 23 40,
  .CX 25 40,
  .CX 89 41,
  .CCX 40 41 90,
  .CX 89 41,
  .CX 25 40,
  .CX 26 40,
  .CX 90 41,
  .CCX 40 41 91,
  .CX 90 41,
  .CX 26 40,
  .CX 20 92,
  .CX 22 92,
  .CX 91 92,
  .CX 23 40,
  .CX 26 41,
  .CCX 40 41 93,
  .CX 26 41,
  .CX 23 40,
  .CX 27 40,
  .CX 93 41,
  .CCX 40 41 94,
  .CX 93 41,
  .CX 27 40,
  .CX 28 40,
  .CX 94 41,
  .CCX 40 41 95,
  .CX 94 41,
  .CX 28 40,
  .CX 29 40,
  .CX 95 41,
  .CCX 40 41 96,
  .CX 95 41,
  .CX 29 40,
  .CX 58 97,
  .CX 31 40,
  .CX 32 41,
  .CCX 40 41 98,
  .CX 32 41,
  .CX 31 40,
  .CX 33 40,
  .CX 98 41
]

private theorem integer_load0Block15Ok : GatePhysical integer_load0Block15 ∧ toffoliCount integer_load0Block15 = 8 ∧ measurementCount integer_load0Block15 = 0 ∧ gateSlots integer_load0Block15 = 48 := by decide +kernel

def integer_load0Block16 : Program := [
  .CCX 40 41 99,
  .CX 98 41,
  .CX 33 40,
  .CX 34 40,
  .CX 99 41,
  .CCX 40 41 100,
  .CX 99 41,
  .CX 34 40,
  .CX 35 40,
  .CX 100 41,
  .CCX 40 41 101,
  .CX 100 41,
  .CX 35 40,
  .CX 22 102,
  .CX 58 102,
  .CX 100 102,
  .CX 101 102,
  .CX 21 103,
  .CX 58 103,
  .CX 24 40,
  .CX 33 40,
  .CX 91 41,
  .CX 92 41,
  .CCX 40 41 104,
  .CX 92 41,
  .CX 91 41,
  .CX 33 40,
  .CX 24 40,
  .CX 25 40,
  .CX 34 40,
  .CX 91 41,
  .CX 92 41,
  .CCX 40 41 105,
  .CX 92 41,
  .CX 91 41,
  .CX 34 40,
  .CX 25 40,
  .CX 59 106,
  .CX 71 106,
  .CX 91 40,
  .CX 92 40,
  .CX 28 41,
  .CX 29 41,
  .CX 106 41,
  .CCX 40 41 107,
  .CX 106 41,
  .CX 29 41,
  .CX 28 41
]

private theorem integer_load0Block16Ok : GatePhysical integer_load0Block16 ∧ toffoliCount integer_load0Block16 = 6 ∧ measurementCount integer_load0Block16 = 0 ∧ gateSlots integer_load0Block16 = 48 := by decide +kernel

def integer_load0Block17 : Program := [
  .CX 92 40,
  .CX 91 40,
  .CX 59 108,
  .CX 66 108,
  .CX 68 108,
  .CX 71 108,
  .CX 107 109,
  .CX 27 40,
  .CX 31 40,
  .CX 97 41,
  .CCX 40 41 110,
  .CX 97 41,
  .CX 31 40,
  .CX 27 40,
  .CX 91 40,
  .CX 92 40,
  .CX 27 41,
  .CX 31 41,
  .CX 110 41,
  .CCX 40 41 111,
  .CX 110 41,
  .CX 31 41,
  .CX 27 41,
  .CX 92 40,
  .CX 91 40,
  .CX 70 112,
  .CX 26 40,
  .CX 32 40,
  .CX 97 41,
  .CCX 40 41 114,
  .CX 97 41,
  .CX 32 40,
  .CX 26 40,
  .CX 91 40,
  .CX 92 40,
  .CX 26 41,
  .CX 32 41,
  .CX 114 41,
  .CCX 40 41 115,
  .CX 114 41,
  .CX 32 41,
  .CX 26 41,
  .CX 92 40,
  .CX 91 40,
  .CX 94 40,
  .CX 23 41,
  .CX 29 41,
  .CX 94 41
]

private theorem integer_load0Block17Ok : GatePhysical integer_load0Block17 ∧ toffoliCount integer_load0Block17 = 4 ∧ measurementCount integer_load0Block17 = 0 ∧ gateSlots integer_load0Block17 = 48 := by decide +kernel

def integer_load0Block18 : Program := [
  .CCX 40 41 116,
  .CX 94 41,
  .CX 29 41,
  .CX 23 41,
  .CX 94 40,
  .CX 94 40,
  .CX 26 41,
  .CX 30 41,
  .CX 94 41,
  .CCX 40 41 117,
  .CX 94 41,
  .CX 30 41,
  .CX 26 41,
  .CX 94 40,
  .CX 95 118,
  .CX 30 40,
  .CX 117 40,
  .CX 28 41,
  .CX 118 41,
  .CCX 40 41 119,
  .CX 118 41,
  .CX 28 41,
  .CX 117 40,
  .CX 30 40,
  .CX 119 40,
  .CX 28 41,
  .CX 29 41,
  .CX 116 41,
  .CX 118 41,
  .CX 119 41,
  .CCX 40 41 120,
  .CX 119 41,
  .CX 118 41,
  .CX 116 41,
  .CX 29 41,
  .CX 28 41,
  .CX 119 40,
  .CX 23 40,
  .CX 24 40,
  .CX 25 40,
  .CX 94 40,
  .CX 116 40,
  .CX 24 41,
  .CX 26 41,
  .CX 94 41,
  .CX 117 41,
  .CCX 40 41 121,
  .CX 117 41
]

private theorem integer_load0Block18Ok : GatePhysical integer_load0Block18 ∧ toffoliCount integer_load0Block18 = 5 ∧ measurementCount integer_load0Block18 = 0 ∧ gateSlots integer_load0Block18 = 48 := by decide +kernel

def integer_load0Block19 : Program := [
  .CX 94 41,
  .CX 26 41,
  .CX 24 41,
  .CX 116 40,
  .CX 94 40,
  .CX 25 40,
  .CX 24 40,
  .CX 23 40,
  .CX 24 40,
  .CX 25 40,
  .CX 26 40,
  .CX 94 40,
  .CX 117 40,
  .CX 23 41,
  .CX 24 41,
  .CX 25 41,
  .CX 94 41,
  .CX 116 41,
  .CX 121 41,
  .CCX 40 41 122,
  .CX 121 41,
  .CX 116 41,
  .CX 94 41,
  .CX 25 41,
  .CX 24 41,
  .CX 23 41,
  .CX 117 40,
  .CX 94 40,
  .CX 26 40,
  .CX 25 40,
  .CX 24 40,
  .CX 23 40,
  .CX 24 40,
  .CX 25 40,
  .CX 94 40,
  .CX 116 40,
  .CX 121 40,
  .CX 24 41,
  .CX 122 41,
  .CCX 40 41 123,
  .CX 122 41,
  .CX 24 41,
  .CX 121 40,
  .CX 116 40,
  .CX 94 40,
  .CX 25 40,
  .CX 24 40,
  .CX 23 40
]

private theorem integer_load0Block19Ok : GatePhysical integer_load0Block19 ∧ toffoliCount integer_load0Block19 = 2 ∧ measurementCount integer_load0Block19 = 0 ∧ gateSlots integer_load0Block19 = 48 := by decide +kernel

def integer_load0Block20 : Program := [
  .CX 23 40,
  .CX 26 40,
  .CX 116 40,
  .CX 117 40,
  .CX 122 40,
  .CX 23 41,
  .CX 24 41,
  .CX 25 41,
  .CX 27 41,
  .CX 116 41,
  .CX 118 41,
  .CX 121 41,
  .CX 123 41,
  .CCX 40 41 124,
  .CX 123 41,
  .CX 121 41,
  .CX 118 41,
  .CX 116 41,
  .CX 27 41,
  .CX 25 41,
  .CX 24 41,
  .CX 23 41,
  .CX 122 40,
  .CX 117 40,
  .CX 116 40,
  .CX 26 40,
  .CX 23 40,
  .CX 31 40,
  .CX 34 41,
  .CCX 40 41 125,
  .CX 34 41,
  .CX 31 40,
  .CX 35 40,
  .CX 125 41,
  .CCX 40 41 126,
  .CX 125 41,
  .CX 35 40,
  .CX 126 40,
  .CX 31 41,
  .CX 37 41,
  .CX 126 41,
  .CCX 40 41 127,
  .CX 126 41,
  .CX 37 41,
  .CX 31 41,
  .CX 126 40,
  .CX 126 40,
  .CX 34 41
]

private theorem integer_load0Block20Ok : GatePhysical integer_load0Block20 ∧ toffoliCount integer_load0Block20 = 4 ∧ measurementCount integer_load0Block20 = 0 ∧ gateSlots integer_load0Block20 = 48 := by decide +kernel

def integer_load0Block21 : Program := [
  .CX 38 41,
  .CX 126 41,
  .CCX 40 41 128,
  .CX 126 41,
  .CX 38 41,
  .CX 34 41,
  .CX 126 40,
  .CX 126 40,
  .CX 35 41,
  .CX 36 41,
  .CX 126 41,
  .CCX 40 41 129,
  .CX 126 41,
  .CX 36 41,
  .CX 35 41,
  .CX 126 40,
  .CX 38 40,
  .CX 128 40,
  .CX 36 41,
  .CX 129 41,
  .CCX 40 41 130,
  .CX 129 41,
  .CX 36 41,
  .CX 128 40,
  .CX 38 40,
  .CX 130 40,
  .CX 36 41,
  .CX 37 41,
  .CX 127 41,
  .CX 129 41,
  .CX 130 41,
  .CCX 40 41 131,
  .CX 130 41,
  .CX 129 41,
  .CX 127 41,
  .CX 37 41,
  .CX 36 41,
  .CX 130 40,
  .CX 31 40,
  .CX 32 40,
  .CX 33 40,
  .CX 126 40,
  .CX 127 40,
  .CX 32 41,
  .CX 34 41,
  .CX 126 41,
  .CX 128 41,
  .CCX 40 41 132
]

private theorem integer_load0Block21Ok : GatePhysical integer_load0Block21 ∧ toffoliCount integer_load0Block21 = 5 ∧ measurementCount integer_load0Block21 = 0 ∧ gateSlots integer_load0Block21 = 48 := by decide +kernel

def integer_load0Block22 : Program := [
  .CX 128 41,
  .CX 126 41,
  .CX 34 41,
  .CX 32 41,
  .CX 127 40,
  .CX 126 40,
  .CX 33 40,
  .CX 32 40,
  .CX 31 40,
  .CX 32 40,
  .CX 33 40,
  .CX 34 40,
  .CX 126 40,
  .CX 128 40,
  .CX 31 41,
  .CX 32 41,
  .CX 33 41,
  .CX 126 41,
  .CX 127 41,
  .CX 132 41,
  .CCX 40 41 133,
  .CX 132 41,
  .CX 127 41,
  .CX 126 41,
  .CX 33 41,
  .CX 32 41,
  .CX 31 41,
  .CX 128 40,
  .CX 126 40,
  .CX 34 40,
  .CX 33 40,
  .CX 32 40,
  .CX 31 40,
  .CX 32 40,
  .CX 33 40,
  .CX 126 40,
  .CX 127 40,
  .CX 132 40,
  .CX 32 41,
  .CX 133 41,
  .CCX 40 41 134,
  .CX 133 41,
  .CX 32 41,
  .CX 132 40,
  .CX 127 40,
  .CX 126 40,
  .CX 33 40,
  .CX 32 40
]

private theorem integer_load0Block22Ok : GatePhysical integer_load0Block22 ∧ toffoliCount integer_load0Block22 = 2 ∧ measurementCount integer_load0Block22 = 0 ∧ gateSlots integer_load0Block22 = 48 := by decide +kernel

def integer_load0Block23 : Program := [
  .CX 31 40,
  .CX 31 40,
  .CX 34 40,
  .CX 127 40,
  .CX 128 40,
  .CX 133 40,
  .CX 31 41,
  .CX 32 41,
  .CX 33 41,
  .CX 35 41,
  .CX 127 41,
  .CX 129 41,
  .CX 132 41,
  .CX 134 41,
  .CCX 40 41 135,
  .CX 134 41,
  .CX 132 41,
  .CX 129 41,
  .CX 127 41,
  .CX 35 41,
  .CX 33 41,
  .CX 32 41,
  .CX 31 41,
  .CX 133 40,
  .CX 128 40,
  .CX 127 40,
  .CX 34 40,
  .CX 31 40,
  .CX 0 136,
  .CX 20 136,
  .CX 94 136,
  .CX 119 136,
  .CX 91 40,
  .CX 92 40,
  .CX 100 40,
  .CX 101 40,
  .CX 102 40,
  .CX 103 40,
  .CX 91 41,
  .CX 92 41,
  .CX 94 41,
  .CX 97 41,
  .CX 100 41,
  .CX 101 41,
  .CX 102 41,
  .CX 119 41,
  .CX 136 41,
  .CCX 40 41 137
]

private theorem integer_load0Block23Ok : GatePhysical integer_load0Block23 ∧ toffoliCount integer_load0Block23 = 2 ∧ measurementCount integer_load0Block23 = 0 ∧ gateSlots integer_load0Block23 = 48 := by decide +kernel

def integer_load0Block24 : Program := [
  .CX 136 41,
  .CX 119 41,
  .CX 102 41,
  .CX 101 41,
  .CX 100 41,
  .CX 97 41,
  .CX 94 41,
  .CX 92 41,
  .CX 91 41,
  .CX 103 40,
  .CX 102 40,
  .CX 101 40,
  .CX 100 40,
  .CX 92 40,
  .CX 91 40,
  .CX 0 138,
  .CX 48 138,
  .CX 80 138,
  .CX 94 138,
  .CX 117 138,
  .CX 119 138,
  .CX 0 139,
  .CX 20 139,
  .CX 21 139,
  .CX 45 139,
  .CX 47 139,
  .CX 49 139,
  .CX 58 139,
  .CX 60 139,
  .CX 68 139,
  .CX 71 139,
  .CX 78 139,
  .CX 79 139,
  .CX 94 139,
  .CX 95 139,
  .CX 104 139,
  .CX 105 139,
  .CX 107 139,
  .CX 116 139,
  .CX 0 140,
  .CX 4 140,
  .CX 8 140,
  .CX 20 140,
  .CX 43 140,
  .CX 45 140,
  .CX 48 140,
  .CX 74 140,
  .CX 76 140
]

private theorem integer_load0Block24Ok : GatePhysical integer_load0Block24 ∧ toffoliCount integer_load0Block24 = 0 ∧ measurementCount integer_load0Block24 = 0 ∧ gateSlots integer_load0Block24 = 48 := by decide +kernel

def integer_load0Block25 : Program := [
  .CX 94 140,
  .CX 117 140,
  .CX 121 140,
  .CX 122 140,
  .CX 123 140,
  .CX 21 141,
  .CX 48 141,
  .CX 49 141,
  .CX 60 141,
  .CX 62 141,
  .CX 64 141,
  .CX 66 141,
  .CX 68 141,
  .CX 73 141,
  .CX 74 141,
  .CX 76 141,
  .CX 78 141,
  .CX 79 141,
  .CX 94 141,
  .CX 95 141,
  .CX 104 141,
  .CX 105 141,
  .CX 110 141,
  .CX 111 141,
  .CX 117 141,
  .CX 0 142,
  .CX 5 142,
  .CX 8 142,
  .CX 9 142,
  .CX 20 142,
  .CX 42 142,
  .CX 44 142,
  .CX 45 142,
  .CX 47 142,
  .CX 48 142,
  .CX 73 142,
  .CX 76 142,
  .CX 116 142,
  .CX 117 142,
  .CX 122 142,
  .CX 141 40,
  .CX 23 41,
  .CX 26 41,
  .CX 116 41,
  .CX 117 41,
  .CX 122 41,
  .CX 142 41,
  .CCX 40 41 143
]

private theorem integer_load0Block25Ok : GatePhysical integer_load0Block25 ∧ toffoliCount integer_load0Block25 = 1 ∧ measurementCount integer_load0Block25 = 0 ∧ gateSlots integer_load0Block25 = 48 := by decide +kernel

def integer_load0Block26 : Program := [
  .CX 142 41,
  .CX 122 41,
  .CX 117 41,
  .CX 116 41,
  .CX 26 41,
  .CX 23 41,
  .CX 141 40,
  .CX 0 144,
  .CX 4 144,
  .CX 9 144,
  .CX 42 144,
  .CX 43 144,
  .CX 44 144,
  .CX 45 144,
  .CX 48 144,
  .CX 76 144,
  .CX 94 144,
  .CX 117 144,
  .CX 122 144,
  .CX 123 144,
  .CX 20 145,
  .CX 21 145,
  .CX 48 145,
  .CX 59 145,
  .CX 62 145,
  .CX 64 145,
  .CX 68 145,
  .CX 71 145,
  .CX 73 145,
  .CX 74 145,
  .CX 75 145,
  .CX 76 145,
  .CX 77 145,
  .CX 78 145,
  .CX 79 145,
  .CX 104 145,
  .CX 105 145,
  .CX 107 145,
  .CX 117 145,
  .CX 10 146,
  .CX 20 146,
  .CX 126 146,
  .CX 130 146,
  .CX 145 40,
  .CX 91 41,
  .CX 92 41,
  .CX 97 41,
  .CX 100 41
]

private theorem integer_load0Block26Ok : GatePhysical integer_load0Block26 ∧ toffoliCount integer_load0Block26 = 0 ∧ measurementCount integer_load0Block26 = 0 ∧ gateSlots integer_load0Block26 = 48 := by decide +kernel

def integer_load0Block27 : Program := [
  .CX 101 41,
  .CX 102 41,
  .CX 126 41,
  .CX 130 41,
  .CX 146 41,
  .CCX 40 41 147,
  .CX 146 41,
  .CX 130 41,
  .CX 126 41,
  .CX 102 41,
  .CX 101 41,
  .CX 100 41,
  .CX 97 41,
  .CX 92 41,
  .CX 91 41,
  .CX 145 40,
  .CX 10 148,
  .CX 56 148,
  .CX 88 148,
  .CX 126 148,
  .CX 128 148,
  .CX 130 148,
  .CX 147 40,
  .CX 38 41,
  .CX 91 41,
  .CX 92 41,
  .CX 97 41,
  .CX 100 41,
  .CX 101 41,
  .CX 102 41,
  .CX 126 41,
  .CX 128 41,
  .CX 130 41,
  .CX 148 41,
  .CCX 40 41 149,
  .CX 148 41,
  .CX 130 41,
  .CX 128 41,
  .CX 126 41,
  .CX 102 41,
  .CX 101 41,
  .CX 100 41,
  .CX 97 41,
  .CX 92 41,
  .CX 91 41,
  .CX 38 41,
  .CX 147 40,
  .CX 10 150
]

private theorem integer_load0Block27Ok : GatePhysical integer_load0Block27 ∧ toffoliCount integer_load0Block27 = 2 ∧ measurementCount integer_load0Block27 = 0 ∧ gateSlots integer_load0Block27 = 48 := by decide +kernel

def integer_load0Block28 : Program := [
  .CX 14 150,
  .CX 18 150,
  .CX 20 150,
  .CX 51 150,
  .CX 53 150,
  .CX 56 150,
  .CX 82 150,
  .CX 84 150,
  .CX 126 150,
  .CX 128 150,
  .CX 132 150,
  .CX 133 150,
  .CX 134 150,
  .CX 149 40,
  .CX 32 41,
  .CX 34 41,
  .CX 91 41,
  .CX 92 41,
  .CX 97 41,
  .CX 100 41,
  .CX 101 41,
  .CX 102 41,
  .CX 126 41,
  .CX 128 41,
  .CX 132 41,
  .CX 133 41,
  .CX 134 41,
  .CX 150 41,
  .CCX 40 41 151,
  .CX 150 41,
  .CX 134 41,
  .CX 133 41,
  .CX 132 41,
  .CX 128 41,
  .CX 126 41,
  .CX 102 41,
  .CX 101 41,
  .CX 100 41,
  .CX 97 41,
  .CX 92 41,
  .CX 91 41,
  .CX 34 41,
  .CX 32 41,
  .CX 149 40,
  .CX 10 152,
  .CX 15 152,
  .CX 18 152,
  .CX 19 152
]

private theorem integer_load0Block28Ok : GatePhysical integer_load0Block28 ∧ toffoliCount integer_load0Block28 = 1 ∧ measurementCount integer_load0Block28 = 0 ∧ gateSlots integer_load0Block28 = 48 := by decide +kernel

def integer_load0Block29 : Program := [
  .CX 20 152,
  .CX 50 152,
  .CX 52 152,
  .CX 53 152,
  .CX 55 152,
  .CX 56 152,
  .CX 81 152,
  .CX 84 152,
  .CX 127 152,
  .CX 128 152,
  .CX 133 152,
  .CX 151 40,
  .CX 31 41,
  .CX 34 41,
  .CX 127 41,
  .CX 128 41,
  .CX 133 41,
  .CX 152 41,
  .CCX 40 41 153,
  .CX 152 41,
  .CX 133 41,
  .CX 128 41,
  .CX 127 41,
  .CX 34 41,
  .CX 31 41,
  .CX 151 40,
  .CX 10 154,
  .CX 14 154,
  .CX 19 154,
  .CX 50 154,
  .CX 51 154,
  .CX 52 154,
  .CX 53 154,
  .CX 56 154,
  .CX 84 154,
  .CX 126 154,
  .CX 128 154,
  .CX 133 154,
  .CX 134 154,
  .measureX 88 [] [.CZ 10 20, .CZ 12 20, .CZ 18 20, .CZ 20 56],
  .measureX 87 [] [.CZ 10 20, .CZ 11 20, .CZ 16 20, .CZ 20 54, .CZ 20 55],
  .measureX 86 [] [.CZ 10 20, .CZ 12 20, .CZ 13 20, .CZ 14 20, .CZ 20 53, .CZ 20 54, .CZ 20 57],
  .measureX 85 [] [.CZ 14 20, .CZ 15 20, .CZ 16 20, .CZ 17 20, .CZ 18 20, .CZ 20 21, .CZ 20 50, .CZ 20 51, .CZ 20 57, .CZ 20 70],
  .measureX 84 [] [.CZ 2 20, .CZ 10 20, .CZ 14 20, .CZ 18 20, .CZ 19 20, .CZ 20 50, .CZ 20 51, .CZ 20 52, .CZ 20 53, .CZ 20 56, .CZ 20 72],
  .measureX 83 [] [.CZ 0 20, .CZ 15 20, .CZ 19 20, .CZ 20 50, .CZ 20 51, .CZ 20 71],
  .measureX 82 [] [.CZ 12 20, .CZ 14 20, .CZ 19 20, .CZ 20 50, .CZ 20 52, .CZ 20 62],
  .measureX 81 [] [.CZ 8 20, .CZ 14 20, .CZ 15 20, .CZ 16 20, .CZ 20 51, .CZ 20 55, .CZ 20 64],
  .measureX 80 [] [.CZ 0 20, .CZ 2 20, .CZ 10 20, .CZ 20 48, .CZ 20 70]
]

private theorem integer_load0Block29Ok : GatePhysical integer_load0Block29 ∧ toffoliCount integer_load0Block29 = 1 ∧ measurementCount integer_load0Block29 = 9 ∧ gateSlots integer_load0Block29 = 109 := by decide +kernel

def integer_load0Block30 : Program := [
  .measureX 79 [] [.CZ 0 20, .CZ 1 20, .CZ 4 20, .CZ 20 46, .CZ 20 47, .CZ 20 68],
  .measureX 78 [] [.CZ 0 20, .CZ 2 20, .CZ 3 20, .CZ 6 20, .CZ 20 45, .CZ 20 46, .CZ 20 49, .CZ 20 66],
  .measureX 77 [] [.CZ 4 20, .CZ 5 20, .CZ 6 20, .CZ 7 20, .CZ 8 20, .CZ 20 22, .CZ 20 42, .CZ 20 43, .CZ 20 49, .CZ 20 64],
  .measureX 76 [] [.CZ 0 20, .CZ 4 20, .CZ 8 20, .CZ 9 20, .CZ 20 42, .CZ 20 43, .CZ 20 44, .CZ 20 45, .CZ 20 48, .CZ 20 62],
  .measureX 75 [] [.CZ 5 20, .CZ 9 20, .CZ 20 42, .CZ 20 43, .CZ 20 60],
  .measureX 74 [] [.CZ 4 20, .CZ 9 20, .CZ 20 42, .CZ 20 44, .CZ 20 59],
  .measureX 73 [] [.CZ 4 20, .CZ 5 20, .CZ 6 20, .CZ 20 22, .CZ 20 43, .CZ 20 47, .CZ 20 58],
  .measureX 72 [] [.CZ 2 22, .CZ 22 67],
  .measureX 71 [] [.CZ 0 22, .CZ 22 65],
  .measureX 70 [] [.CZ 22 69],
  .measureX 69 [] [.CZ 10 21],
  .measureX 68 [] [.CZ 4 22, .CZ 6 22, .CZ 22 67],
  .measureX 67 [] [.CZ 6 21],
  .measureX 66 [] [.CZ 4 22, .CZ 6 22, .CZ 22 65],
  .measureX 65 [] [.CZ 4 21],
  .measureX 64 [] [.CZ 8 22, .CZ 22 63],
  .measureX 63 [] [.CZ 8 21],
  .measureX 62 [] [.CZ 12 22, .CZ 22 61],
  .measureX 61 [] [.CZ 12 21],
  .measureX 60 [] [.CZ 2 22],
  .measureX 59 [] [.CZ 0 22],
  .measureX 58 [] [.CZ 21 22],
  .measureX 57 [] [.CZ 10 12, .CZ 10 13, .CZ 10 14, .CZ 10 15, .CZ 10 16, .CZ 10 17, .CZ 10 18, .CZ 10 50, .CZ 10 51, .CZ 10 54, .CZ 12 53, .CZ 13 53, .CZ 14 53, .CZ 15 53, .CZ 16 53, .CZ 17 53, .CZ 18 53, .CZ 50 53, .CZ 51 53, .CZ 53 54],
  .measureX 56 [] [.Z 10, .CZ 10 12, .CZ 10 14, .CZ 10 18, .CZ 10 19, .CZ 10 50, .CZ 10 51, .CZ 10 52, .CZ 10 53, .CZ 12 53, .CZ 14 53, .CZ 18 53, .CZ 19 53, .CZ 50 53, .CZ 51 53, .CZ 52 53],
  .measureX 55 [] [.CZ 10 11, .CZ 10 14, .CZ 10 15, .CZ 10 16, .CZ 10 51, .CZ 10 53, .CZ 10 54, .CZ 11 53, .CZ 14 53, .CZ 15 53, .CZ 16 53, .CZ 51 53, .Z 53, .CZ 53 54],
  .measureX 54 [] [.CZ 11 53, .CZ 12 53, .CZ 13 53],
  .measureX 53 [] [.Z 10, .CZ 10 12],
  .measureX 52 [] [.CZ 15 16, .CZ 15 18, .CZ 15 19, .CZ 15 50, .CZ 16 18, .CZ 16 19, .CZ 16 50, .Z 18, .Z 19, .Z 50],
  .measureX 51 [] [.CZ 14 16, .CZ 14 18, .CZ 14 19, .CZ 14 50, .CZ 15 16, .CZ 15 18, .CZ 15 19, .CZ 15 50, .CZ 16 18, .Z 18, .CZ 18 19, .CZ 18 50],
  .measureX 50 [] [.CZ 16 17, .CZ 16 18, .CZ 16 19],
  .measureX 49 [] [.CZ 0 2, .CZ 0 3, .CZ 0 4, .CZ 0 5, .CZ 0 6, .CZ 0 7, .CZ 0 8, .CZ 0 42, .CZ 0 43, .CZ 0 46, .CZ 2 45, .CZ 3 45, .CZ 4 45, .CZ 5 45, .CZ 6 45, .CZ 7 45, .CZ 8 45, .CZ 42 45, .CZ 43 45, .CZ 45 46],
  .measureX 48 [] [.Z 0, .CZ 0 2, .CZ 0 4, .CZ 0 8, .CZ 0 9, .CZ 0 42, .CZ 0 43, .CZ 0 44, .CZ 0 45, .CZ 2 45, .CZ 4 45, .CZ 8 45, .CZ 9 45, .CZ 42 45, .CZ 43 45, .CZ 44 45],
  .measureX 47 [] [.CZ 0 1, .CZ 0 4, .CZ 0 5, .CZ 0 6, .CZ 0 43, .CZ 0 45, .CZ 0 46, .CZ 1 45, .CZ 4 45, .CZ 5 45, .CZ 6 45, .CZ 43 45, .Z 45, .CZ 45 46],
  .measureX 46 [] [.CZ 1 45, .CZ 2 45, .CZ 3 45],
  .measureX 45 [] [.Z 0, .CZ 0 2],
  .measureX 44 [] [.CZ 5 6, .CZ 5 8, .CZ 5 9, .CZ 5 42, .CZ 6 8, .CZ 6 9, .CZ 6 42, .Z 8, .Z 9, .Z 42],
  .measureX 43 [] [.CZ 4 6, .CZ 4 8, .CZ 4 9, .CZ 4 42, .CZ 5 6, .CZ 5 8, .CZ 5 9, .CZ 5 42, .CZ 6 8, .Z 8, .CZ 8 9, .CZ 8 42],
  .measureX 42 [] [.CZ 6 7, .CZ 6 8, .CZ 6 9],
  .measureX 0 [] [.Z 91, .Z 92, .Z 94, .Z 97, .Z 100, .Z 101, .Z 102, .Z 119, .Z 136],
  .measureX 1 [] [.Z 29, .CZ 29 91, .CZ 29 92, .CZ 29 97, .CZ 29 100, .CZ 29 101, .CZ 29 102, .Z 91, .CZ 91 116, .CZ 91 120, .Z 92, .CZ 92 116, .CZ 92 120, .CZ 97 116, .CZ 97 120, .Z 100, .CZ 100 116, .CZ 100 120, .Z 101, .CZ 101 116, .CZ 101 120, .Z 102, .CZ 102 116, .CZ 102 120, .Z 103, .Z 116, .Z 120, .Z 137],
  .measureX 2 [] [.Z 30, .Z 91, .Z 92, .Z 94, .Z 97, .Z 100, .Z 101, .Z 102, .Z 117, .Z 119, .Z 138],
  .measureX 3 [] [.Z 39, .Z 28, .CZ 28 91, .CZ 28 92, .CZ 28 97, .CZ 28 100, .CZ 28 101, .CZ 28 102, .Z 30, .CZ 30 91, .CZ 30 92, .CZ 30 97, .CZ 30 100, .CZ 30 101, .CZ 30 102, .Z 91, .CZ 91 94, .CZ 91 117, .CZ 91 118, .CZ 91 120, .Z 92, .CZ 92 94, .CZ 92 117, .CZ 92 118, .CZ 92 120, .Z 94, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .Z 97, .CZ 97 117, .CZ 97 118, .CZ 97 120, .Z 100, .CZ 100 117, .CZ 100 118, .CZ 100 120, .Z 101, .CZ 101 117, .CZ 101 118, .CZ 101 120, .Z 102, .CZ 102 117, .CZ 102 118, .CZ 102 120, .Z 117, .Z 118, .Z 120, .Z 137, .Z 139],
  .measureX 4 [] [.Z 24, .Z 26, .Z 91, .Z 92, .Z 94, .Z 97, .Z 100, .Z 101, .Z 102, .Z 117, .Z 121, .Z 122, .Z 123, .Z 140],
  .measureX 5 [] [.CZ 91 121, .CZ 91 122, .CZ 92 121, .CZ 92 122, .CZ 97 121, .CZ 97 122, .CZ 100 121, .CZ 100 122, .CZ 101 121, .CZ 101 122, .CZ 102 121, .CZ 102 122, .Z 121, .Z 122, .Z 139, .Z 141],
  .measureX 6 [] [.Z 39, .Z 23, .Z 26, .Z 116, .Z 117, .Z 122, .Z 142],
  .measureX 7 [] [.Z 23, .CZ 23 91, .CZ 23 92, .CZ 23 97, .CZ 23 100, .CZ 23 101, .CZ 23 102, .Z 24, .CZ 24 91, .CZ 24 92, .CZ 24 97, .CZ 24 100, .CZ 24 101, .CZ 24 102, .Z 25, .CZ 25 91, .CZ 25 92, .CZ 25 97, .CZ 25 100, .CZ 25 101, .CZ 25 102, .CZ 91 94, .CZ 91 116, .CZ 91 121, .CZ 91 124, .CZ 92 94, .CZ 92 116, .CZ 92 121, .CZ 92 124, .Z 94, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 97 116, .CZ 97 121, .CZ 97 124, .CZ 100 116, .CZ 100 121, .CZ 100 124, .CZ 101 116, .CZ 101 121, .CZ 101 124, .CZ 102 116, .CZ 102 121, .CZ 102 124, .Z 116, .Z 121, .Z 124, .Z 143],
  .measureX 8 [] [.Z 26, .Z 91, .Z 92, .Z 94, .Z 97, .Z 100, .Z 101, .Z 102, .Z 117, .Z 122, .Z 123, .Z 144],
  .measureX 9 [] [.Z 39, .Z 26, .CZ 26 91, .CZ 26 92, .CZ 26 97, .CZ 26 100, .CZ 26 101, .CZ 26 102, .Z 27, .CZ 27 91, .CZ 27 92, .CZ 27 97, .CZ 27 100, .CZ 27 101, .CZ 27 102, .Z 91, .CZ 91 117, .CZ 91 118, .CZ 91 122, .CZ 91 124, .Z 92, .CZ 92 117, .CZ 92 118, .CZ 92 122, .CZ 92 124, .Z 97, .CZ 97 117, .CZ 97 118, .CZ 97 122, .CZ 97 124, .Z 100, .CZ 100 117, .CZ 100 118, .CZ 100 122, .CZ 100 124, .Z 101, .CZ 101 117, .CZ 101 118, .CZ 101 122, .CZ 101 124, .Z 102, .CZ 102 117, .CZ 102 118, .CZ 102 122, .CZ 102 124, .Z 117, .Z 118, .Z 122, .Z 124, .Z 141, .Z 143, .Z 145]
]

private theorem integer_load0Block30Ok : GatePhysical integer_load0Block30 ∧ toffoliCount integer_load0Block30 = 0 ∧ measurementCount integer_load0Block30 = 48 ∧ gateSlots integer_load0Block30 = 532 := by decide +kernel

def integer_load0Block31 : Program := [
  .measureX 10 [] [.Z 91, .Z 92, .Z 97, .Z 100, .Z 101, .Z 102, .Z 126, .Z 130, .Z 146],
  .measureX 11 [] [.Z 37, .CZ 37 91, .CZ 37 92, .CZ 37 97, .CZ 37 100, .CZ 37 101, .CZ 37 102, .CZ 91 127, .CZ 91 131, .CZ 92 127, .CZ 92 131, .CZ 97 127, .CZ 97 131, .CZ 100 127, .CZ 100 131, .CZ 101 127, .CZ 101 131, .CZ 102 127, .CZ 102 131, .Z 127, .Z 131, .Z 145, .Z 147],
  .measureX 12 [] [.Z 38, .Z 91, .Z 92, .Z 97, .Z 100, .Z 101, .Z 102, .Z 126, .Z 128, .Z 130, .Z 148],
  .measureX 13 [] [.Z 39, .Z 36, .CZ 36 91, .CZ 36 92, .CZ 36 97, .CZ 36 100, .CZ 36 101, .CZ 36 102, .Z 38, .CZ 38 91, .CZ 38 92, .CZ 38 97, .CZ 38 100, .CZ 38 101, .CZ 38 102, .Z 91, .CZ 91 126, .CZ 91 128, .CZ 91 129, .CZ 91 131, .Z 92, .CZ 92 126, .CZ 92 128, .CZ 92 129, .CZ 92 131, .Z 97, .CZ 97 126, .CZ 97 128, .CZ 97 129, .CZ 97 131, .Z 100, .CZ 100 126, .CZ 100 128, .CZ 100 129, .CZ 100 131, .Z 101, .CZ 101 126, .CZ 101 128, .CZ 101 129, .CZ 101 131, .Z 102, .CZ 102 126, .CZ 102 128, .CZ 102 129, .CZ 102 131, .Z 126, .Z 128, .Z 129, .Z 131, .Z 147, .Z 149],
  .measureX 14 [] [.Z 32, .Z 34, .Z 91, .Z 92, .Z 97, .Z 100, .Z 101, .Z 102, .Z 126, .Z 128, .Z 132, .Z 133, .Z 134, .Z 150],
  .measureX 15 [] [.CZ 91 132, .CZ 91 133, .CZ 92 132, .CZ 92 133, .CZ 97 132, .CZ 97 133, .CZ 100 132, .CZ 100 133, .CZ 101 132, .CZ 101 133, .CZ 102 132, .CZ 102 133, .Z 132, .Z 133, .Z 149, .Z 151],
  .measureX 16 [] [.Z 39, .Z 31, .Z 34, .Z 127, .Z 128, .Z 133, .Z 152],
  .measureX 17 [] [.Z 31, .CZ 31 91, .CZ 31 92, .CZ 31 97, .CZ 31 100, .CZ 31 101, .CZ 31 102, .Z 32, .CZ 32 91, .CZ 32 92, .CZ 32 97, .CZ 32 100, .CZ 32 101, .CZ 32 102, .Z 33, .CZ 33 91, .CZ 33 92, .CZ 33 97, .CZ 33 100, .CZ 33 101, .CZ 33 102, .CZ 91 126, .CZ 91 127, .CZ 91 132, .CZ 91 135, .CZ 92 126, .CZ 92 127, .CZ 92 132, .CZ 92 135, .CZ 97 126, .CZ 97 127, .CZ 97 132, .CZ 97 135, .CZ 100 126, .CZ 100 127, .CZ 100 132, .CZ 100 135, .CZ 101 126, .CZ 101 127, .CZ 101 132, .CZ 101 135, .CZ 102 126, .CZ 102 127, .CZ 102 132, .CZ 102 135, .Z 126, .Z 127, .Z 132, .Z 135, .Z 153],
  .measureX 18 [] [.Z 34, .Z 91, .Z 92, .Z 97, .Z 100, .Z 101, .Z 102, .Z 126, .Z 128, .Z 133, .Z 134, .Z 154],
  .measureX 19 [] [.Z 39, .Z 34, .CZ 34 91, .CZ 34 92, .CZ 34 97, .CZ 34 100, .CZ 34 101, .CZ 34 102, .CZ 34 151, .CZ 34 153, .Z 35, .CZ 35 91, .CZ 35 92, .CZ 35 97, .CZ 35 100, .CZ 35 101, .CZ 35 102, .Z 91, .CZ 91 128, .CZ 91 129, .CZ 91 133, .CZ 91 135, .CZ 91 151, .CZ 91 153, .Z 92, .CZ 92 128, .CZ 92 129, .CZ 92 133, .CZ 92 135, .CZ 92 151, .CZ 92 153, .Z 97, .CZ 97 128, .CZ 97 129, .CZ 97 133, .CZ 97 135, .CZ 97 151, .CZ 97 153, .Z 100, .CZ 100 128, .CZ 100 129, .CZ 100 133, .CZ 100 135, .CZ 100 151, .CZ 100 153, .Z 101, .CZ 101 128, .CZ 101 129, .CZ 101 133, .CZ 101 135, .CZ 101 151, .CZ 101 153, .Z 102, .CZ 102 128, .CZ 102 129, .CZ 102 133, .CZ 102 135, .CZ 102 151, .CZ 102 153, .CZ 126 151, .CZ 126 153, .Z 128, .CZ 128 151, .CZ 128 153, .Z 129, .Z 133, .CZ 133 151, .CZ 133 153, .CZ 134 151, .CZ 134 153, .Z 135, .Z 151, .CZ 151 154, .Z 153, .CZ 153 154],
  .measureX 20 [] [.Z 91, .Z 92, .Z 97, .Z 100, .Z 101, .Z 102],
  .measureX 21 [] [.Z 97, .Z 103],
  .measureX 22 [] [.Z 97, .Z 100, .Z 101, .Z 102],
  .measureX 154 [] [.CZ 34 91, .CZ 34 92, .CZ 34 97, .CZ 34 100, .CZ 34 101, .CZ 34 102, .CZ 38 91, .CZ 38 92, .CZ 38 97, .CZ 38 100, .CZ 38 101, .CZ 38 102, .CZ 91 126, .CZ 91 128, .CZ 91 133, .CZ 91 134, .CZ 92 126, .CZ 92 128, .CZ 92 133, .CZ 92 134, .CZ 97 126, .CZ 97 128, .CZ 97 133, .CZ 97 134, .CZ 100 126, .CZ 100 128, .CZ 100 133, .CZ 100 134, .CZ 101 126, .CZ 101 128, .CZ 101 133, .CZ 101 134, .CZ 102 126, .CZ 102 128, .CZ 102 133, .CZ 102 134],
  .measureX 153 [] [.CZ 31 151, .CZ 34 151, .CZ 127 151, .CZ 128 151, .CZ 133 151, .CZ 151 152],
  .measureX 152 [] [.CZ 31 91, .CZ 31 92, .CZ 31 97, .CZ 31 100, .CZ 31 101, .CZ 31 102, .CZ 34 91, .CZ 34 92, .CZ 34 97, .CZ 34 100, .CZ 34 101, .CZ 34 102, .CZ 37 91, .CZ 37 92, .CZ 37 97, .CZ 37 100, .CZ 37 101, .CZ 37 102, .CZ 91 127, .CZ 91 128, .CZ 91 133, .CZ 92 127, .CZ 92 128, .CZ 92 133, .CZ 97 127, .CZ 97 128, .CZ 97 133, .CZ 100 127, .CZ 100 128, .CZ 100 133, .CZ 101 127, .CZ 101 128, .CZ 101 133, .CZ 102 127, .CZ 102 128, .CZ 102 133],
  .measureX 151 [] [.CZ 32 149, .CZ 34 149, .CZ 91 149, .CZ 92 149, .CZ 97 149, .CZ 100 149, .CZ 101 149, .CZ 102 149, .CZ 126 149, .CZ 128 149, .CZ 132 149, .CZ 133 149, .CZ 134 149, .CZ 149 150],
  .measureX 150 [] [.CZ 32 91, .CZ 32 92, .CZ 32 97, .CZ 32 100, .CZ 32 101, .CZ 32 102, .CZ 34 91, .CZ 34 92, .CZ 34 97, .CZ 34 100, .CZ 34 101, .CZ 34 102, .CZ 36 91, .CZ 36 92, .CZ 36 97, .CZ 36 100, .CZ 36 101, .CZ 36 102, .CZ 91 126, .CZ 91 128, .CZ 91 132, .CZ 91 133, .CZ 91 134, .CZ 92 126, .CZ 92 128, .CZ 92 132, .CZ 92 133, .CZ 92 134, .CZ 97 126, .CZ 97 128, .CZ 97 132, .CZ 97 133, .CZ 97 134, .CZ 100 126, .CZ 100 128, .CZ 100 132, .CZ 100 133, .CZ 100 134, .CZ 101 126, .CZ 101 128, .CZ 101 132, .CZ 101 133, .CZ 101 134, .CZ 102 126, .CZ 102 128, .CZ 102 132, .CZ 102 133, .CZ 102 134],
  .measureX 149 [] [.CZ 38 147, .CZ 91 147, .CZ 92 147, .CZ 97 147, .CZ 100 147, .CZ 101 147, .CZ 102 147, .CZ 126 147, .CZ 128 147, .CZ 130 147, .CZ 147 148],
  .measureX 148 [] [.CZ 26 91, .CZ 26 92, .CZ 26 97, .CZ 26 100, .CZ 26 101, .CZ 26 102, .CZ 38 91, .CZ 38 92, .CZ 38 97, .CZ 38 100, .CZ 38 101, .CZ 38 102, .CZ 91 114, .CZ 91 115, .CZ 91 126, .CZ 91 128, .CZ 91 130, .CZ 92 114, .CZ 92 115, .CZ 92 126, .CZ 92 128, .CZ 92 130, .CZ 97 114, .CZ 97 115, .CZ 97 126, .CZ 97 128, .CZ 97 130, .CZ 100 114, .CZ 100 115, .CZ 100 126, .CZ 100 128, .CZ 100 130, .CZ 101 114, .CZ 101 115, .CZ 101 126, .CZ 101 128, .CZ 101 130, .CZ 102 114, .CZ 102 115, .CZ 102 126, .CZ 102 128, .CZ 102 130],
  .measureX 147 [] [.CZ 91 145, .CZ 92 145, .CZ 97 145, .CZ 100 145, .CZ 101 145, .CZ 102 145, .CZ 126 145, .CZ 130 145, .CZ 145 146],
  .measureX 146 [] [.CZ 30 91, .CZ 30 92, .CZ 30 97, .CZ 30 100, .CZ 30 101, .CZ 30 102, .CZ 91 112, .CZ 91 113, .CZ 91 126, .CZ 91 130, .CZ 92 112, .CZ 92 113, .CZ 92 126, .CZ 92 130, .CZ 97 112, .CZ 97 113, .CZ 97 126, .CZ 97 130, .CZ 100 112, .CZ 100 113, .CZ 100 126, .CZ 100 130, .CZ 101 112, .CZ 101 113, .CZ 101 126, .CZ 101 130, .CZ 102 112, .CZ 102 113, .CZ 102 126, .CZ 102 130],
  .measureX 145 [] [.CZ 26 141, .CZ 26 143, .CZ 91 141, .CZ 91 143, .CZ 92 141, .CZ 92 143, .CZ 94 141, .CZ 94 143, .CZ 97 141, .CZ 97 143, .CZ 100 141, .CZ 100 143, .CZ 101 141, .CZ 101 143, .CZ 102 141, .CZ 102 143, .CZ 117 141, .CZ 117 143, .CZ 122 141, .CZ 122 143, .CZ 123 141, .CZ 123 143, .CZ 141 144, .CZ 143 144],
  .measureX 144 [] [.CZ 26 91, .CZ 26 92, .CZ 26 97, .CZ 26 100, .CZ 26 101, .CZ 26 102, .CZ 27 91, .CZ 27 92, .CZ 27 97, .CZ 27 100, .CZ 27 101, .CZ 27 102, .CZ 91 94, .CZ 91 110, .CZ 91 111, .CZ 91 117, .CZ 91 122, .CZ 91 123, .CZ 92 94, .CZ 92 110, .CZ 92 111, .CZ 92 117, .CZ 92 122, .CZ 92 123, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 97 110, .CZ 97 111, .CZ 97 117, .CZ 97 122, .CZ 97 123, .CZ 100 110, .CZ 100 111, .CZ 100 117, .CZ 100 122, .CZ 100 123, .CZ 101 110, .CZ 101 111, .CZ 101 117, .CZ 101 122, .CZ 101 123, .CZ 102 110, .CZ 102 111, .CZ 102 117, .CZ 102 122, .CZ 102 123],
  .measureX 143 [] [.CZ 23 141, .CZ 26 141, .CZ 116 141, .CZ 117 141, .CZ 122 141, .CZ 141 142],
  .measureX 142 [] [.CZ 23 91, .CZ 23 92, .CZ 23 97, .CZ 23 100, .CZ 23 101, .CZ 23 102, .CZ 26 91, .CZ 26 92, .CZ 26 97, .CZ 26 100, .CZ 26 101, .CZ 26 102, .CZ 29 91, .CZ 29 92, .CZ 29 97, .CZ 29 100, .CZ 29 101, .CZ 29 102, .CZ 91 108, .CZ 91 109, .CZ 91 116, .CZ 91 117, .CZ 91 122, .CZ 92 108, .CZ 92 109, .CZ 92 116, .CZ 92 117, .CZ 92 122, .CZ 97 108, .CZ 97 109, .CZ 97 116, .CZ 97 117, .CZ 97 122, .CZ 100 108, .CZ 100 109, .CZ 100 116, .CZ 100 117, .CZ 100 122, .CZ 101 108, .CZ 101 109, .CZ 101 116, .CZ 101 117, .CZ 101 122, .CZ 102 108, .CZ 102 109, .CZ 102 116, .CZ 102 117, .CZ 102 122],
  .measureX 141 [] [.CZ 24 139, .CZ 26 139, .CZ 91 139, .CZ 92 139, .CZ 94 139, .CZ 97 139, .CZ 100 139, .CZ 101 139, .CZ 102 139, .CZ 117 139, .CZ 121 139, .CZ 122 139, .CZ 123 139, .CZ 139 140],
  .measureX 140 [] [.CZ 24 91, .CZ 24 92, .CZ 24 97, .CZ 24 100, .CZ 24 101, .CZ 24 102, .CZ 26 91, .CZ 26 92, .CZ 26 97, .CZ 26 100, .CZ 26 101, .CZ 26 102, .CZ 28 91, .CZ 28 92, .CZ 28 97, .CZ 28 100, .CZ 28 101, .CZ 28 102, .CZ 91 94, .CZ 91 106, .CZ 91 107, .CZ 91 117, .CZ 91 121, .CZ 91 122, .CZ 91 123, .CZ 92 94, .CZ 92 106, .CZ 92 107, .CZ 92 117, .CZ 92 121, .CZ 92 122, .CZ 92 123, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 97 106, .CZ 97 107, .CZ 97 117, .CZ 97 121, .CZ 97 122, .CZ 97 123, .CZ 100 106, .CZ 100 107, .CZ 100 117, .CZ 100 121, .CZ 100 122, .CZ 100 123, .CZ 101 106, .CZ 101 107, .CZ 101 117, .CZ 101 121, .CZ 101 122, .CZ 101 123, .CZ 102 106, .CZ 102 107, .CZ 102 117, .CZ 102 121, .CZ 102 122, .CZ 102 123],
  .measureX 139 [] [.CZ 30 137, .CZ 91 137, .CZ 92 137, .CZ 94 137, .CZ 97 137, .CZ 100 137, .CZ 101 137, .CZ 102 137, .CZ 117 137, .CZ 119 137, .CZ 137 138],
  .measureX 138 [] [.CZ 25 91, .CZ 25 92, .CZ 25 97, .CZ 25 100, .CZ 25 101, .CZ 25 102, .CZ 30 91, .CZ 30 92, .CZ 30 97, .CZ 30 100, .CZ 30 101, .CZ 30 102, .CZ 91 94, .CZ 91 105, .CZ 91 117, .CZ 91 119, .CZ 92 94, .CZ 92 105, .CZ 92 117, .CZ 92 119, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 97 105, .CZ 97 117, .CZ 97 119, .CZ 100 105, .CZ 100 117, .CZ 100 119, .CZ 101 105, .CZ 101 117, .CZ 101 119, .CZ 102 105, .CZ 102 117, .CZ 102 119],
  .measureX 137 [] [.Z 91, .CZ 91 94, .CZ 91 97, .CZ 91 103, .CZ 91 119, .CZ 91 136, .Z 92, .CZ 92 94, .CZ 92 97, .CZ 92 103, .CZ 92 119, .CZ 92 136, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 94 103, .CZ 97 100, .CZ 97 101, .CZ 97 102, .CZ 97 103, .Z 100, .CZ 100 103, .CZ 100 119, .CZ 100 136, .Z 101, .CZ 101 103, .CZ 101 119, .CZ 101 136, .Z 102, .CZ 102 103, .CZ 102 119, .CZ 102 136, .CZ 103 119, .CZ 103 136],
  .measureX 136 [] [.CZ 24 91, .CZ 24 92, .CZ 24 97, .CZ 24 100, .CZ 24 101, .CZ 24 102, .CZ 91 94, .CZ 91 104, .CZ 91 119, .CZ 92 94, .CZ 92 104, .CZ 92 119, .CZ 94 97, .CZ 94 100, .CZ 94 101, .CZ 94 102, .CZ 97 104, .CZ 97 119, .CZ 100 104, .CZ 100 119, .CZ 101 104, .CZ 101 119, .CZ 102 104, .CZ 102 119],
  .measureX 135 [] [.Z 31, .CZ 31 32, .CZ 31 33, .CZ 31 34, .CZ 31 35, .CZ 31 128, .CZ 31 129, .CZ 31 132, .CZ 31 133, .CZ 31 134, .CZ 32 34, .CZ 32 127, .CZ 32 128, .CZ 32 133, .CZ 33 34, .CZ 33 127, .CZ 33 128, .CZ 33 133, .CZ 34 35, .CZ 34 127, .CZ 34 129, .CZ 34 132, .CZ 34 134, .CZ 35 127, .CZ 35 128, .CZ 35 133, .Z 127, .CZ 127 128, .CZ 127 129, .CZ 127 132, .CZ 127 133, .CZ 127 134, .CZ 128 129, .CZ 128 132, .CZ 128 134, .CZ 129 133, .CZ 132 133, .CZ 133 134],
  .measureX 134 [] [.CZ 31 32, .CZ 31 133, .Z 32, .CZ 32 33, .CZ 32 126, .CZ 32 127, .CZ 32 132, .CZ 32 133, .CZ 33 133, .CZ 126 133, .CZ 127 133, .CZ 132 133],
  .measureX 133 [] [.CZ 31 32, .CZ 31 33, .CZ 31 34, .CZ 31 126, .CZ 31 128, .Z 32, .CZ 32 34, .CZ 32 127, .CZ 32 128, .CZ 32 132, .Z 33, .CZ 33 34, .CZ 33 127, .CZ 33 128, .CZ 33 132, .CZ 34 126, .CZ 34 127, .CZ 34 132, .Z 126, .CZ 126 127, .CZ 126 128, .CZ 126 132, .CZ 127 128, .CZ 128 132],
  .measureX 132 [] [.CZ 31 32, .CZ 31 34, .CZ 31 126, .CZ 31 128, .Z 32, .CZ 32 33, .CZ 32 34, .CZ 32 127, .CZ 32 128, .CZ 33 34, .CZ 33 126, .CZ 33 128, .CZ 34 126, .CZ 34 127, .Z 126, .CZ 126 127, .CZ 126 128, .CZ 127 128],
  .measureX 131 [] [.CZ 36 130, .CZ 37 130, .CZ 127 130, .CZ 129 130, .Z 130],
  .measureX 130 [] [.CZ 36 38, .CZ 36 128, .CZ 38 129, .CZ 128 129],
  .measureX 129 [] [.CZ 35 126, .CZ 36 126, .Z 126],
  .measureX 128 [] [.CZ 34 126, .CZ 38 126, .Z 126],
  .measureX 127 [] [.CZ 31 126, .CZ 37 126, .Z 126],
  .measureX 126 [] [.CZ 35 125],
  .measureX 125 [] [.CZ 31 34],
  .measureX 124 [] [.Z 23, .CZ 23 24, .CZ 23 25, .CZ 23 26, .CZ 23 27, .CZ 23 117, .CZ 23 118, .CZ 23 121, .CZ 23 122, .CZ 23 123, .CZ 24 26, .CZ 24 116, .CZ 24 117, .CZ 24 122, .CZ 25 26, .CZ 25 116, .CZ 25 117, .CZ 25 122, .CZ 26 27, .CZ 26 116, .CZ 26 118, .CZ 26 121, .CZ 26 123, .CZ 27 116, .CZ 27 117, .CZ 27 122, .Z 116, .CZ 116 117, .CZ 116 118, .CZ 116 121, .CZ 116 122, .CZ 116 123, .CZ 117 118, .CZ 117 121, .CZ 117 123, .CZ 118 122, .CZ 121 122, .CZ 122 123],
  .measureX 123 [] [.CZ 23 24, .CZ 23 122, .Z 24, .CZ 24 25, .CZ 24 94, .CZ 24 116, .CZ 24 121, .CZ 24 122, .CZ 25 122, .CZ 94 122, .CZ 116 122, .CZ 121 122],
  .measureX 122 [] [.CZ 23 24, .CZ 23 25, .CZ 23 26, .CZ 23 94, .CZ 23 117, .Z 24, .CZ 24 26, .CZ 24 116, .CZ 24 117, .CZ 24 121, .Z 25, .CZ 25 26, .CZ 25 116, .CZ 25 117, .CZ 25 121, .CZ 26 94, .CZ 26 116, .CZ 26 121, .Z 94, .CZ 94 116, .CZ 94 117, .CZ 94 121, .CZ 116 117, .CZ 117 121],
  .measureX 121 [] [.CZ 23 24, .CZ 23 26, .CZ 23 94, .CZ 23 117, .Z 24, .CZ 24 25, .CZ 24 26, .CZ 24 116, .CZ 24 117, .CZ 25 26, .CZ 25 94, .CZ 25 117, .CZ 26 94, .CZ 26 116, .Z 94, .CZ 94 116, .CZ 94 117, .CZ 116 117],
  .measureX 120 [] [.CZ 28 119, .CZ 29 119, .CZ 116 119, .CZ 118 119, .Z 119]
]

private theorem integer_load0Block31Ok : GatePhysical integer_load0Block31 ∧ toffoliCount integer_load0Block31 = 0 ∧ measurementCount integer_load0Block31 = 48 ∧ gateSlots integer_load0Block31 = 1074 := by decide +kernel

def integer_load0Block32 : Program := [
  .measureX 119 [] [.CZ 28 30, .CZ 28 117, .CZ 30 118, .CZ 117 118],
  .measureX 118 [] [.CZ 27 94, .CZ 28 94, .Z 94],
  .measureX 117 [] [.CZ 26 94, .CZ 30 94, .Z 94],
  .measureX 116 [] [.CZ 23 94, .CZ 29 94, .Z 94],
  .measureX 115 [] [.CZ 26 91, .CZ 26 92, .CZ 32 91, .CZ 32 92, .CZ 91 114, .CZ 92 114],
  .measureX 114 [] [.CZ 26 97, .CZ 32 97],
  .measureX 113 [] [.CZ 91 112, .CZ 92 112],
  .measureX 112 [] [.CZ 30 97, .CZ 35 97],
  .measureX 111 [] [.CZ 27 91, .CZ 27 92, .CZ 31 91, .CZ 31 92, .CZ 91 110, .CZ 92 110],
  .measureX 110 [] [.CZ 27 97, .CZ 31 97],
  .measureX 109 [] [.CZ 28 91, .CZ 28 92, .CZ 29 91, .CZ 29 92, .CZ 91 108, .CZ 92 108],
  .measureX 108 [] [.CZ 29 97, .CZ 34 97],
  .measureX 107 [] [.CZ 28 91, .CZ 28 92, .CZ 29 91, .CZ 29 92, .CZ 91 106, .CZ 92 106],
  .measureX 106 [] [.CZ 28 97, .CZ 33 97],
  .measureX 105 [] [.CZ 25 91, .CZ 25 92, .CZ 34 91, .CZ 34 92],
  .measureX 104 [] [.CZ 24 91, .CZ 24 92, .CZ 33 91, .CZ 33 92],
  .measureX 103 [] [.CZ 35 91, .CZ 35 92],
  .measureX 102 [] [.CZ 23 100, .CZ 23 101],
  .measureX 101 [] [.CZ 35 100],
  .measureX 100 [] [.CZ 34 99],
  .measureX 99 [] [.CZ 33 98],
  .measureX 98 [] [.CZ 31 32],
  .measureX 97 [] [.CZ 30 96],
  .measureX 96 [] [.CZ 29 95],
  .measureX 95 [] [.CZ 28 94],
  .measureX 94 [] [.CZ 27 93],
  .measureX 93 [] [.CZ 23 26],
  .measureX 92 [] [.CZ 27 91],
  .measureX 91 [] [.CZ 26 90],
  .measureX 90 [] [.CZ 25 89],
  .measureX 89 [] [.CZ 23 24],
  .X 39,
  .CX 23 0,
  .CX 0 23,
  .CX 24 1,
  .CX 1 24,
  .CX 25 2,
  .CX 2 25,
  .CX 26 3,
  .CX 3 26,
  .CX 27 4,
  .CX 4 27,
  .CX 28 5,
  .CX 5 28,
  .CX 29 6,
  .CX 6 29,
  .CX 30 7,
  .CX 7 30
]

private theorem integer_load0Block32Ok : GatePhysical integer_load0Block32 ∧ toffoliCount integer_load0Block32 = 0 ∧ measurementCount integer_load0Block32 = 31 ∧ gateSlots integer_load0Block32 = 122 := by decide +kernel

def integer_load0Block33 : Program := [
  .CX 31 8,
  .CX 8 31,
  .CX 32 9,
  .CX 9 32,
  .CX 33 10,
  .CX 10 33,
  .CX 34 11,
  .CX 11 34,
  .CX 35 12,
  .CX 12 35,
  .CX 36 13,
  .CX 13 36,
  .CX 37 14,
  .CX 14 37,
  .CX 38 15,
  .CX 15 38
]

private theorem integer_load0Block33Ok : GatePhysical integer_load0Block33 ∧ toffoliCount integer_load0Block33 = 0 ∧ measurementCount integer_load0Block33 = 0 ∧ gateSlots integer_load0Block33 = 16 := by decide +kernel

def integer_load0 : Program := integer_load0Block0 ++ integer_load0Block1 ++ integer_load0Block2 ++ integer_load0Block3 ++ integer_load0Block4 ++ integer_load0Block5 ++ integer_load0Block6 ++ integer_load0Block7 ++ integer_load0Block8 ++ integer_load0Block9 ++ integer_load0Block10 ++ integer_load0Block11 ++ integer_load0Block12 ++ integer_load0Block13 ++ integer_load0Block14 ++ integer_load0Block15 ++ integer_load0Block16 ++ integer_load0Block17 ++ integer_load0Block18 ++ integer_load0Block19 ++ integer_load0Block20 ++ integer_load0Block21 ++ integer_load0Block22 ++ integer_load0Block23 ++ integer_load0Block24 ++ integer_load0Block25 ++ integer_load0Block26 ++ integer_load0Block27 ++ integer_load0Block28 ++ integer_load0Block29 ++ integer_load0Block30 ++ integer_load0Block31 ++ integer_load0Block32 ++ integer_load0Block33

theorem integer_load0_GatePhysical : GatePhysical integer_load0 := by
  simp only [integer_load0, gatePhysical_append, and_true, integer_load0Block0Ok.1, integer_load0Block1Ok.1, integer_load0Block2Ok.1, integer_load0Block3Ok.1, integer_load0Block4Ok.1, integer_load0Block5Ok.1, integer_load0Block6Ok.1, integer_load0Block7Ok.1, integer_load0Block8Ok.1, integer_load0Block9Ok.1, integer_load0Block10Ok.1, integer_load0Block11Ok.1, integer_load0Block12Ok.1, integer_load0Block13Ok.1, integer_load0Block14Ok.1, integer_load0Block15Ok.1, integer_load0Block16Ok.1, integer_load0Block17Ok.1, integer_load0Block18Ok.1, integer_load0Block19Ok.1, integer_load0Block20Ok.1, integer_load0Block21Ok.1, integer_load0Block22Ok.1, integer_load0Block23Ok.1, integer_load0Block24Ok.1, integer_load0Block25Ok.1, integer_load0Block26Ok.1, integer_load0Block27Ok.1, integer_load0Block28Ok.1, integer_load0Block29Ok.1, integer_load0Block30Ok.1, integer_load0Block31Ok.1, integer_load0Block32Ok.1, integer_load0Block33Ok.1]

theorem integer_load0_toffoliCount : toffoliCount integer_load0 = 89 := by
  simp only [integer_load0, toffoliCount_append, integer_load0Block0Ok.2.1, integer_load0Block1Ok.2.1, integer_load0Block2Ok.2.1, integer_load0Block3Ok.2.1, integer_load0Block4Ok.2.1, integer_load0Block5Ok.2.1, integer_load0Block6Ok.2.1, integer_load0Block7Ok.2.1, integer_load0Block8Ok.2.1, integer_load0Block9Ok.2.1, integer_load0Block10Ok.2.1, integer_load0Block11Ok.2.1, integer_load0Block12Ok.2.1, integer_load0Block13Ok.2.1, integer_load0Block14Ok.2.1, integer_load0Block15Ok.2.1, integer_load0Block16Ok.2.1, integer_load0Block17Ok.2.1, integer_load0Block18Ok.2.1, integer_load0Block19Ok.2.1, integer_load0Block20Ok.2.1, integer_load0Block21Ok.2.1, integer_load0Block22Ok.2.1, integer_load0Block23Ok.2.1, integer_load0Block24Ok.2.1, integer_load0Block25Ok.2.1, integer_load0Block26Ok.2.1, integer_load0Block27Ok.2.1, integer_load0Block28Ok.2.1, integer_load0Block29Ok.2.1, integer_load0Block30Ok.2.1, integer_load0Block31Ok.2.1, integer_load0Block32Ok.2.1, integer_load0Block33Ok.2.1]

theorem integer_load0_measurementCount : measurementCount integer_load0 = 136 := by
  simp only [integer_load0, measurementCount_append, integer_load0Block0Ok.2.2.1, integer_load0Block1Ok.2.2.1, integer_load0Block2Ok.2.2.1, integer_load0Block3Ok.2.2.1, integer_load0Block4Ok.2.2.1, integer_load0Block5Ok.2.2.1, integer_load0Block6Ok.2.2.1, integer_load0Block7Ok.2.2.1, integer_load0Block8Ok.2.2.1, integer_load0Block9Ok.2.2.1, integer_load0Block10Ok.2.2.1, integer_load0Block11Ok.2.2.1, integer_load0Block12Ok.2.2.1, integer_load0Block13Ok.2.2.1, integer_load0Block14Ok.2.2.1, integer_load0Block15Ok.2.2.1, integer_load0Block16Ok.2.2.1, integer_load0Block17Ok.2.2.1, integer_load0Block18Ok.2.2.1, integer_load0Block19Ok.2.2.1, integer_load0Block20Ok.2.2.1, integer_load0Block21Ok.2.2.1, integer_load0Block22Ok.2.2.1, integer_load0Block23Ok.2.2.1, integer_load0Block24Ok.2.2.1, integer_load0Block25Ok.2.2.1, integer_load0Block26Ok.2.2.1, integer_load0Block27Ok.2.2.1, integer_load0Block28Ok.2.2.1, integer_load0Block29Ok.2.2.1, integer_load0Block30Ok.2.2.1, integer_load0Block31Ok.2.2.1, integer_load0Block32Ok.2.2.1, integer_load0Block33Ok.2.2.1]

theorem integer_load0_gateSlots : gateSlots integer_load0 = 3245 := by
  simp only [integer_load0, gateSlots_append, integer_load0Block0Ok.2.2.2, integer_load0Block1Ok.2.2.2, integer_load0Block2Ok.2.2.2, integer_load0Block3Ok.2.2.2, integer_load0Block4Ok.2.2.2, integer_load0Block5Ok.2.2.2, integer_load0Block6Ok.2.2.2, integer_load0Block7Ok.2.2.2, integer_load0Block8Ok.2.2.2, integer_load0Block9Ok.2.2.2, integer_load0Block10Ok.2.2.2, integer_load0Block11Ok.2.2.2, integer_load0Block12Ok.2.2.2, integer_load0Block13Ok.2.2.2, integer_load0Block14Ok.2.2.2, integer_load0Block15Ok.2.2.2, integer_load0Block16Ok.2.2.2, integer_load0Block17Ok.2.2.2, integer_load0Block18Ok.2.2.2, integer_load0Block19Ok.2.2.2, integer_load0Block20Ok.2.2.2, integer_load0Block21Ok.2.2.2, integer_load0Block22Ok.2.2.2, integer_load0Block23Ok.2.2.2, integer_load0Block24Ok.2.2.2, integer_load0Block25Ok.2.2.2, integer_load0Block26Ok.2.2.2, integer_load0Block27Ok.2.2.2, integer_load0Block28Ok.2.2.2, integer_load0Block29Ok.2.2.2, integer_load0Block30Ok.2.2.2, integer_load0Block31Ok.2.2.2, integer_load0Block32Ok.2.2.2, integer_load0Block33Ok.2.2.2]

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace0In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246] ++ List.replicate 132 0

def integer_load0Trace0Out : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col263,
col131,
0x0,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130] ++ List.replicate 89 0

theorem integer_load0Trace0_checked : eval col263 (integer_load0Block0 ++ integer_load0Block1 ++ integer_load0Block2 ++ integer_load0Block3 ++ integer_load0Block4 ++ integer_load0Block5) integer_load0Trace0In =

    (true, integer_load0Trace0Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace1In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col263,
col131,
0x0,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130] ++ List.replicate 89 0

def integer_load0Trace1Out : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col263,
col262,
col70,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76] ++ List.replicate 68 0

theorem integer_load0Trace1_checked : eval col263 (integer_load0Block6 ++ integer_load0Block7 ++ integer_load0Block8 ++ integer_load0Block9 ++ integer_load0Block10 ++ integer_load0Block11) integer_load0Trace1In =

    (true, integer_load0Trace1Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace2In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col263,
col262,
col70,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76] ++ List.replicate 68 0

def integer_load0Trace2Out : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
col243,
col248,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76,
col79,
col84,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35] ++ List.replicate 39 0

theorem integer_load0Trace2_checked : eval col263 (integer_load0Block12 ++ integer_load0Block13 ++ integer_load0Block14 ++ integer_load0Block15 ++ integer_load0Block16 ++ integer_load0Block17) integer_load0Trace2In =

    (true, integer_load0Trace2Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace3In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
col243,
col248,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76,
col79,
col84,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35] ++ List.replicate 39 0

def integer_load0Trace3Out : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
col34,
col157,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76,
col79,
col84,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35,
col241,
col242,
col237,
col42,
col40,
col136,
col176,
col27,
col48,
col213,
col212,
col208,
col210,
col206,
col119,
col117,
col101,
col195,
col90,
col115,
col158,
col30] ++ List.replicate 17 0

theorem integer_load0Trace3_checked : eval col263 (integer_load0Block18 ++ integer_load0Block19 ++ integer_load0Block20 ++ integer_load0Block21 ++ integer_load0Block22 ++ integer_load0Block23) integer_load0Trace3In =

    (true, integer_load0Trace3Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace4In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
col34,
col157,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
col162,
col98,
col75,
col132,
col111,
col222,
col76,
col79,
col84,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35,
col241,
col242,
col237,
col42,
col40,
col136,
col176,
col27,
col48,
col213,
col212,
col208,
col210,
col206,
col119,
col117,
col101,
col195,
col90,
col115,
col158,
col30] ++ List.replicate 17 0

def integer_load0Trace4Out : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
0x0,
0x0,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35,
col241,
col242,
col237,
col42,
col40,
col136,
col176,
col27,
col48,
col213,
col212,
col208,
col210,
col206,
col119,
col117,
col101,
col195,
col90,
col115,
col158,
col30,
col147,
col25,
col153,
col23,
col166,
col21,
col167,
col16,
col83,
col13,
col122,
col9,
col134,
col7,
col126,
col5,
col202] ++ List.replicate 0 0

theorem integer_load0Trace4_checked : eval col263 (integer_load0Block24 ++ integer_load0Block25 ++ integer_load0Block26 ++ integer_load0Block27 ++ integer_load0Block28 ++ integer_load0Block29) integer_load0Trace4In =

    (true, integer_load0Trace4Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates

open CodecBitSliceVerify StairArchiveIntegerColumns

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000

def integer_load0Trace5In : Cols := [col157,
col32,
col146,
col29,
col131,
col24,
col109,
col22,
col96,
col19,
col82,
col15,
col73,
col12,
col64,
col8,
col59,
col6,
col55,
col3,
col262,
col256,
col246,
col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231,
col263,
0x0,
0x0,
col88,
col100,
col91,
col154,
col28,
col124,
col123,
col135,
col53,
col56,
col54,
col78,
col11,
col61,
col60,
col67,
col233,
col156,
col145,
col72,
col10,
col95,
col17,
col130,
col106,
col108,
col129,
col81,
col80,
col160,
col150,
col125,
col161,
col149,
col140,
col189,
col144,
col155,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
0x0,
col182,
col174,
col173,
col169,
col257,
col243,
col237,
col236,
col233,
col217,
col198,
col193,
col191,
col77,
col45,
col39,
col38,
col128,
col37,
col105,
col37,
col94,
col44,
col80,
0x0,
col71,
col35,
col241,
col242,
col237,
col42,
col40,
col136,
col176,
col27,
col48,
col213,
col212,
col208,
col210,
col206,
col119,
col117,
col101,
col195,
col90,
col115,
col158,
col30,
col147,
col25,
col153,
col23,
col166,
col21,
col167,
col16,
col83,
col13,
col122,
col9,
col134,
col7,
col126,
col5,
col202] ++ List.replicate 0 0

def integer_load0Trace5Out : Cols := [col259,
col184,
col187,
col261,
col245,
col252,
col249,
col254,
col219,
col224,
col200,
col215,
col221,
col226,
col228,
col231] ++ List.replicate 139 0

theorem integer_load0Trace5_checked : eval col263 (integer_load0Block30 ++ integer_load0Block31 ++ integer_load0Block32 ++ integer_load0Block33) integer_load0Trace5In =

    (true, integer_load0Trace5Out) := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.Stair44WalkStage
open Arithmetic MappedCompressed DirectSkywalk

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem park_ready (w : Nat → Wire) (d : Bool) (hn : (skywalkPoolWires w).Nodup)
    (x p : Nat) (hp0 : 0 < p) (hpo : p % 2 = 1) (s : State)
    (hs : Rolling1588.Integer.Stage w d x p 16 s.basis) (k : Nat) (hk : k < 5) :
    s.basis (w (Placement5.H k)) = false := by
  obtain ⟨raw, hraw, bits⟩ := hs
  have hl : NewHistory5.RawLegal w 3 raw.basis := by
    intro j hj
    exact W.stage_group_legal w hn x p 16 (5*j) hp0 hpo (by omega) (by decide) raw.basis hraw
  have cut := Rolling1588.Integer.encodePrefix_index w d 3
  let port : Fin 10 := if k % 2 = 0 then 5 else 9
  have hp : port=5 ∨ port=9 := by unfold port; split <;> simp
  have site : w (Placement5.H k) = History5.historyMap w (5*(k/2)) port := by
    change w (Placement5.H k)=w (History5.historyId (5*(k/2)) port)
    congr 1
    unfold Placement5.H History5.historyId port
    split_ifs <;> omega
  rw [congrFun bits _, cut, site]
  exact Rolling1588.allEncode_hole w d hn 3 (k/2) (by decide) (by omega) raw [] hl port hp

private theorem encode_away (d : Bool) (i : Nat) (hi : i ∈ [500,501,502,503,504,1541,1542]) :
    base i ∉ wires (Rolling1588.allEncode base d 3) := by
  intro used
  rw [Rolling1588.allEncode_support_eq, NewHistory5.allEncode_support_eq] at used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member base 3 _ used
  obtain ⟨q,hq⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) _ member
  have eq : i = History5.historyId (5*j) q := Nat.add_right_cancel hq
  have bound := q.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold History5.historyId at eq
  split_ifs at eq <;> omega

theorem early_ready (d : Bool) (x p : Nat) (s : State)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis)
    (i : Nat) (hi : i ∈ [500,501,502,503,504,1541,1542]) :
    s.basis (base i) = false := by
  obtain ⟨raw, hraw, bits⟩ := hs
  rw [congrFun bits _, Rolling1588.Integer.encodePrefix_index base d 3]
  have eq := run_preserves_outside (Rolling1588.allEncode base d 3) [] raw (base i) (encode_away d i hi)
  rw [eq]
  have f := (W.compactSkywalkStage_fields_iff base _ 16 (by decide) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_, _, _, _, ext, carries, _, _, _⟩ := f
  have eb (j : Nat) (h1 : 16 ≤ j) (h2 : j < 512) := (ext j h1 h2).1
  have cb := (regValue_zero _ _).mp carries
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst i
  · exact eb 242 (by decide) (by decide)
  · exact eb 243 (by decide) (by decide)
  · exact eb 244 (by decide) (by decide)
  · exact eb 245 (by decide) (by decide)
  · exact eb 246 (by decide) (by decide)
  · exact cb _ (by decide)
  · exact cb _ (by decide)

end ECDSAAdd.Entrant.Stair44WalkStage

end

section

namespace ECDSAAdd.Entrant.StairArchiveGates
open CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem integer_load0_checked : eval 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff integer_load0 integer_load0Trace0In = (true, integer_load0Trace5Out) := by
  have shape : integer_load0 = ((integer_load0Block0 ++ integer_load0Block1 ++ integer_load0Block2 ++ integer_load0Block3 ++ integer_load0Block4 ++ integer_load0Block5) ++ ((integer_load0Block6 ++ integer_load0Block7 ++ integer_load0Block8 ++ integer_load0Block9 ++ integer_load0Block10 ++ integer_load0Block11) ++ ((integer_load0Block12 ++ integer_load0Block13 ++ integer_load0Block14 ++ integer_load0Block15 ++ integer_load0Block16 ++ integer_load0Block17) ++ ((integer_load0Block18 ++ integer_load0Block19 ++ integer_load0Block20 ++ integer_load0Block21 ++ integer_load0Block22 ++ integer_load0Block23) ++ ((integer_load0Block24 ++ integer_load0Block25 ++ integer_load0Block26 ++ integer_load0Block27 ++ integer_load0Block28 ++ integer_load0Block29) ++ (integer_load0Block30 ++ integer_load0Block31 ++ integer_load0Block32 ++ integer_load0Block33)))))) := by
    simp only [integer_load0, List.append_assoc]
  rw [shape]
  exact (StairArchiveRows.combine _ _ _ _ _ _ integer_load0Trace0_checked (StairArchiveRows.combine _ _ _ _ _ _ integer_load0Trace1_checked (StairArchiveRows.combine _ _ _ _ _ _ integer_load0Trace2_checked (StairArchiveRows.combine _ _ _ _ _ _ integer_load0Trace3_checked (StairArchiveRows.combine _ _ _ _ _ _ integer_load0Trace4_checked integer_load0Trace5_checked)))))

private theorem integer_load0_target : ∀ i ∈ integer_load0, target i < 155 := by decide +kernel

theorem integer_load0_run (row x : Nat) (m : List Bool) (s : State)
    (active : (0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Nat).testBit row = true)
    (input : Rel integer_load0Trace0In x row) (state : ∀ q ∈ wires integer_load0, s.basis q = x.testBit q) :
    (run integer_load0 m s).phase = s.phase ∧
    (∀ q ∈ wires integer_load0, (run integer_load0 m s).basis q = (get integer_load0Trace5Out q).testBit row) ∧
    (∀ q ∉ wires integer_load0, (run integer_load0 m s).basis q = s.basis q) :=
  StairArchiveRows.run_row integer_load0 _ row x m s integer_load0Trace0In integer_load0Trace5Out active integer_load0_target input integer_load0_checked state

end ECDSAAdd.Entrant.StairArchiveGates

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
open CodecBitSliceVerify StairArchiveGates

def rawCol (q : Nat) := get integer_load0Trace0In q
def page (word base width : Nat) := (word >>> base) % 2^width
def pack (n : Nat) (f : Nat → Bool) := packBits ((List.range n).map f)
def trit (q rank : Nat) : Bool :=
  rank / 3^(4-q/2) % 3 == (if q%2=0 then 2 else 1)

def nearTile (q high : Nat) : Nat :=
  if q<10 then (if trit q high then 2^243-1 else 0)
  else if q<20 then pack 243 (trit (q-10)) else 0

def farBit (q group lo : Nat) : Bool :=
  let mask := (group%16)*64+lo
  let u := decide (32 ≤ group)
  let c := decide (group/16%2 = 1)
  if q<20 then
    let i := q/2
    if q%2=0 then !(mask.testBit i)
    else !u && mask.testBit i && (mask % 2^i == 0)
  else if q=20 then true else if q=21 then u else c

def checks (q : Nat) : Bool :=
  (List.range 243).all (fun high => page (rawCol q) (243*high) 243 == nearTile q high) &&
  (List.range 64).all (fun group => page (rawCol q) (59049+64*group) 64 == pack 64 (farBit q group))

theorem page_bit (word base width offset : Nat) (h : offset<width) :
    (page word base width).testBit offset = word.testBit (base+offset) := by
  simp only [page, Nat.testBit_mod_two_pow, decide_eq_true h, Bool.true_and, Nat.testBit_shiftRight]

theorem pack_bit (n : Nat) (f : Nat→Bool) (i : Nat) (h : i<n) : (pack n f).testBit i=f i := by
  rw [pack, pack_testBit]
  simp [h]

theorem near_bit (q hi lo : Nat) (hq : checks q = true) (hh : hi<243) (hl : lo<243) :
    (rawCol q).testBit (243*hi+lo) =
      (if q<10 then trit q hi else if q<20 then trit (q-10) lo else false) := by
  have c : page (rawCol q) (243*hi) 243 = nearTile q hi := by
    simp only [checks, Bool.and_eq_true] at hq
    exact beq_iff_eq.mp (List.all_eq_true.mp hq.1 _ (List.mem_range.mpr hh))
  rw [←page_bit _ _ _ _ hl, c]
  unfold nearTile
  split
  · cases b : trit q hi
    · exact Nat.zero_testBit lo
    · change (2^243-1 : Nat).testBit lo = true
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hl
  · split
    · exact pack_bit _ _ _ hl
    · exact Nat.zero_testBit lo

theorem far_bit (q group lo : Nat) (hq : checks q = true) (hg : group<64) (hl : lo<64) :
    (rawCol q).testBit (59049+64*group+lo) = farBit q group lo := by
  have c : page (rawCol q) (59049+64*group) 64 = pack 64 (farBit q group) := by
    simp only [checks, Bool.and_eq_true] at hq
    exact beq_iff_eq.mp (List.all_eq_true.mp hq.2 _ (List.mem_range.mpr hg))
  rw [←page_bit _ _ _ _ hl, c]
  exact pack_bit _ _ _ hl

end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.Stair44FieldSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairConcreteAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

abbrev holes := StairPhysicalInventory.physicalHoles
theorem hsub (x : Wire) (h : x ∈ holes) : x ∈ StairPhysicalInventory.physicalHoles := h
private def extraFree (q : Wire) : Bool :=
  let x := StairPlaceFast.outerPlaceB q
  !(Nat.ble 4835 x && Nat.blt x 4840)
private theorem complete {P : Program} (stock : PieceOK StairCertificate.holes39 TP P)
    (hf : ∀ q ∈ wires P, extraFree q = true) : PieceOK holes TP P := by
  refine ⟨stock.1,?_⟩
  intro x hx hbad
  have h := hf x hx
  have rest := stock.2 x hx
  change StairOuterPlacement.outerPlace x ∉ _ at rest
  change StairOuterPlacement.outerPlace x ∈ StairPhysicalInventory.physicalHoles at hbad
  rw [StairPlaceFast.outerPlace_eqB,StairPhysicalLayout.physicalHoles_eq_nat] at hbad
  rw [StairPlaceFast.outerPlace_eqB] at rest
  have lookup : ∀ v ∈ StairPhysicalLayout.newHolesNat,
      v ∈ StairCertificate.holes39 ∨ (4835 ≤ v ∧ v < 4840) := by
    rw [StairSquareEntryR.holes39_eq]
    decide +kernel
  rcases lookup _ hbad with old | ⟨lo,hi⟩
  · exact rest old
  · have l : Nat.ble 4835 (StairPlaceFast.outerPlaceB x) = true := by simpa only [Nat.ble_eq] using lo
    have u : Nat.blt (StairPlaceFast.outerPlaceB x) 4840 = true := by simpa only [Nat.blt_eq] using hi
    simp [extraFree,l,u] at h

private theorem converter {P Q : Program}
    (env : wires P ⊆ wires Q ∪ StairBoundaryLoan.converterHosts.toFinset)
    (rec : wires Q ⊆ StairBoundaryLoan.converterLayout760.wires.toFinset)
    (avoid : ∀ q ∈ StairBoundaryLoan.exclusiveHoles, q ∉ wires P)
    (old : PieceOK StairCertificate.holes39 TP P) :
    PieceOK holes TP P := by
  apply complete old
  intro x hx
  have mem : x ∈ StairBoundaryLoan.converterLayout760.wires ++
      StairBoundaryLoan.converterHosts := by
    rcases Finset.mem_union.mp (env hx) with h | h
    · exact List.mem_append_left _ (List.mem_toFinset.mp (rec h))
    · exact List.mem_append_right _ (List.mem_toFinset.mp h)
  have table : (StairBoundaryLoan.converterLayout760.wires ++ StairBoundaryLoan.converterHosts).all
      (fun y => decide (RoleI y) || extraFree y) = true := by decide +kernel
  have t := List.all_eq_true.mp table x mem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at t
  exact t.resolve_left (fun m => avoid x (roleI_mem m) hx)

theorem canon : PieceOK holes TP StairConcrete.bestLoans.canon :=
  converter StairBoundaryLoan.canon760Loan_envelope
    (by
      rw [StairBoundaryLoan.canon760_eq]
      exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).2)
    StairBoundaryLoan.canon760Loan_avoids canon39

theorem center : PieceOK holes TP StairConcrete.bestLoans.center :=
  converter StairBoundaryLoan.center760Loan_envelope
    (by
      rw [StairBoundaryLoan.center760_eq]
      exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).1)
    StairBoundaryLoan.center760Loan_avoids center39

private theorem de_tab : DecoderBiasReuse.fixedLayout.wires.all (fun w =>
    decide (RoleI w) || (extraFree (OB5.sig 511 (Equiv.swap (base 760) (base 717)
      (shifted Placement5.pi0 (Equiv.swap (base 719) (base 510) w)))))) = true := by
  decide +kernel

private theorem de_g : extraFree (OB5.sig 511 (Equiv.swap (base 760) (base 717)
    (shifted Placement5.pi0 (base 510)))) = true := by
  decide +kernel

private theorem de_flag : extraFree (OB5.sig 511 (Equiv.swap (base 760) (base 717)
    (shifted Placement5.pi0 (base 2409)))) = true := by
  decide +kernel

private theorem de_pad : extraFree (OB5.sig 511 (Equiv.swap (base 760) (base 717)
    (shifted Placement5.pi0 (Equiv.swap (base 719) (base 510) (base 512))))) = true := by
  decide +kernel

attribute [local irreducible] ECDSAAdd.wires in
private theorem de_tpi (y : Wire)
    (hy : y ∈ wires CompareDecoder.BoundaryLoan.endPacket760DivLoan) : extraFree (OB5.sig 511 y) = true := by
  unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
  rw [renameProgram_support] at hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h | h
  · rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact de_g
    · exact de_flag
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    rw [wires_append, Finset.mem_union] at hz
    rcases hz with hz | hz
    · have hl := List.mem_toFinset.mp
        (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz))
      have t := List.all_eq_true.mp de_tab z hl
      simp only [Bool.or_eq_true, decide_eq_true_eq] at t
      exact t.resolve_left (fun m => k5_loan_avoids z (roleI_mem m) hz)
    · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
      rw [Finset.mem_singleton] at hc
      rw [hc]
      exact de_pad

attribute [local irreducible] ECDSAAdd.wires in
theorem endpointD : PieceOK holes TP
    (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) := by
  apply complete endpointDiv39
  intro x hx
  rw [renameProgram_support, StairConcrete.bestLoans_divEndpoint] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact de_tpi y hy

attribute [local irreducible] ECDSAAdd.wires in
theorem endpointM : PieceOK holes TP
    (StairHostsSchedule.hostedEndpoint hp false 68) := by
  apply complete endpointMult39
  intro x hx
  have e : StairConcrete.bestLoans.endPacket false 68 =
      StairEndpointLoan44.endPacket760Loan44 false := by
    simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true,
      if_false, if_true]
  rw [StairHostsSchedule.hostedEndpoint, StairSchedule.placedEndPacket, e,
    renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have notRole : ¬ RoleI y := fun m =>
    StairEndpointLoan44.endPacket760Loan44_avoids y (roleI_mem m) hy
  have table : multEndL.all (fun z => decide (RoleI z) || extraFree (OB5.sig 511 z)) = true := by decide +kernel
  have t := List.all_eq_true.mp table y
    (endPacket760_false_mem y (StairEndpointLoan44.endPacket760Loan44_support hy))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at t
  exact t.resolve_left notRole
end ECDSAAdd.Entrant.Stair44FieldSites

end

section

namespace ECDSAAdd.Entrant.Stair44Groups
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy

set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

private theorem safe_table :
    tpList.all (fun x => decide (x ∈ StairSchedule.exclusiveRoles) ||
      decide (StairPlaceFast.outerPlaceB x ∉ StairPhysicalLayout.newHolesNat)) = true := by
  decide +kernel

private theorem asList (x : Nat) (h : TPI x) : x∈tpList := by
  unfold TPI at h
  simp only [tpList,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  omega

private theorem physical_safe {x : Wire} (tpi : TPI x) (nr : x ∉ StairSchedule.exclusiveRoles) :
    TP x ∉ StairPhysicalInventory.physicalHoles := by
  have mem := asList x tpi
  have h := List.all_eq_true.mp safe_table x mem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  change StairOuterPlacement.outerPlace x ∉ StairPhysicalLayout.newHolesNat
  rw [StairPlaceFast.outerPlace_eqB]
  exact h.resolve_left nr

private theorem host_nonrole : ∀ g ∈ schedule, ∀ h ∈ hp.group true g.1 g.2.1 g.2.2,
    h ∉ StairSchedule.exclusiveRoles := by decide +kernel

theorem hostedGroup44 (divide : Bool) (d f c : Nat) (hg : (d, f, c) ∈ schedule) :
    PieceOK StairPhysicalInventory.physicalHoles TP (StairHostsSchedule.hostedGroup hp divide d f c) := by
  obtain ⟨hd, hf, hc⟩ := schedule_bounds _ hg
  obtain ⟨disj, nr, nh, hlen, htpi⟩ := hostFacts _ hg
  simp only at hd hf hc disj nr nh hlen htpi
  rw [← group_dir divide] at disj nh hlen htpi
  refine ⟨(hostedGroup39 divide d f c hg).1, ?_⟩
  intro x hx
  unfold StairHostsSchedule.hostedGroup at hx
  rcases rebind_mem _ _ _ (hostsFresh divide d f c hg) disj nr nh hlen x hx with hh | ⟨hP, hnr⟩
  · exact physical_safe (htpi x hh) (by
      rw [group_dir divide] at hh
      exact host_nonrole _ hg x hh)
  · change x ∈ wires (renameProgram (OB5.sig 511) (StairGroups.groups divide d f c)) at hP
    rw [renameProgram_support] at hP
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj1, hj2, hjw⟩ := seq_mem divide (StairGroups.packet divide d) c f w hw
    unfold StairGroups.packet at hjw
    rw [renameProgram_support] at hjw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hjw
    have hjr : j ∈ List.range' 1 101 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
    obtain ⟨nt, hr⟩ := basePacket_tgt divide d j hjr hd z hz
    have nr : Mj j z ∉ StairSchedule.exclusiveRoles := by
      intro role
      rw [← List.take_append_drop d StairSchedule.exclusiveRoles, List.mem_append] at role
      exact role.elim nt hnr
    rcases hr with hr | hr
    · exact absurd hr nr
    · exact physical_safe hr nr

end ECDSAAdd.Entrant.Stair44Groups

end

section

namespace ECDSAAdd.Entrant.Stair44OuterSites
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy Stair44PointMap
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

def fit (q : Wire) := good39B q && decide (q∉retired)
private theorem extra : ∀q∈StairPhysicalInventory.physicalHoles,
    q∈StairCertificate.holes39 ∨ q∈retired := by
  rw [StairPhysicalLayout.physicalHoles_eq_nat,StairSquareEntryR.holes39_eq]
  decide +kernel

theorem fits {f : Wire → Wire} {P : Program} (h : ∀q∈wires P,fit (f q)=true) :
    PieceOK StairPhysicalInventory.physicalHoles f P := by
  have good (q : Wire) (hq : q∈wires P) : good39B (f q)=true ∧ f q∉retired := by
    simpa only [fit,Bool.and_eq_true,decide_eq_true_eq] using h q hq
  have old := ok39_of_good (fun q hq => good39_of_B (good q hq).1)
  exact ⟨old.1,fun q hq bad => (extra _ bad).elim (old.2 q hq) (good q hq).2⟩

theorem lifted (f : Wire → Wire) (c : Equiv.Perm Wire) (P : Program)
    (h : ∀q∈wires P,fit (f (c q))=true) : PieceOK StairPhysicalInventory.physicalHoles f (renameProgram c P) := by
  apply fits
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  exact h q hq

end ECDSAAdd.Entrant.Stair44OuterSites

end

section

namespace ECDSAAdd.Entrant.Stair44WalkMap
open Arithmetic MappedCompressed
set_option maxRecDepth 10000

def shared : Equiv.Perm Wire := Equiv.swap (base 1026) (base 514)
def first : Equiv.Perm Wire := (Equiv.swap (base 1542) (base 500)).trans
  ((Equiv.swap (base 1541) (base 501)).trans shared)
def rest : Equiv.Perm Wire := (Equiv.swap (base 1542) (base (Placement5.H 0))).trans
  ((Equiv.swap (base 1541) (base (Placement5.H 1))).trans shared)

private theorem pull_sw (f : Wire → Wire) (a b : Wire) (actual logical : State)
    (ha : logical.basis a = false) (hb : logical.basis b = false) :
    pullState (f ∘ Equiv.swap a b) actual = logical ↔ pullState f actual = logical := by
  constructor
  · intro h
    have twice : (Equiv.swap a b : Wire → Wire) ∘ Equiv.swap a b = id := by
      funext q; exact Equiv.swap_apply_self a b q
    have back := cleanWireRebind _ actual logical _ _ h ha hb
    simpa only [Function.comp_assoc,twice,Function.comp_id] using back
  · exact fun h => cleanWireRebind f actual logical a b h ha hb

def switchSites : List Wire :=
  [base 1542,base 1541,base 500,base 501,base (Placement5.H 0),base (Placement5.H 1)]

theorem switch_at (actual logical : State) (map : Wire → Wire)
    (clean : ∀ q ∈ switchSites, logical.basis q = false) :
    pullState (map ∘ first) actual = logical ↔ pullState (map ∘ rest) actual = logical := by
  let f := map ∘ shared
  change (pullState ((f ∘ Equiv.swap (base 1541) (base 501)) ∘ Equiv.swap (base 1542) (base 500)) actual = logical) ↔
    pullState ((f ∘ Equiv.swap (base 1541) (base (Placement5.H 1))) ∘ Equiv.swap (base 1542) (base (Placement5.H 0))) actual = logical
  rw [pull_sw _ _ _ _ _ (clean _ (by decide)) (clean _ (by decide)),
      pull_sw _ _ _ _ _ (clean _ (by decide)) (clean _ (by decide)),
      pull_sw _ _ _ _ _ (clean _ (by decide)) (clean _ (by decide)),
      pull_sw _ _ _ _ _ (clean _ (by decide)) (clean _ (by decide))]

theorem stage_clean (d : Bool) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s : State) (hs : Rolling1588.Integer.Stage base d x p 16 s.basis) :
    ∀ q ∈ switchSites, (pullState (OB5.sig 15) s).basis q = false := by
  let logical := pullState (OB5.sig 15) s
  have e (i : Nat) (hi : i ∈ [500,501,1541,1542]) : logical.basis (base i) = false := by
    have mem : i ∈ [500,501,502,503,504,1541,1542] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto
    have fixed : OB5.sig 15 (base i) = base i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h|h|h <;> subst i <;> decide
    change s.basis (OB5.sig 15 (base i)) = false
    rw [fixed]
    exact Stair44WalkStage.early_ready d x p s hs i mem
  have h (i : Nat) (hi : i ∈ [0,1]) : logical.basis (base (Placement5.H i)) = false := by
    have small : i < 5 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    have fixed : OB5.sig 15 (base (Placement5.H i)) = base (Placement5.H i) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h <;> subst i <;> decide
    change s.basis (OB5.sig 15 (base (Placement5.H i))) = false
    rw [fixed]
    exact Stair44WalkStage.park_ready base d base_pool_nodup x p hp0 hpo s hs i small
  intro q hq
  simp only [switchSites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q
  · exact e _ (by decide)
  · exact e _ (by decide)
  · exact e _ (by decide)
  · exact e _ (by decide)
  · exact h _ (by decide)
  · exact h _ (by decide)

theorem stage_switch (d : Bool) (x p : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (s actual : State) (map : Wire → Wire) (hs : Rolling1588.Integer.Stage base d x p 16 s.basis)
    (frame : pullState (map ∘ first) actual = pullState (OB5.sig 15) s) :
    pullState (map ∘ rest) actual = pullState (OB5.sig 15) s := by
  exact (switch_at actual _ map (stage_clean d x p hp0 hpo s hs)).mp frame

end ECDSAAdd.Entrant.Stair44WalkMap

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q0 : checks 0 = true := by decide +kernel
theorem q1 : checks 1 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q2 : checks 2 = true := by decide +kernel
theorem q3 : checks 3 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q4 : checks 4 = true := by decide +kernel
theorem q5 : checks 5 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q6 : checks 6 = true := by decide +kernel
theorem q7 : checks 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q8 : checks 8 = true := by decide +kernel
theorem q9 : checks 9 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q10 : checks 10 = true := by decide +kernel
theorem q11 : checks 11 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q12 : checks 12 = true := by decide +kernel
theorem q13 : checks 13 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q14 : checks 14 = true := by decide +kernel
theorem q15 : checks 15 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q16 : checks 16 = true := by decide +kernel
theorem q17 : checks 17 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q18 : checks 18 = true := by decide +kernel
theorem q19 : checks 19 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q20 : checks 20 = true := by decide +kernel
theorem q21 : checks 21 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
theorem q22 : checks 22 = true := by decide +kernel
end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.Stair44FirstRow
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def freePhase (x : Wire) : Bool :=
  decide (StairPlaceFast.phasePlaceB x ∉ StairPhysicalLayout.newHolesNat)

private theorem checked {P : Program} (arena : ArenaOld PP P) (chk : allSites freePhase P = true) :
    PieceOK StairPhysicalInventory.physicalHoles PP P := by
  refine ⟨arena,?_⟩
  intro x hx
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  change StairOuterPlacement.phasePlace x ∉ _
  rw [StairPlaceFast.phasePlace_eqB]
  exact of_decide_eq_true (allSites_sound chk x hx)

private theorem rows {P : Program}
    (h : ∀q∈wires P,q ∈ StairPhysicalPrimitives.rowSitesL 87) :
    PieceOK StairPhysicalInventory.physicalHoles PP (renameProgram StairPhysicalLayout.phaseRelabel P) := by
  refine ⟨(phaseRows39 h).1,?_⟩
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  change StairOuterPlacement.phasePlace (StairPhysicalLayout.phaseRelabel x) ∉ _
  rw [StairPlaceFast.phasePlace_eqB,StairPhysicalV3.phaseRelabel_eqB]
  exact of_decide_eq_true (List.all_eq_true.mp
    (by decide +kernel : (StairPhysicalPrimitives.rowSitesL 87).all (fun r =>
      decide (StairPlaceFast.phasePlaceB (StairPlaceFast.phaseHostB (StairPlaceFast.fieldPlaceB r))
        ∉ StairPhysicalLayout.newHolesNat)) = true) x (h x hx))

private theorem orient : PieceOK StairPhysicalInventory.physicalHoles PP (renameProgram StairV3Primitives.xRelabel (StairV3Primitives.orient 425)) := checked firstOrient39.1 (by decide +kernel)
private theorem packRow : PieceOK StairPhysicalInventory.physicalHoles PP (renameProgram (OB5.sig 425) (Rolling1588.Integer.packFirst base true 425)) := checked firstPacket39.1 (by decide +kernel)
private theorem unpackRow : PieceOK StairPhysicalInventory.physicalHoles PP (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)) := checked firstUnpacket39.1 (by decide +kernel)
private theorem move : PieceOK StairPhysicalInventory.physicalHoles PP StairPhysicalLayout.phaseBMove := checked phaseBMove39.1 (by decide +kernel)
private theorem back : PieceOK StairPhysicalInventory.physicalHoles PP StairPhysicalPhase.phaseBReturn := checked phaseBReturn39.1 (by decide +kernel)

theorem pack : PieceOK StairPhysicalInventory.physicalHoles PP StairV3Primitives.firstPack := by
  unfold StairV3Primitives.firstPack
  exact PieceOK.append (PieceOK.append (PieceOK.append orient packRow) move)
    (rows (StairPhysicalPrimitives.pack_rows 87 (by decide)))

theorem unpack : PieceOK StairPhysicalInventory.physicalHoles PP StairV3Primitives.firstUnpack := by
  unfold StairV3Primitives.firstUnpack
  exact PieceOK.append (PieceOK.append (PieceOK.append
    (rows (StairPhysicalPrimitives.unpack_rows 87 (by decide))) back) unpackRow) orient

end ECDSAAdd.Entrant.Stair44FirstRow

end

section

namespace ECDSAAdd.Entrant.Stair44OuterSites
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy Stair44PointMap
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

theorem ysFit : yList.all (fun r => fit (StairPlaceFast.ugB (duringY r)))=true := by decide +kernel

private def e1B (q : Nat) : Nat :=
  StairPlaceFast.swB 1558 736 (StairPlaceFast.swB 1557 738 (StairPlaceFast.swB 1042 737
    (StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
      (StairPlaceFast.swB 527 741 q))))))

private theorem e1_eq (q : Wire) : E1QubitPlacement.sig (E1QubitPlacement.rho q) = e1B q := by
  unfold E1QubitPlacement.sig E1QubitPlacement.phaseHost E1QubitPlacement.nativeSwap
    E1QubitPlacement.rho e1B
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl

/-- `pmapR L0` in closed form (`StairPlaceFast.wireFn2_eqB`). -/
private def pmB (q : Nat) : Nat :=
  StairPlaceFast.pwB (StairPlaceFast.swB 785 1813 (e1B q) - 16)

private theorem pmapR_fast (q : Wire) : E1QubitPlacement.pmapR layout q = pmB q := by
  show wireFn2 Baselines.layout (E1QubitPlacement.sig (E1QubitPlacement.rho q)) = _
  rw [StairPlaceFast.wireFn2_eqB, e1_eq]
  rfl

theorem xsFit (q : Wire) (hq : q ∈ xList) :
    fit (StairPlaceFast.ugB (duringX (E1QubitPlacement.pmapR layout q))) = true := by
  rw [pmapR_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    xList.all (fun r => fit (StairPlaceFast.ugB (duringX (pmB r)))) = true) q hq

end ECDSAAdd.Entrant.Stair44OuterSites

end

section

namespace ECDSAAdd.Entrant.Stair44WalkExit
open Arithmetic MappedCompressed
set_option maxRecDepth 15000
set_option maxHeartbeats 1200000
attribute [local irreducible] run wires Rolling1588.Integer.encodePrefix Rolling1588.allEncode

private theorem prefix4 (d : Bool) (j : Nat) :
    Rolling1588.Integer.encodePrefix base d (5*j+5) = Rolling1588.allEncode base d j := by
  let n := 5*j
  have step (l : Nat) (out : l % 5 ≠ 0) :
      Rolling1588.Integer.encodePrefix base d (l+1) = Rolling1588.Integer.encodePrefix base d l := by
    rw [Rolling1588.Integer.encodePrefix, Rolling1588.Integer.packAfter,
      if_neg (fun h => out (History5.packDue_true l h).2), List.append_nil]
  change Rolling1588.Integer.encodePrefix base d (n+4+1) = _
  rw [step (n+4) (by dsimp [n]; omega),step (n+3) (by dsimp [n]; omega),
    step (n+2) (by dsimp [n]; omega),step (n+1) (by dsimp [n]; omega)]
  exact Rolling1588.Integer.encodePrefix_index base d j

private theorem stock_prefix (d : Bool) (i : Nat) (hi : i∈[425,505,506]) :
    Rolling1588.Integer.encodePrefix base d i = Rolling1588.allEncode base d ((i-1)/5) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with e|e|e <;> subst i
  · exact prefix4 d 84
  · exact prefix4 d 100
  · exact Rolling1588.Integer.encodePrefix_index base d 101

private theorem raw_away (d : Bool) (j : Nat) (n : Nat) (hn : n ∈ [1026,1541,1542])
    (bound : 5*j ≤ 512) : base n ∉ wires (Rolling1588.allEncode base d j) := by
  intro used
  have h := List.mem_toFinset.mp (Rolling1588.allEncode_history_support base d j bound used)
  rcases List.mem_append.mp h with a|a
  all_goals obtain ⟨t,ht,et⟩ := List.mem_map.mp a
  all_goals have ht' := List.mem_range'_1.mp ht
  all_goals have e := Nat.add_right_cancel et
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  all_goals omega

def atExit : List Wire := [base 1542,base 1541,base 1026,base (Placement5.H 0), base (Placement5.H 1)]

theorem ready (d : Bool) (i x p : Nat) (hi : i∈[425,505,506])
    (hp0 : 0 < p) (hpo : p%2=1) (s : State) (stage : Rolling1588.Integer.Stage base d x p i s.basis) :
    ∀ q∈atExit, (pullState (OB5.sig (i-1)) s).basis q = false := by
  have range : 425 ≤ i ∧ i ≤ 506 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  obtain ⟨raw,hraw,bits⟩ := stage
  let n := (i-1)/5
  have bound : 5*n ≤ i := by dsimp [n]; omega
  have labels : ∀q∈atExit, OB5.sig (i-1) q=q :=
    (by decide +kernel : ∀ i∈[425,505,506], ∀ q ∈ atExit, OB5.sig (i-1) q = q) i hi
  have bits' : s.basis = (run (Rolling1588.allEncode base d n) [] raw).basis := bits.trans (by rw [stock_prefix d i hi])
  have f := (W.compactSkywalkStage_fields_iff base _ i (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_, _, _, _, _, carries, _, _, released⟩ := f
  have ca := (regValue_zero _ _).mp carries
  have high : base 1026 ∈ (W.compactSkywalkSignPoolB base i).released :=
    (by decide +kernel : ∀ i∈[425,505,506], base 1026 ∈ (W.compactSkywalkSignPoolB base i).released) i hi
  have old (a : Nat) (ha : a ∈ [1026,1541,1542]) :
      (run (Rolling1588.allEncode base d n) [] raw).basis (base a) = raw.basis (base a) :=
    run_preserves_outside _ [] raw _ (raw_away d n a ha (by omega))
  have legal : NewHistory5.RawLegal base n raw.basis := by
    intro j hj
    exact W.stage_group_legal base base_pool_nodup x p i (5*j) hp0 hpo (by omega) (by omega) _ hraw
  have hole (j : Fin 10) (hj : j=5 ∨ j=9) :=
    Rolling1588.allEncode_hole base d base_pool_nodup n 0 (by omega) (by dsimp [n]; omega) raw [] legal j hj
  intro q hq
  change s.basis (OB5.sig (i-1) q) = false
  rw [labels q hq,congrFun bits']
  simp only [atExit,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with h|h|h|h|h <;> subst q
  · exact (old 1542 (by decide)).trans (ca _ (by decide))
  · exact (old 1541 (by decide)).trans (ca _ (by decide))
  · exact (old 1026 (by decide)).trans (released _ high)
  · exact hole 5 (Or.inl rfl)
  · exact hole 9 (Or.inr rfl)

def firstClean := [500,501,502,503,504,514,723,724,1541,1542]
theorem first_ready (d : Bool) (x p : Nat) (s : State)
    (stage : Rolling1588.Integer.Stage base d x p 1 s.basis) :
    ∀ i∈firstClean, s.basis (base i)=false := by
  obtain ⟨raw,hraw,bits⟩ := stage
  have tiny : Rolling1588.Integer.encodePrefix base d 1 = [] := by
    simp [Rolling1588.Integer.encodePrefix,Rolling1588.Integer.packAfter,History5.packDue]
  rw [tiny] at bits
  have f := (W.compactSkywalkStage_fields_iff base _ 1 (by decide) base_pool_nodup raw.basis).mp hraw
  obtain ⟨_, _, _, _, ext, carry, _, _, _⟩ := f
  have ex (j : Nat) (h1 : 1 ≤ j) (h2 : j < 512) := (ext j h1 h2).1
  have ca := (regValue_zero _ _).mp carry
  intro i hi
  rw [congrFun bits]
  simp only [run] 
  by_cases small : i ≤ 724
  · rw [show i=(i-258)+258 by simp [firstClean] at hi; omega]
    exact ex (i-258) (by simp [firstClean] at hi;omega) (by omega)
  · have mem : i = 1541 ∨ i=1542 := by simp [firstClean] at hi; omega
    rcases mem with e|e <;> subst i <;> exact ca _ (by decide)

end ECDSAAdd.Entrant.Stair44WalkExit

end

section

namespace ECDSAAdd.Entrant.Stair44WalkRun
open Arithmetic MappedCompressed Secp256k1 Stair44WalkMap
set_option maxRecDepth 7000
set_option maxHeartbeats 1000000
attribute [local irreducible] run wires measurementCount Rolling1588TickGap.forward
  Rolling1588.Integer.regularForward

def forward (d : Bool) (after : Nat) : Program :=
  renameProgram first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram rest (Rolling1588TickGap.forward d 16 after)

private theorem split (d : Bool) (i n m : Nat) :
    Rolling1588TickGap.forward d i (n+m) =
      Rolling1588TickGap.forward d i n ++ Rolling1588TickGap.forward d (i+n) m := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward]
  | succ n ih =>
    simp only [Nat.succ_add,Rolling1588TickGap.forward,List.append_assoc]
    rw [ih]
    congr 3; omega

theorem forward_run (d : Bool) (after x : Nat) (hx0 : 0 < x) (hx : x < p)
    (s actual : State) (m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis)
    (input : pullState first actual = s) :
    pullState rest (run (forward d after) m actual) =
      run (Rolling1588TickGap.forward d 1 (15+after)) m s := by
  let a := Rolling1588TickGap.forward d 1 15
  let b := Rolling1588TickGap.forward d 16 after
  let ma := m.take (measurementCount a)
  let mid := run a ma s
  let actualMid := run (renameProgram first a) ma actual
  have ready : pullState first actualMid = mid := by
    change pullState first (run (renameProgram first a) ma actual) = run a ma s
    rw [run_rename _ first.injective, input]
  obtain ⟨hp0,hpo,hp,coprime⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p + 2^32 ≤ 2^256 := by norm_num [p]
  let t := run (Rolling1588.Integer.regularForward base d 1 15) ma s
  have real : mid = pullState (OB5.sig 15) t := by
    have equal := Rolling1588TickGap.forward_gen d x hx0 hx 15 1 (by decide) (by decide) s ma hs
    have init : pullState (OB5.sig 0) s = s := by
      apply State.extensionality _ s
      · rfl
      · funext q; exact congrArg s.basis (OB5.sig_zero q)
    rw [init] at equal
    exact equal
  have stage : Rolling1588.Integer.Stage base d x p 16 t.basis :=
    (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
      1 15 hp0 hx0 hpo hp gap hx coprime (by decide) s ma hs).2
  have changed : pullState rest actualMid = mid := by
    rw [real]
    exact stage_switch d x p hp0 hpo t actualMid id stage (ready.trans real)
  rw [split d 1 15 after, forward, run_append, run_append, (renameProgram_counts first a).2]
  change pullState rest (run (renameProgram rest b) (m.drop (measurementCount a)) actualMid) =
    run b (m.drop (measurementCount a)) mid
  rw [run_rename _ rest.injective, changed]

def backward (d : Bool) (after : Nat) : Program :=
  renameProgram rest (Rolling1588.reverse d 16 after) ++
  renameProgram first (Rolling1588.reverse d 1 15)

private theorem rsplit (d : Bool) (i n m : Nat) :
    Rolling1588.reverse d i (n+m) =
      Rolling1588.reverse d (i+n) m ++ Rolling1588.reverse d i n := by
  induction n generalizing i with
  | zero => simp [Rolling1588.reverse]
  | succ n ih =>
    simp only [Nat.succ_add, Rolling1588.reverse, ih, List.append_assoc]
    congr 3

theorem backward_run (d : Bool) (after x : Nat) (bound : 16 + after ≤ 512)
    (hx0 : 0 < x) (hx : x < p) (s v actual : State) (enc m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base, v.basis q =
      (run (Rolling1588.Integer.regularForward base d 16 after) enc s).basis q)
    (input : pullState rest actual = pullState (OB5.sig (16 + after - 1)) v) :
    pullState first (run (backward d after) m actual) =
      run (Rolling1588.reverse d 1 (15+after)) m (pullState (OB5.sig (16 + after - 1)) v) := by
  let a := Rolling1588.reverse d 16 after
  let b := Rolling1588.reverse d 1 15
  let ma := m.take (measurementCount a)
  let t := run (Rolling1588.Integer.regularReverse base d 16 after) ma v
  let mid := run a ma (pullState (OB5.sig (16+after-1)) v)
  let actualMid := run (renameProgram rest a) ma actual
  have ready : pullState rest actualMid = mid := by
    change pullState rest (run (renameProgram rest a) ma actual) = _
    rw [run_rename _ rest.injective,input]
  have result := Rolling1588.Integer.reverse_gen d x hx0 hx after 16 (by decide) bound s enc v ma hs agree
  have mid_eq : mid = pullState (OB5.sig 15) t := by
    change run (Rolling1588.reverse d 16 after) _ _ = _
    rw [← Rolling1588.Integer.reverse_eq_packets]
    exact result.1
  obtain ⟨hp0,hpo,_,_⟩ := StackOB5.prime_facts x hx0 hx
  have pool : switchSites.all (fun q => decide (OB5.sig 15 q ∈ skywalkPoolWires base)) = true := by
    decide +kernel
  have clean : ∀q∈switchSites, mid.basis q = false := by
    intro q hq
    rw [mid_eq]
    change t.basis (OB5.sig 15 q) = false
    have member := of_decide_eq_true (List.all_eq_true.mp pool q hq)
    exact (result.2 _ member).trans (stage_clean d x p hp0 hpo s hs q hq)
  have changed : pullState first actualMid = mid := (switch_at actualMid mid id clean).mpr ready
  rw [rsplit d 1 15 after, backward, run_append, run_append, (renameProgram_counts rest a).2]
  change pullState first (run (renameProgram first b) (m.drop (measurementCount a)) actualMid) =
    run b (m.drop (measurementCount a)) mid
  rw [run_rename _ first.injective,changed]

theorem metrics (d : Bool) (n : Nat) :
    (toffoliCount (forward d n) = toffoliCount (Rolling1588TickGap.forward d 1 (15+n)) ∧
     measurementCount (forward d n) = measurementCount (Rolling1588TickGap.forward d 1 (15+n)) ∧
     Challenge.gateSlots (forward d n) = Challenge.gateSlots (Rolling1588TickGap.forward d 1 (15+n))) ∧
    (toffoliCount (backward d n) = toffoliCount (Rolling1588.reverse d 1 (15+n)) ∧
     measurementCount (backward d n) = measurementCount (Rolling1588.reverse d 1 (15+n)) ∧
     Challenge.gateSlots (backward d n) = Challenge.gateSlots (Rolling1588.reverse d 1 (15+n))) := by
  rw [split d 1 15 n,rsplit d 1 15 n]
  simp only [forward,backward,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,Baselines.rename_gateSlots, and_self]

end ECDSAAdd.Entrant.Stair44WalkRun

end

section

namespace ECDSAAdd.Entrant.ArchiveFieldScratch
open ECDSAAdd Arithmetic MappedCompressed
open StairPhysicalLayout StairOuterPlacement StairField2V3Delta StairField2V3Replay

def indices := List.range' 8 104
def hole (k : Nat) := OB5.sig 511 (base (Placement5.H k))
def phys (k : Nat) := StairPlaceFast.outerPlaceB (hole k)

set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

theorem inventory : indices.length=104 ∧ (indices.map phys).Nodup ∧
    indices.all (fun k => Stair44OuterSites.fit (phys k) &&
      decide (hole k ∉ futurePayload 87) && decide (hole k ∉ hosts 87) &&
      decide (hole k ∉ StairSchedule.exclusiveRoles)) = true := by decide +kernel

theorem clean (cut : Nat) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (X Y : Fp) (r : State) (frame : Rolling1588.CutFrame cut origin X Y r)
    (k : Nat) (hk : k∈indices) : r.basis (base (Placement5.H k)) = false := by
  have bound : k<204 := by
    have h := List.mem_range'_1.mp hk
    omega
  exact Rolling1588.cutFrame_zero_region cut origin ctx X Y r frame _ (Or.inr (Placement5.H_region k bound))

theorem in_selected (actual reference : State) (same : AgreeOutside (Δv 87) actual reference)
    (k : Nat) (hk : k∈indices) (zero : reference.basis (fieldPlace (hole k))=false) :
    actual.basis (fieldPlace (hole k))=false := by
  have tab := List.all_eq_true.mp inventory.2.2 _ hk
  have off : hole k∉futurePayload 87 := by
    simp only [Bool.and_eq_true,decide_eq_true_eq] at tab
    exact tab.1.1.2
  apply Eq.trans (same.2 _ ?_) zero
  intro h
  obtain ⟨q,hq,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  exact off (StairOuterPlacement.fieldPlace_injective eq ▸ hq)
open StairField2V3RecScratch

theorem outsideEP : indices.all (fun k => decide (hole k ∉ EP)) = true := by decide +kernel

theorem division_clean (c : Nat) (t actual : State) (inv : Inv c t)
    (same : AgreeOutside (Δv 87) actual t) (k : Nat) (hk : k ∈ indices) :
    actual.basis (fieldPlace (hole k)) = false := by
  obtain ⟨origin, X, Y, s, ctx, _, frame, agree⟩ := inv
  apply in_selected _ _ same _ hk
  change (StairField2V3Seg.pullIn t).basis (hole k) = false
  rw [agree _ (off_of_not_EP _ (of_decide_eq_true (List.all_eq_true.mp outsideEP _ hk)))]
  exact clean _ _ ctx X Y _ frame _ hk

theorem multiplication_clean (x c : Nat) (t actual : State)
    (inv : StairField2V3ExitRec.InvE x c t)
    (same : AgreeOutside (Δv 87) actual t) (k : Nat) (hk : k ∈ indices) :
    actual.basis (fieldPlace (hole k)) = false := by
  obtain ⟨origin, X, Y, s, ctx, _, _, _, frame, agree⟩ := inv
  apply in_selected _ _ same _ hk
  change (StairField2V3Seg.pullIn t).basis (hole k) = false
  rw [agree _ (off_of_not_EP _ (of_decide_eq_true (List.all_eq_true.mp outsideEP _ hk)))]
  exact clean _ _ ctx X Y _ frame _ hk

def packetSites (j : Nat) : List Wire := (List.range 10).flatMap (fun i =>
  [letterSite (5*j+i)] ++ (if i%5=2 ∨ i%5=4 then [] else [sLetter (5*j+i)]))

def layout (j : Nat) := (packetSites j).map StairPlaceFast.outerPlaceB ++ 4835 :: indices.map phys

theorem tag_root : StairPlaceFast.outerPlaceB (base 720) = 4835 := by decide +kernel

def layoutOK (j : Nat) : Bool :=
  (layout j).length == 121 && decide (layout j).Nodup &&
    (layout j).all (fun q => q == 4835 || Stair44OuterSites.fit q)

def transientPhysical : List Wire := [4909, 4911, 4914, 4916, 4919, 4921, 4924, 4926, 4929, 4931, 4934, 4936, 4939, 4941, 4944, 4946, 4949, 4951, 4954, 4956, 4959, 4961, 4964, 4966, 4969, 4971, 4974, 4976, 4979, 4981, 4984, 4986, 4989, 4991, 4994, 4996, 4999, 5001, 5004, 5006, 5009, 5011, 5014, 5016, 5019, 5021, 5024, 5026, 5029, 5031, 5034, 5036, 5039, 5041, 5044, 5046, 5049, 5051, 5054, 5056, 5059, 5061, 5064, 5066, 5069, 5071, 5074, 5076, 5079, 5081, 5084, 5086, 5089, 5091, 5094, 5096, 5099, 5101, 5104, 5106, 5109, 5111, 5114, 5116, 5119, 5121, 5124, 5126, 5129, 5131, 5134, 5136, 5139, 5141, 0, 5653, 5650, 5648, 5645, 5643, 5640, 5638, 5635, 5633]

theorem transient_exact : indices.map phys = transientPhysical := by decide +kernel

theorem permanent_exact : (4835 :: transientPhysical).Nodup ∧
    transientPhysical.all Stair44OuterSites.fit = true := by decide +kernel

def packetOK (j : Nat) : Bool := Id.run do
  let a := (packetSites j).map StairPlaceFast.outerPlaceB
  return a.length == 16 && decide a.Nodup && a.all (fun q =>
    Stair44OuterSites.fit q && decide (q ∉ 4835 :: transientPhysical))

private theorem p1 : ((List.range' 1 4).all packetOK) = true := by decide +kernel
private theorem p5 : ((List.range' 5 4).all packetOK) = true := by decide +kernel
private theorem p9 : ((List.range' 9 4).all packetOK) = true := by decide +kernel
private theorem p13 : ((List.range' 13 4).all packetOK) = true := by decide +kernel
private theorem p17 : ((List.range' 17 4).all packetOK) = true := by decide +kernel
private theorem p21 : ((List.range' 21 4).all packetOK) = true := by decide +kernel
private theorem p25 : ((List.range' 25 4).all packetOK) = true := by decide +kernel
private theorem p29 : ((List.range' 29 4).all packetOK) = true := by decide +kernel
private theorem p33 : ((List.range' 33 4).all packetOK) = true := by decide +kernel
private theorem p37 : ((List.range' 37 4).all packetOK) = true := by decide +kernel
private theorem p41 : ((List.range' 41 4).all packetOK) = true := by decide +kernel
private theorem p45 : ((List.range' 45 4).all packetOK) = true := by decide +kernel
private theorem p49 : ((List.range' 49 4).all packetOK) = true := by decide +kernel
private theorem p53 : ((List.range' 53 4).all packetOK) = true := by decide +kernel
private theorem p57 : ((List.range' 57 4).all packetOK) = true := by decide +kernel
private theorem p61 : ((List.range' 61 4).all packetOK) = true := by decide +kernel
private theorem p65 : ((List.range' 65 4).all packetOK) = true := by decide +kernel
private theorem p69 : ((List.range' 69 4).all packetOK) = true := by decide +kernel
private theorem p73 : ((List.range' 73 4).all packetOK) = true := by decide +kernel
private theorem p77 : ((List.range' 77 4).all packetOK) = true := by decide +kernel
private theorem p81 : ((List.range' 81 3).all packetOK) = true := by decide +kernel

theorem packets_exact : (List.range' 1 83).all packetOK = true := by
  change (List.range' 1 4 ++ List.range' 5 4 ++ List.range' 9 4 ++ List.range' 13 4 ++ List.range' 17 4 ++ List.range' 21 4 ++ List.range' 25 4 ++ List.range' 29 4 ++ List.range' 33 4 ++ List.range' 37 4 ++ List.range' 41 4 ++ List.range' 45 4 ++ List.range' 49 4 ++ List.range' 53 4 ++ List.range' 57 4 ++ List.range' 61 4 ++ List.range' 65 4 ++ List.range' 69 4 ++ List.range' 73 4 ++ List.range' 77 4 ++ List.range' 81 3).all packetOK = true
  simp only [List.all_append, p1, p5, p9, p13, p17, p21, p25, p29, p33, p37, p41, p45, p49, p53, p57, p61, p65, p69, p73, p77, p81, Bool.and_self]

end ECDSAAdd.Entrant.ArchiveFieldScratch

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
open CodecBitSliceVerify StairArchiveGates
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

theorem checked (q : Nat) (h : q<23) : checks q = true := by
  interval_cases q
  · exact q0
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · exact q5
  · exact q6
  · exact q7
  · exact q8
  · exact q9
  · exact q10
  · exact q11
  · exact q12
  · exact q13
  · exact q14
  · exact q15
  · exact q16
  · exact q17
  · exact q18
  · exact q19
  · exact q20
  · exact q21
  · exact q22

def toDigit (p : Bool × Bool) : Fin 3 :=
  if p.1 then 2 else if p.2 then 1 else 0

def rank5 (a b c d e : Fin 3) : Nat := 81*a.val+27*b.val+9*c.val+3*d.val+e.val
def rankAt (cells : Nat → Bool × Bool) (k : Nat) := rank5
  (toDigit (cells k)) (toDigit (cells (k+1))) (toDigit (cells (k+2)))
  (toDigit (cells (k+3))) (toDigit (cells (k+4)))

private theorem radix : ∀ a b c d e : Fin 3, rank5 a b c d e < 243 ∧
    ∀ i : Fin 5, rank5 a b c d e / 3^(4-i.val) % 3 =
      ([a.val,b.val,c.val,d.val,e.val] : List Nat)[i.val]! := by decide +kernel

theorem rank_lt (cells : Nat → Bool × Bool) (k : Nat) : rankAt cells k < 243 :=
  (radix _ _ _ _ _).1

theorem digit_at (cells : Nat → Bool × Bool) (k i : Nat) (hi : i<5) :
    rankAt cells k / 3^(4-i) % 3 = (toDigit (cells (k+i))).val := by
  have h := (radix (toDigit (cells k)) (toDigit (cells (k+1))) (toDigit (cells (k+2)))
    (toDigit (cells (k+3))) (toDigit (cells (k+4)))).2 ⟨i,hi⟩
  interval_cases i <;> exact h

def letterBit (p : Bool × Bool) (q : Nat) := if q%2=0 then p.1 else p.2

theorem ranked_letter (cells : Nat → Bool × Bool) (k q : Nat) (hq : q<10)
    (ok : cells (k+q/2) ≠ (true,true)) :
    trit q (rankAt cells k) = letterBit (cells (k+q/2)) q := by
  unfold trit
  rw [digit_at cells k (q/2) (by omega)]
  generalize hh : cells (k+q/2)=p at *
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> by_cases t : q%2=0 <;> simp_all [toDigit,letterBit]

def rawBit (cells : Nat → Bool × Bool) (far u c : Bool) (q : Nat) : Bool :=
  if q<20 then letterBit (cells (q/2)) q
  else if q=20 then far else if q=21 then u else c

def nearRow (cells : Nat → Bool × Bool) := 243*rankAt cells 0 + rankAt cells 5

theorem near_member (cells : Nat → Bool × Bool) (ok : ∀ i<10, cells i ≠ (true,true)) :
    nearRow cells < 63145 ∧ ∀ q<23, (rawCol q).testBit (nearRow cells) =
      rawBit cells false false false q := by
  have hi := rank_lt cells 0
  have lo := rank_lt cells 5
  refine ⟨by unfold nearRow; omega, ?_⟩
  intro q hq
  rw [nearRow, near_bit q _ _ (checked q hq) hi lo]
  unfold rawBit
  by_cases h : q<10
  · rw [if_pos h, if_pos (by omega : q<20)]
    simpa only [Nat.zero_add] using ranked_letter cells 0 q h (by apply ok; omega)
  · rw [if_neg h]
    by_cases t : q<20
    · rw [if_pos t, if_pos t]
      have div : 5+(q-10)/2=q/2 := by omega
      have rem : (q-10)%2=q%2 := by omega
      rw [ranked_letter cells 5 (q-10) (by omega) (by apply ok; omega), div]
      unfold letterBit
      rw [rem]
    · simp [t]

def farCells (u : Bool) (mask i : Nat) : Bool × Bool :=
  (!(mask.testBit i), !u && mask.testBit i && (mask % 2^i == 0))

def farRow (u c : Bool) (mask : Nat) := 59049 + 1024*(2*u.toNat+c.toNat)+mask

theorem far_member (u c : Bool) (mask : Nat) (hm : mask<1024) :
    farRow u c mask < 63145 ∧ ∀ q<23, (rawCol q).testBit (farRow u c mask) =
      rawBit (farCells u mask) true u c q := by
  let group := 32*u.toNat+16*c.toNat+mask/64
  let lo := mask%64
  have split : farRow u c mask=59049+64*group+lo := by
    cases u <;> cases c <;> simp [farRow, group, lo] <;> omega
  have limit : group<64 := by cases u <;> cases c <;> simp [group] <;> omega
  have low : lo<64 := Nat.mod_lt _ (by decide)
  have packed : group%16*64+lo=mask := by cases u <;> cases c <;> simp [group,lo] <;> omega
  have utag : decide (32≤group)=u := by cases u <;> cases c <;> simp [group] <;> omega
  have ctag : decide (group/16%2=1)=c := by cases u <;> cases c <;> simp [group] <;> omega
  refine ⟨by omega, ?_⟩
  intro q hq
  rw [split, far_bit q group lo (checked q hq) limit low]
  simp only [farBit, packed, utag, ctag, rawBit, letterBit, farCells]

end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.Stair44WalkSites
open Arithmetic MappedCompressed
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def retired : List Wire := [base 1542,base 1026,base 1541,base 723,base 724]
def blocked (i : Nat) : List Wire := if i < 16 then
  [base 500,base 514,base 501,base 723,base 724]
  else [base (Placement5.H 0),base 514,base (Placement5.H 1),base 723,base 724]

def interval (a b q : Nat) : Prop := base a ≤ q ∧ q ≤ base b

def permitted (i q : Nat) : Prop :=
  let n := W.compactSkywalkTickPreWidth i
  interval (i-1) (i+n) q ∨ q = base (1028+i) ∨ interval 770 (770+n-1) q ∨
  interval 1540 (1540+n-2) q ∨
  interval (i-5) (i-5+4) q ∨ interval (1028+(i-5)) (1028+(i-5)+4) q

private def inB (a b q : Nat) := Nat.ble (a+16) q && Nat.ble q (b+16)

private def allowed (i q : Nat) : Bool :=
  let n := W.compactSkywalkTickPreWidth i
  inB (i-1) (i+n) q || Nat.beq q (1028+i+16) || inB 770 (770+n-1) q ||
    inB 1540 (1540+n-2) q || inB (i-5) (i-5+4) q || inB (1028+(i-5)) (1028+(i-5)+4) q

private theorem allowed_spec (i q : Nat) : allowed i q = true ↔ permitted i q := by
  simp [allowed,permitted,inB,interval,base,Bool.and_eq_true,Bool.or_eq_true,Nat.ble_eq,
    Nat.beq_eq,or_assoc]

private theorem table : (List.range' 1 505).all (fun i => (blocked i).all
    (fun q => !allowed i (OB5.sig i q))) = true := by decide +kernel

private theorem no_label {i q : Nat} (hi : i ∈ List.range' 1 505) (hq : q ∈ blocked i) :
    ¬permitted i (OB5.sig i q) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp table i hi) q hq
  intro hp
  rw [(allowed_spec _ _).mpr hp] at h
  exact Bool.noConfusion h

private theorem block_range {a n q : Nat} (h : q ∈ wireBlock base a n) :
    base a ≤ q ∧ q < base (a+n) := by
  obtain ⟨i,mi,rfl⟩ := List.mem_map.mp h
  obtain ⟨lo,hi⟩ := List.mem_range'_1.mp mi
  change a+16 ≤ i+16 ∧ i+16 < a+n+16
  omega

private theorem tick_sites (i : Nat) (hpos : 0 < i) (hi : i < 512) (q : Wire)
    (hq : q ∈ (W.compactSkywalkTickLayout base i).wires) : permitted i q := by
  have n := (W.compactSkywalkTick_width_bounds i hi).1
  let k := W.compactSkywalkTickPreWidth i
  change 3 ≤ k at n
  change q ∈ _ :: _ :: _ :: _ :: _ :: ((_ ++ [_]) ++ (_ ++ [_]) ++ _) at hq
  simp only [List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] at hq
  change (q = base (skywalkPoolPreviousId i) ∨ q = base (1028+i) ∨ q = base (i+k) ∨
    q = base i ∨ q = base 770 ∨ ((q ∈ wireBlock base (i+1) (k-2) ∨ q = base (i+k-1)) ∨
    (q ∈ wireBlock base 771 (k-2) ∨ q = base (770+k-1))) ∨ q ∈ wireBlock base 1540 (k-1)) at hq
  unfold permitted interval
  dsimp only [k] at hq n
  rcases hq with h|h|h|h|h|((h|h)|(h|h))|h
  · unfold skywalkPoolPreviousId at h
    rw [if_neg (by omega)] at h
    subst q
    left; constructor <;> simp only [base,Wire] <;> omega
  · exact Or.inr (Or.inl h)
  · subst q; left; constructor <;> simp only [base,Wire] <;> omega
  · subst q; left; constructor <;> simp only [base,Wire] <;> omega
  · subst q; right; right; left; constructor <;> simp only [base,Wire] <;> omega
  · obtain ⟨lo,hi'⟩ := block_range h
    left; constructor <;> simp only [base,Wire] at * <;> omega
  · subst q; left; constructor <;> simp only [base,Wire] <;> omega
  · obtain ⟨lo,hi'⟩ := block_range h
    right; right; left; constructor <;> simp only [base,Wire] at * <;> omega
  · subst q; right; right; left; constructor <;> simp only [base,Wire] <;> omega
  · obtain ⟨lo,hi'⟩ := block_range h
    right; right; right; left; constructor <;> simp only [base,Wire] at * <;> omega

private def packetWires (i : Nat) : Finset Wire :=
  Finset.univ.image (History5.historyMap base (i-5))

private theorem first_packet (d : Bool) :
    wires (Rolling1588.Integer.packFirst base d 5) ⊆ packetWires 5 ∧
    wires (Rolling1588.unpackAtTick d 5) ⊆ packetWires 5 := by cases d <;> decide +kernel

private theorem packet_sites (d : Bool) (i q : Nat)
    (hq : q ∈ wires (Rolling1588.Integer.packFirst base d i) ∨
      q ∈ wires (Rolling1588.unpackAtTick d i)) : permitted i q := by
  have site : ∃ j : Fin 10, q = History5.historyMap base (i-5) j := by
    by_cases first : i=5
    · subst i
      have hp : q ∈ packetWires 5 := hq.elim (fun h => (first_packet d).1 h) (fun h => (first_packet d).2 h)
      obtain ⟨j,_,e⟩ := Finset.mem_image.mp hp
      exact ⟨j,e.symm⟩
    · rcases hq with h|h
      · rw [Rolling1588.Integer.packFirst,if_neg first,Rolling1588.Integer.pack_support_eq] at h
        unfold History5.packAfter at h
        split at h
        · exact History5.history_gate_mem base (i-5) _ (Or.inl rfl) q h
        · simp [wires] at h
      · rw [← Rolling1588.Integer.unpackFirst_base,Rolling1588.Integer.unpackFirst,if_neg first,
          Rolling1588.Integer.decodeBefore_support_eq] at h
        unfold History5.decodeBefore at h
        split at h
        · exact History5.history_gate_mem base (i-5) _ (Or.inr rfl) q h
        · simp [wires] at h
  obtain ⟨j,rfl⟩ := site
  have lim := j.isLt
  unfold permitted interval History5.historyMap History5.historyId
  right; right; right; right
  split_ifs
  · left; constructor <;> simp only [base,Wire] <;> omega
  · right; constructor <;> simp only [base,Wire] <;> omega

private theorem step (d : Bool) (i q : Nat) (hi : i ∈ List.range' 1 505) (hb : q ∈ blocked i) :
    q ∉ wires (renameProgram (OB5.sig i)
      (TickRanges.tick base i ++ Rolling1588.Integer.packFirst base d i)) ∧
    q ∉ wires (renameProgram (OB5.sig i)
      (Rolling1588.unpackAtTick d i ++ W.ReverseCarry.compactReceiverTick base i)) := by
  obtain ⟨lo,up⟩ := List.mem_range'_1.mp hi
  have il : i < 512 := by omega
  have exclude (x : Wire) (eq : OB5.sig i x = q) (hp : permitted i x) : False := by
    have inv := congrArg (OB5.sig i) eq
    rw [OB5.sig_invol i (by omega)] at inv
    exact no_label hi hb (inv ▸ hp)
  constructor <;> intro used <;> rw [renameProgram_support] at used <;>
    obtain ⟨x,member,eq⟩ := Finset.mem_image.mp used <;> apply exclude x eq <;>
    rw [wires_append,Finset.mem_union] at member
  · rcases member with ht|hc
    · exact tick_sites i lo il x (List.mem_toFinset.mp
        (W.repairedTick_support base i il base_pool_nodup
          (TickRanges.tick_support base i il base_pool_nodup ht)))
    · exact packet_sites d i x (Or.inl hc)
  · rcases member with hc|ht
    · exact packet_sites d i x (Or.inr hc)
    · exact tick_sites i lo il x (List.mem_toFinset.mp
        (W.ReverseCarry.compactReceiverTick_support base i il base_pool_nodup ht))

private theorem windows (d : Bool) (q : Wire) (n i : Nat) (lo : 1 ≤ i) (up : i+n ≤ 506)
    (hb : ∀ j, i ≤ j → j < i+n → q ∈ blocked j) :
    q ∉ wires (Rolling1588TickGap.forward d i n) ∧ q ∉ wires (Rolling1588.reverse d i n) := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward,Rolling1588.reverse,wires]
  | succ n ih =>
    have a := step d i q (List.mem_range'_1.mpr ⟨lo,by omega⟩) (hb i (le_refl i) (by omega))
    have b := ih (i+1) (by omega) (by omega) (fun j l h => hb j (by omega) (by omega))
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨a.1,b.1⟩,⟨b.2,a.2⟩⟩

theorem idle514 (d : Bool) (i n : Nat) (lo : 1 ≤ i) (hi : i+n ≤ 506) :
    base 514 ∉ wires (Rolling1588TickGap.forward d i n) ∧
    base 514 ∉ wires (Rolling1588.reverse d i n) :=
  windows d _ n i lo hi (fun j _ _ => by unfold blocked; split <;> simp)

private theorem early_map : ∀ z ∈ retired, ∀ y : Wire, Stair44WalkMap.first y=z →
    y ∈ blocked 1 := by
  intro z hz y eq
  have r := congrArg Stair44WalkMap.first.symm eq
  rw [Equiv.symm_apply_apply] at r
  rw [r]
  exact (by decide +kernel : ∀z∈retired, Stair44WalkMap.first.symm z ∈ blocked 1) z hz

private theorem late_map : ∀ z ∈ retired, ∀ y : Wire, Stair44WalkMap.rest y=z →
    y ∈ blocked 16 := by
  intro z hz y eq
  have r := congrArg Stair44WalkMap.rest.symm eq
  rw [Equiv.symm_apply_apply] at r
  rw [r]
  exact (by decide +kernel : ∀z∈retired, Stair44WalkMap.rest.symm z ∈ blocked 16) z hz

attribute [local irreducible] wires renameProgram Rolling1588.reverse Rolling1588TickGap.forward
theorem routed_free (d : Bool) (n : Nat) (le : 16+n ≤ 506) (q : Wire) (hq : q∈retired) :
    q ∉ wires (Stair44WalkRun.forward d n) ∧ q ∉ wires (Stair44WalkRun.backward d n) := by
  have a (w : Wire) (eq : Stair44WalkMap.first w=q) := windows d w 15 1 (by decide) (by decide)
    (fun j _ hj => by simpa [blocked,show j<16 by omega] using early_map q hq w eq)
  have b (w : Wire) (eq : Stair44WalkMap.rest w=q) := windows d w n 16 (by decide) le
    (fun j hj _ => by simpa [blocked,show ¬j<16 by omega] using late_map q hq w eq)
  unfold Stair44WalkRun.forward Stair44WalkRun.backward
  simp only [wires_append,Finset.mem_union,renameProgram_support,Finset.mem_image,not_or]
  exact ⟨⟨fun ⟨w,hw,e⟩ => (a w e).1 hw, fun ⟨w,hw,e⟩ => (b w e).1 hw⟩,
    ⟨fun ⟨w,hw,e⟩ => (b w e).2 hw,fun ⟨w,hw,e⟩ => (a w e).2 hw⟩⟩

end ECDSAAdd.Entrant.Stair44WalkSites

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
open Arithmetic MappedCompressed ArchiveFieldScratch StairPhysicalLayout

set_option maxHeartbeats 900000
set_option maxRecDepth 22000

def rebinder : List Wire → List Wire → Equiv.Perm Wire
  | r::rs,h::hs => (rebinder rs hs).trans (Equiv.swap r h)
  | _, _ => Equiv.refl _

theorem hosts_eq (rs hs : List Wire) (p : Program) :
    StairLoan.rebindMany rs hs p = renameProgram (rebinder rs hs) p := by
  have hid : p = renameProgram id p := (StairField2V3Win.renameProgram_id' p).symm
  induction rs generalizing hs with
  | nil => exact hid
  | cons r rs ih =>
    cases hs with
    | nil => exact hid
    | cons h hs =>
      rw [StairLoan.rebindMany, ih, renameProgram_comp]
      rfl

def host := rebinder StairSchedule.exclusiveRoles (hosts 87)
def packet (d : Bool) (j : Nat) := StairLoan.rebindMany StairSchedule.exclusiveRoles (hosts 87)
  (renameProgram (OB5.sig 511) (StairGroups.packet d 0 j))

def preimage (j : Nat) (q : Wire) := (shifted (Placement5.pi j)).symm (OB5.sig 511 (host.symm q))
def savedSites (j : Nat) (second : Bool) := base 720 ::
  (if second then (packetSites j).take 8 else (packetSites j).drop 8)

def cover (j : Nat) := [base 2400,base 2409,base 2410] ++ Q6EndpointCell.ids.map base ++
  (List.finRange 10).map (History5.historyMap base (5*j))

theorem cover_read (j : Nat) {q : Wire} (used : q ∈ FrontierReplay1591.readSites (5*j)) :
    q ∈ cover j := by
  simp only [FrontierReplay1591.readSites, FrontierReplay1591.fieldSites,
    Finset.mem_union, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton,
    List.mem_cons] at used
  simp only [cover, List.mem_append, List.mem_cons]
  rcases used with ((h | h) | (h | h)) | h
  · tauto
  · tauto
  · tauto
  · tauto
  · have img := (ParityCodec5New.supportAt (History5.historyMap base (5*j))).1 h
    obtain ⟨i, _, eq⟩ := Finset.mem_image.mp img
    exact Or.inr (List.mem_map.mpr ⟨i, List.mem_finRange _, eq⟩)

attribute [local irreducible] wires renameProgram StairGroups.packet Rolling1588.basePacket StairLoan.rebindMany rebinder

theorem original (d : Bool) (j : Nat) (hj : j<102) {q : Wire} (used : q∈wires (packet d j)) :
    preimage j q ∈ cover j := by
  rw [packet, hosts_eq, renameProgram_support] at used
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp used
  rw [renameProgram_support] at hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  rw [StairGroups.packet_zero, Rolling1588.packet, renameProgram_support] at ha
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  have back : preimage j (host (OB5.sig 511 (shifted (Placement5.pi j) r))) = r := by
    simp only [preimage, Equiv.symm_apply_apply, OB5.sig_invol 511 (by decide)]
  exact (back.symm ▸ cover_read j (Rolling1588.basePacket_readSites_support d j hj hr) : preimage j (host (OB5.sig 511 (shifted (Placement5.pi j) r))) ∈ cover j)

def safe (j : Nat) (second : Bool) := (savedSites j second).all (fun q =>
  decide (preimage (if second then j+1 else j) q ∉ cover (if second then j+1 else j)))

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.ArchiveFieldScratch
open Arithmetic
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

def port (j q : Nat) : Wire := (layout j)[q]?.getD q

theorem layout_frame (j : Nat) (hj : j∈List.range' 1 83) :
    (layout j).Nodup ∧ (layout j).length=121 := by
  have h := List.all_eq_true.mp packets_exact j hj
  dsimp only [packetOK, Id.run, pure] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have eq : layout j = (packetSites j).map StairPlaceFast.outerPlaceB ++ 4835 :: transientPhysical := by
    exact congrArg (fun xs => (packetSites j).map StairPlaceFast.outerPlaceB ++ 4835 :: xs) transient_exact
  rw [eq]
  refine ⟨List.nodup_append'.mpr ⟨h.1.2, permanent_exact.1, ?_⟩, ?_⟩
  · apply List.disjoint_left.mpr
    intro q hq
    have val := List.all_eq_true.mp h.2 _ hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at val
    exact val.2
  · rw [List.length_append, h.1.1]
    rfl

theorem port_inj (j : Nat) (hj : j∈List.range' 1 83) :
    ∀ a∈Finset.range 121,∀ b∈Finset.range 121,port j a = port j b → a=b := by
  obtain ⟨hn, hl⟩ := layout_frame j hj
  intro a ha b hb e
  have al : a < (layout j).length := hl ▸ Finset.mem_range.mp ha
  have bl : b < (layout j).length := hl ▸ Finset.mem_range.mp hb
  simp only [port, List.getElem?_eq_getElem al, List.getElem?_eq_getElem bl, Option.getD_some] at e
  exact List.Nodup.getElem_inj_iff hn |>.mp e

def within (w : Nat) (i : Instr) := decide (∀ q∈i.wires, q<w)

theorem bounded {p : Program} (w : Nat) (h : p.all (within w)=true) :
    wires p ⊆ Finset.range w := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have a : ∀ q∈i.wires, q<w := of_decide_eq_true h.1
    rw [wires, Finset.union_subset_iff]
    exact ⟨fun q hq => Finset.mem_range.mpr (a q hq), ih h.2⟩

theorem transfer (j : Nat) (hj : j∈List.range' 1 83) (p : Program)
    (sub : wires p⊆Finset.range 121) (m : List Bool) (s : State) :
    (run (renameProgram (port j) p) m s).phase=(run p m (pullState (port j) s)).phase ∧
    ∀ q∈Finset.range 121, (run (renameProgram (port j) p) m s).basis (port j q)=
      (run p m (pullState (port j) s)).basis q :=
  run_rename_pool _ _ (port_inj _ hj) _ sub _ _ _ rfl (fun _ _ => rfl)

end ECDSAAdd.Entrant.ArchiveFieldScratch

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b0 : (safe 16 false && safe 16 true) = true := by decide +kernel
theorem b1 : (safe 19 false && safe 19 true) = true := by decide +kernel
theorem b2 : (safe 22 false && safe 22 true) = true := by decide +kernel
theorem b3 : (safe 25 false && safe 25 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b4 : (safe 28 false && safe 28 true) = true := by decide +kernel
theorem b5 : (safe 31 false && safe 31 true) = true := by decide +kernel
theorem b6 : (safe 34 false && safe 34 true) = true := by decide +kernel
theorem b7 : (safe 37 false && safe 37 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b8 : (safe 40 false && safe 40 true) = true := by decide +kernel
theorem b9 : (safe 43 false && safe 43 true) = true := by decide +kernel
theorem b10 : (safe 46 false && safe 46 true) = true := by decide +kernel
theorem b11 : (safe 49 false && safe 49 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b12 : (safe 52 false && safe 52 true) = true := by decide +kernel
theorem b13 : (safe 55 false && safe 55 true) = true := by decide +kernel
theorem b14 : (safe 58 false && safe 58 true) = true := by decide +kernel
theorem b15 : (safe 61 false && safe 61 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b16 : (safe 64 false && safe 64 true) = true := by decide +kernel
theorem b17 : (safe 67 false && safe 67 true) = true := by decide +kernel
theorem b18 : (safe 70 false && safe 70 true) = true := by decide +kernel
theorem b19 : (safe 73 false && safe 73 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

theorem b20 : (safe 76 false && safe 76 true) = true := by decide +kernel
theorem b21 : (safe 79 false && safe 79 true) = true := by decide +kernel
theorem b22 : (safe 82 false && safe 82 true) = true := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveRelease
open Arithmetic CodecBitSliceVerify StairArchiveGates ArchiveFieldScratch

inductive Stage where
  | enter0
  | switch0
  | leave0
  | enter1
  | switch1
  | leave1

def program : Stage → Program
  | .enter0 => enter0
  | .switch0 => switch0
  | .leave0 => leave0
  | .enter1 => enter1
  | .switch1 => switch1
  | .leave1 => leave1

def inputCols : Stage → Cols
  | .enter0 => enter0Trace0In
  | .switch0 => switch0Trace0In
  | .leave0 => leave0Trace0In
  | .enter1 => enter1Trace0In
  | .switch1 => switch1Trace0In
  | .leave1 => leave1Trace0In

def outputCols : Stage → Cols
  | .enter0 => enter0Trace3Out
  | .switch0 => switch0Trace2Out
  | .leave0 => leave0Trace3Out
  | .enter1 => enter1Trace3Out
  | .switch1 => switch1Trace2Out
  | .leave1 => leave1Trace2Out

set_option maxRecDepth 20000
set_option exponentiation.threshold 100000
set_option maxHeartbeats 3000000

theorem sub (op : Stage) : wires (program op) ⊆ Finset.range 121 := by
  apply bounded
  cases op <;> decide +kernel

def placed (j : Nat) (op : Stage) := renameProgram (port j) (program op)

private theorem row_run (op : Stage) (row x : Nat) (hr : row < 63145)
    (m : List Bool) (s : State) (bitrow : Rel (inputCols op) x row)
    (data : ∀ q ∈ wires (program op), s.basis q = x.testBit q) :
    (run (program op) m s).phase = s.phase ∧
    (∀ q ∈ wires (program op), (run (program op) m s).basis q = (get (outputCols op) q).testBit row) ∧
    (∀ q ∉ wires (program op), (run (program op) m s).basis q = s.basis q) := by
  have active : (2^63145-1 : Nat).testBit row = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hr
  cases op with
  | enter0 => exact enter0_run row x m s active bitrow data
  | switch0 => exact switch0_run row x m s active bitrow data
  | leave0 => exact leave0_run row x m s active bitrow data
  | enter1 => exact enter1_run row x m s active bitrow data
  | switch1 => exact switch1_run row x m s active bitrow data
  | leave1 => exact leave1_run row x m s active bitrow data

theorem placed_run (j : Nat) (hj : j ∈ List.range' 1 83) (op : Stage)
    (row x : Nat) (hr : row < 63145) (m : List Bool) (s : State)
    (bitrow : Rel (inputCols op) x row)
    (data : ∀ q ∈ wires (program op), s.basis (port j q) = x.testBit q) :
    (run (placed j op) m s).phase = s.phase ∧
    (∀ q ∈ wires (program op), (run (placed j op) m s).basis (port j q) =
      (get (outputCols op) q).testBit row) ∧
    (∀ q ∉ wires (placed j op), (run (placed j op) m s).basis q = s.basis q) := by
  have core := row_run op row x hr m (pullState (port j) s) bitrow data
  have lifted := transfer j hj (program op) (sub op) m s
  exact ⟨lifted.1.trans core.1, fun q hq => (lifted.2 q (sub op hq)).trans (core.2.1 q hq),
    fun q hq => run_preserves_outside _ _ _ q hq⟩

end ECDSAAdd.Entrant.StairArchiveRelease

end

section

namespace ECDSAAdd.Entrant.StairArchiveRelease
open Arithmetic MappedCompressed ArchiveFieldScratch StairPlaceFast CodecBitSliceVerify
set_option maxHeartbeats 500000

attribute [local irreducible] ArchiveFieldScratch.indices hole outerPlaceB layout placed program packetSites port

def fieldSites (j : Nat) := packetSites j ++ (base 720 :: ArchiveFieldScratch.indices.map hole)
def fieldPort (j q : Nat) : Wire := (fieldSites j)[q]?.getD q
def fieldHook (j : Nat) (op : Stage) := renameProgram (fieldPort j) (program op)

theorem field_layout (j : Nat) : (fieldSites j).map outerPlaceB = layout j := by
  have mapped : (ArchiveFieldScratch.indices.map hole).map outerPlaceB = ArchiveFieldScratch.indices.map phys := by
    rw [List.map_map]
    rfl
  unfold layout
  simp only [fieldSites, List.map_append, List.map_cons, mapped, tag_root]

theorem placed_port (j : Nat) (hj : j∈List.range' 1 83) (q : Nat) (hq : q<121) :
    outerPlaceB (fieldPort j q) = port j q := by
  have size := (layout_frame j hj).2
  rw [←field_layout, List.length_map] at size
  have lt : q < (fieldSites j).length := by omega
  simp only [port, ←field_layout, fieldPort, List.getElem?_map, List.getElem?_eq_getElem lt,
    Option.map_some, Option.getD_some]

theorem field_to_root (j : Nat) (hj : j∈List.range' 1 83) (op : Stage) :
    renameProgram outerPlaceB (fieldHook j op) = placed j op := by
  unfold fieldHook placed
  rw [renameProgram_comp]
  exact renameProgram_congr_support _ _ _ (fun q h => placed_port j hj q (Finset.mem_range.mp (sub op h)))

theorem field_inj (j : Nat) (hj : j∈List.range' 1 83) :
    ∀ a∈Finset.range 121,∀ b∈Finset.range 121,fieldPort j a = fieldPort j b → a=b := by
  intro a ha b hb h
  apply port_inj j hj a ha b hb
  rw [←placed_port j hj _ (Finset.mem_range.mp ha), ←placed_port j hj _ (Finset.mem_range.mp hb), h]

end ECDSAAdd.Entrant.StairArchiveRelease

end

section

namespace ECDSAAdd.Entrant.StairArchiveHandoff
open StairArchiveGates CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000

/-- Equality of columns entails bit-for-bit equality for every legal record row. -/
theorem wires_eq (a b : Cols) (width : Nat) (matchWord : a.take width = b.take width)
    (q row : Nat) (hq : q<width) : (get a q).testBit row=(get b q).testBit row := by
  have same := congrArg (fun t : List Nat => t[q]?) matchWord
  simp only [List.getElem?_take, if_pos hq] at same
  exact congrArg (fun z : Option Nat => (z.getD 0).testBit row) same

/-- Eight cross-program joins certify identical chronological 16-bit boundary words.
    field enter0 starts in A and field leave0 ends in B. -/
theorem archive_edges :
    integer_load0Trace5Out.take 16 = enter0Trace0In.take 16 ∧
    integer_load1Trace5Out.take 16 = enter1Trace0In.take 16 ∧
    leave0Trace3Out.take 16 = integer_restore1Trace0In.take 16 ∧
    leave1Trace2Out.take 16 = integer_restore0Trace0In.take 16 ∧
    enter0Trace0In.take 16 = integer_restore0Trace0In.take 16 ∧
    enter1Trace0In.take 16 = integer_restore1Trace0In.take 16 ∧
    leave0Trace3Out.take 16 = enter1Trace0In.take 16 ∧
    leave1Trace2Out.take 16 = enter0Trace0In.take 16 := by decide +kernel

theorem raw_edges :
    integer_load0Trace0In.take 23 = integer_load1Trace0In.take 23 ∧
    integer_restore0Trace6Out.take 23 = integer_load0Trace0In.take 23 ∧
    integer_restore1Trace6Out.take 23 = integer_load0Trace0In.take 23 := by decide +kernel

def value (cs : Cols) (row : Nat) := packBits (cs.map (fun x => x.testBit row))

theorem value_rel (cs : Cols) (row : Nat) : Rel cs (value cs row) row := by
  intro q
  rw [value, pack_testBit, List.getElem?_map]
  change (((cs[q]?).map (fun x => x.testBit row)).getD false) =
    ((cs[q]?).getD 0).testBit row
  cases h : cs[q]? <;> simp

end ECDSAAdd.Entrant.StairArchiveHandoff

end

section

namespace ECDSAAdd.Entrant.StairArchiveInactive

def both (j : Nat) := safe j false && safe j true
def starts : List Nat := [16, 19, 22, 25, 28, 31, 34, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64, 67, 70, 73, 76, 79, 82]
theorem checks : starts.all both = true := by
  simp only [starts, both, List.all_cons, List.all_nil, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, Bool.and_self]

attribute [local irreducible] packet wires preimage cover savedSites

theorem packet_avoids (j : Nat) (hj : j∈starts) (d second : Bool)
    (q : Wire) (save : q∈savedSites j second) :
    q∉wires (packet d (if second then j+1 else j)) := by
  intro used
  have limits : starts.all (fun i => decide (i+1<102)) = true := by decide +kernel
  have within : j+1<102 := of_decide_eq_true (List.all_eq_true.mp limits j hj)
  have pair := List.all_eq_true.mp checks j hj
  have pass : safe j second = true := by
    simp only [both, Bool.and_eq_true] at pair
    cases second
    · exact pair.1
    · exact pair.2
  let k := if second then j+1 else j
  have hk : k<102 := by dsimp only [k]; split <;> omega
  change (savedSites j second).all (fun z => decide (preimage k z ∉ cover k)) = true at pass
  have exc : preimage k q ∉ cover k := of_decide_eq_true (List.all_eq_true.mp pass q save)
  exact exc (original d k hk used)

/-- A real hosted group can consume its own byte with arbitrary other-bank bits and tag. -/
theorem advance (start : Nat) (hs : start∈starts) (d second : Bool) (m : List Bool)
    (reference actual : State)
    (same : ∀ q ∉ savedSites start second, actual.basis q = reference.basis q) :
    let p := packet d (if second then start+1 else start)
    ((run p m actual).phase ^^ actual.phase) = ((run p m reference).phase ^^ reference.phase) ∧
    (∀ q ∉ savedSites start second, (run p m actual).basis q = (run p m reference).basis q) ∧
    (∀ q ∈ savedSites start second, (run p m actual).basis q = actual.basis q) := by
  let p := packet d (if second then start+1 else start)
  have unchanged := packet_avoids start hs d second
  have act := Arithmetic.run_local_increment p actual reference m
    (fun q hq => same q (fun h => unchanged q h hq))
  refine ⟨act.1, ?_, fun q hq => run_preserves_outside p m actual q (unchanged q hq)⟩
  intro q keep
  by_cases used : q∈wires p
  · exact act.2 q used
  · exact (run_preserves_outside p m actual q used).trans ((same q keep).trans
      (run_preserves_outside p m reference q used).symm)

end ECDSAAdd.Entrant.StairArchiveInactive

end

section

namespace ECDSAAdd.Entrant.StairArchiveAllPorts
open Arithmetic MeasuredCodec5 CodecBitSliceVerify StairArchiveGates ArchiveFieldScratch
open StairArchiveHandoff StairArchiveRelease
set_option maxRecDepth 20000
set_option maxHeartbeats 3200000
set_option exponentiation.threshold 100000

theorem mapped (p : Program) (f : Wire → Wire) (width row : Nat) (m : List Bool)
    (actual : State) (source dest : Cols) (mask : Nat) (hm : mask.testBit row = true)
    (checked : eval mask p source = (true, dest))
    (bound : ∀ i ∈ p, target i < source.length)
    (subp : wires p ⊆ Finset.range width)
    (inject : ∀ a∈Finset.range width, ∀ b∈Finset.range width, f a=f b→a=b)
    (data : ∀ q∈Finset.range width, actual.basis (f q)=(get source q).testBit row) :
    (run (renameProgram f p) m actual).phase=actual.phase ∧
    (∀ q ∈ Finset.range width, (run (renameProgram f p) m actual).basis (f q)=
      (get dest q).testBit row) ∧
    (∀ q∉(Finset.range width).image f, (run (renameProgram f p) m actual).basis q=actual.basis q) := by
  let x := value source row
  have hr : Rel source x row := value_rel _ _
  have hEval : (eval mask p source).1 = true := by rw [checked]
  obtain ⟨safe, result⟩ := eval_sound mask row hm p source x bound hr hEval
  rw [checked] at result
  have ref := MeasuredCodec5.run_sim p m actual.phase x
  rw [sim_safe _ _ safe] at ref
  have phys := run_rename_pool f _ inject p subp m ⟨actual.phase,bitsOf x⟩ actual rfl
    (fun q hq => (hr q).trans (data q hq).symm)
  rw [ref] at phys
  exact ⟨phys.1, fun q hq => (phys.2 q hq).trans (result q),
    fun q hq => run_rename_pool_outside f _ p subp m actual q hq⟩

private theorem field_checked (op : Stage) :
    eval (2^63145-1) (program op) (inputCols op) = (true, outputCols op) := by
  cases op with
  | enter0 => exact enter0_checked
  | switch0 => exact switch0_checked
  | leave0 => exact leave0_checked
  | enter1 => exact enter1_checked
  | switch1 => exact switch1_checked
  | leave1 => exact leave1_checked

private theorem target_bound (op : Stage) : ∀ i∈program op, target i < (inputCols op).length := by
  cases op <;> decide +kernel

theorem field_run (j : Nat) (hj : j∈List.range' 1 83) (op : Stage)
    (row : Nat) (hr : row<63145) (m : List Bool) (s : State)
    (data : ∀ q∈Finset.range 121, s.basis (fieldPort j q) = (get (inputCols op) q).testBit row) :
    (run (fieldHook j op) m s).phase = s.phase ∧
    (∀ q∈Finset.range 121, (run (fieldHook j op) m s).basis (fieldPort j q)=
      (get (outputCols op) q).testBit row) ∧
    (∀ q∉(Finset.range 121).image (fieldPort j), (run (fieldHook j op) m s).basis q=s.basis q) := by
  have active : (2^63145-1 : Nat).testBit row = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hr
  exact mapped _ _ 121 row m s _ _ _ active (field_checked op)
    (target_bound op) (sub op) (field_inj j hj) data

end ECDSAAdd.Entrant.StairArchiveAllPorts

end

section

namespace ECDSAAdd.Entrant.StairArchiveIntegerHook
open Arithmetic CodecBitSliceVerify StairArchiveGates ArchiveFieldScratch StairArchiveHandoff
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 100000

inductive Operation where
  | load0 | load1 | restore0 | restore1

def program : Operation → Program
  | .load0 => integer_load0
  | .load1 => integer_load1
  | .restore0 => integer_restore0
  | .restore1 => integer_restore1

def width : Operation → Nat
  | .load0 => 155
  | .load1 => 155
  | .restore0 => 150
  | .restore1 => 150

def input : Operation → Cols
  | .load0 => integer_load0Trace0In
  | .load1 => integer_load1Trace0In
  | .restore0 => integer_restore0Trace0In
  | .restore1 => integer_restore1Trace0In

def output : Operation → Cols
  | .load0 => integer_load0Trace5Out
  | .load1 => integer_load1Trace5Out
  | .restore0 => integer_restore0Trace6Out
  | .restore1 => integer_restore1Trace6Out

theorem sub (op : Operation) : wires (program op) ⊆ Finset.range (width op) := by
  apply bounded
  cases op <;> decide +kernel

theorem word_run (op : Operation) (row : Nat) (hr : row < 63145)
    (m : List Bool) (s : State)
    (data : ∀ q ∈ wires (program op), s.basis q = (get (input op) q).testBit row) :
    (run (program op) m s).phase = s.phase ∧
    (∀ q ∈ wires (program op), (run (program op) m s).basis q = (get (output op) q).testBit row) ∧
    (∀ q ∉ wires (program op), (run (program op) m s).basis q = s.basis q) := by
  have active : (2^63145-1 : Nat).testBit row = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hr
  let x := value (input op) row
  have rel : Rel (input op) x row := value_rel _ _
  have same : ∀ q ∈ wires (program op), s.basis q = x.testBit q :=
    fun q h => (data q h).trans (rel q).symm
  cases op with
  | load0 => exact integer_load0_run row _ m s active rel same
  | load1 => exact integer_load1_run row _ m s active rel same
  | restore0 => exact integer_restore0_run row _ m s active rel same
  | restore1 => exact integer_restore1_run row _ m s active rel same

def placed (f : Wire → Wire) (op : Operation) := renameProgram f (program op)

theorem placed_run (f : Wire → Wire) (op : Operation) (row : Nat) (hr : row < 63145)
    (inj : ∀ a∈Finset.range (width op), ∀ b∈Finset.range (width op), f a=f b → a=b)
    (m : List Bool) (s : State)
    (data : ∀ q ∈ wires (program op), s.basis (f q) = (get (input op) q).testBit row) :
    (run (placed f op) m s).phase = s.phase ∧
    (∀ q ∈ wires (program op), (run (placed f op) m s).basis (f q) = (get (output op) q).testBit row) ∧
    (∀ q ∉ wires (placed f op), (run (placed f op) m s).basis q = s.basis q) := by
  have logical := word_run op row hr m (pullState f s) data
  have phys := run_rename_pool f _ inj (program op) (sub op) m (pullState f s) s rfl (fun _ _ => rfl)
  exact ⟨phys.1.trans logical.1, fun q hq => (phys.2 q (sub op hq)).trans (logical.2.1 q hq),
    fun q hq => run_preserves_outside _ _ _ q hq⟩

end ECDSAAdd.Entrant.StairArchiveIntegerHook

end

section

namespace ECDSAAdd.Entrant.StairArchiveNativeRows
open CodecBitSliceVerify StairArchiveGates
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 100000

def ones : Nat := 2^63145-1
def order (isA : Bool) : List Nat := if isA then [2,3,4,0,1] else [2,0,1,3,4]

/-- The raw 5-trit stock word, prepared in its original code order and twist convention. -/
def encodeInput (isA high : Bool) : Cols := Id.run do
  let bank := if high then 10 else 0
  let raw := (order isA).flatMap (fun j => [get integer_load0Trace0In (bank+2*j), get integer_load0Trace0In (bank+2*j+1)])
  return raw.set 9 (get raw 9 ^^^ ones ^^^ get raw 8)

def byte (s : Cols) (high : Bool) : Cols := (s.drop (if high then 8 else 0)).take 8

/-- The five-cell codec leaves 5 and 9 zero; the remaining eight bits are stored. -/
def storage (b : Cols) : Cols :=
  [get b 0, get b 1, get b 2, get b 3, get b 4, 0, get b 5, get b 6, get b 7, 0]

def native (isA high : Bool) : Cols :=
  match isA, high with
  | true, false  => byte enter0Trace3Out false
  | true, true   => byte switch0Trace2Out true
  | false, false => byte switch1Trace2Out false
  | false, true  => byte enter1Trace3Out true

/-- Actual original solver codec on all tagged chronological rows. -/
theorem ordinary_encode (isA high : Bool) :
    eval ones MeasuredCodec5.encode (encodeInput isA high) = (true, storage (native isA high)) := by
  cases isA <;> cases high <;> decide +kernel

/-- The other end of each intervening real five-cell packet has precisely its native byte. -/
theorem native_exits :
  byte switch0Trace0In false = native false false ∧
  byte leave0Trace0In true = native false true ∧
  byte switch1Trace0In true = native true true ∧
  byte leave1Trace0In false = native true false := by decide +kernel

/-- The inactive byte and the far bit survive each native body unaltered. -/
theorem side_unchanged :
  byte enter0Trace3Out true = byte switch0Trace0In true ∧
  byte switch0Trace2Out false = byte leave0Trace0In false ∧
  byte enter1Trace3Out false = byte switch1Trace0In false ∧
  byte switch1Trace2Out true = byte leave1Trace0In true ∧
  get enter0Trace3Out 16 = get switch0Trace0In 16 ∧
  get switch0Trace2Out 16 = get leave0Trace0In 16 ∧
  get enter1Trace3Out 16 = get switch1Trace0In 16 ∧
  get switch1Trace2Out 16 = get leave1Trace0In 16 := by decide +kernel

end ECDSAAdd.Entrant.StairArchiveNativeRows

end

section

namespace ECDSAAdd.Entrant.StairArchiveRaw
open CodecBitSliceVerify StairArchiveGates StairArchiveHandoff

def read (xs : List (Bool × Bool)) (i : Nat) := xs[i]?.getD (false,false)
def maskOf (xs : List (Bool × Bool)) := pack 10 (fun i => !(read xs i).1) % (2^10)

theorem mask_bit (xs : List (Bool × Bool)) (i : Nat) (hi : i<10) :
    (maskOf xs).testBit i = !(read xs i).1 := by
  simp only [maskOf, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, pack_bit _ _ _ hi]

theorem empty_prefix (v i : Nat) :
    v % 2^i = 0 ↔ ∀ k < i, v.testBit k = false := by
  constructor
  · intro h k hk
    have b := congrArg (fun x : Nat => x.testBit k) h
    simpa only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.zero_testBit] using b
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < i <;> simp [Nat.testBit_mod_two_pow,hk,h]

theorem prefix_bits (xs : List (Bool × Bool)) (i : Nat) (hi : i<10) :
    (maskOf xs % 2^i == 0) = (List.range i).all (fun k => (read xs k).1) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, empty_prefix, List.all_eq_true]
  constructor
  · intro h a ha
    have hq := List.mem_range.mp ha
    have hv := h a hq
    rw [mask_bit xs a (by omega)] at hv
    simpa using hv
  · intro h a ha
    rw [mask_bit xs a (by omega),h a (List.mem_range.mpr ha)]
    rfl

def firstOdd (xs : List (Bool × Bool)) (u : Bool) := ∀ i<10,
  (read xs i).2 = (!u && !(read xs i).1 && (List.range i).all (fun k => (read xs k).1))

theorem far_read (xs : List (Bool × Bool)) (u : Bool) (h : firstOdd xs u) (i : Nat) (hi : i<10) :
    farCells u (maskOf xs) i = read xs i := by
  apply Prod.ext
  · simp only [farCells, mask_bit xs i hi, Bool.not_not]
  · simpa only [farCells, mask_bit xs i hi, prefix_bits xs i hi] using (h i hi).symm

def legal (xs : List (Bool × Bool)) := ∀ cs∈xs, cs≠(true,true)

/-- A ten-tick recorded trace determines a valid row of the actual integer and field gate
tables. For Far only the signed first-odd law is needed. Near has no stored tags. -/
theorem list_member (xs : List (Bool × Bool)) (n : xs.length=10) (far u c : Bool)
    (near : far=false → legal xs ∧ u=false ∧ c=false)
    (farLaw : far=true → firstOdd xs u) :
    ∃ row<63145, ∀ q<23, (rawCol q).testBit row = rawBit (read xs) far u c q := by
  cases far with
  | false =>
    obtain ⟨trits, rfl, rfl⟩ := near rfl
    refine ⟨nearRow (read xs), near_member (read xs) ?_⟩
    intro i hi
    have h : i<xs.length := by omega
    simp only [read, List.getElem?_eq_getElem h, Option.getD_some]
    exact trits _ (List.getElem_mem h)
  | true =>
    let mask := maskOf xs
    have bound : mask<1024 := Nat.mod_lt _ (by decide)
    obtain ⟨lt,eqs⟩ := far_member u c mask bound
    refine ⟨farRow u c mask, lt, ?_⟩
    intro q hq
    rw [eqs q hq]
    unfold rawBit
    split
    · rw [show farCells u mask (q/2)=read xs (q/2) from far_read _ _ (farLaw rfl) _ (by omega)]
    · rfl

/-- Load-B accepts exactly the same raw bits as load-A. -/
theorem load1_raw (q row : Nat) (hq : q<23) :
    (get integer_load1Trace0In q).testBit row=(rawCol q).testBit row :=
  wires_eq _ _ 23 raw_edges.1.symm q row hq

end ECDSAAdd.Entrant.StairArchiveRaw

end

section

namespace ECDSAAdd.Entrant.StairArchiveSlots
open StairArchiveRelease ArchiveFieldScratch StairArchiveInactive
set_option maxRecDepth 14000
set_option maxHeartbeats 600000

def held (second : Bool) : List Nat := 16 :: (if second then List.range 8 else List.range' 8 8)

private theorem generic (xs : List Nat) (hx : xs.length = 16) (tag : Nat) (more : List Nat)
    (second : Bool) :
    tag :: (if second then xs.take 8 else xs.drop 8) =
      (held second).map (fun q => ((xs ++ tag :: more)[q]?).getD q) := by
  rcases xs with _ | ⟨a,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨b,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨c,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨d,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨e,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨f,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨g,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨h,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨i,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨j,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨k,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨l,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨m,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨n,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨o,xs⟩ <;> simp at hx
  rcases xs with _ | ⟨p,xs⟩ <;> simp at hx
  subst xs
  cases second <;> rfl

theorem held_eq (j : Nat) (hj : j∈List.range' 1 83) (second : Bool) :
    savedSites j second = (held second).map (fieldPort j) := by
  have h := List.all_eq_true.mp packets_exact j hj
  dsimp only [packetOK, Id.run, pure] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at h
  exact generic _ h.1.1 _ _ _

theorem held_bounded (second : Bool) {q : Nat} (hq : q∈held second) : q∈Finset.range 121 := by
  have h : (held second).all (fun i => decide (i<121)) = true := by cases second <;> decide +kernel
  exact Finset.mem_range.mpr (of_decide_eq_true (List.all_eq_true.mp h _ hq))

theorem held_at (j : Nat) (hj : j∈List.range' 1 83) (second : Bool)
    (q : Nat) (hq : q∈Finset.range 121) :
    fieldPort j q ∈ savedSites j second ↔ q∈held second := by
  rw [held_eq j hj second, List.mem_map]
  constructor
  · rintro ⟨p,hp,heq⟩
    exact field_inj j hj p (held_bounded second hp) q hq heq ▸ hp
  · exact fun h => ⟨q,h,rfl⟩

end ECDSAAdd.Entrant.StairArchiveSlots

end

section

namespace ECDSAAdd.Entrant.Stair44PhaseSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairRestSupport StairConcreteAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

abbrev holes := StairPhysicalInventory.physicalHoles
abbrev valid (q : Nat) := Stair44OuterSites.fit (StairPlaceFast.phasePlaceB q)

private theorem ppiList {q : Nat} (h : PPI q) : q ∈ ppList := by
  unfold PPI at h
  simp only [ppList,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  omega

private def rawReady (q : Wire) : Bool := decide (q ∈ Stair44WalkSites.retired) || valid q
private theorem firstTable : ppList.all (fun x => rawReady (Stair44WalkMap.first x)) = true := by decide +kernel
private theorem restTable : ppList.all (fun x => rawReady (Stair44WalkMap.rest x)) = true := by decide +kernel

private theorem rebased {P : Program} (c : Equiv.Perm Wire)
    (table : ppList.all (fun x => rawReady (c x)) = true) (seen : ∀ q ∈ wires P, PPI q) :
    ∀ q ∈ wires (renameProgram c P), rawReady q = true := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact List.all_eq_true.mp table x (ppiList (seen x hx))

private theorem walk {P : Program} (ready : ∀ q ∈ wires P, rawReady q = true)
    (free : ∀ q ∈ Stair44WalkSites.retired, q ∉ wires P) : PieceOK holes PP P := by
  apply Stair44OuterSites.fits
  intro q hq
  have t := ready q hq
  simp only [rawReady,Bool.or_eq_true,decide_eq_true_eq] at t
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace q) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact t.resolve_left (fun bad => free q bad hq)

attribute [local irreducible] wires Rolling1588TickGap.forward Rolling1588.reverse renameProgram

theorem forward (d : Bool) (n : Nat) (bound : 16+n ≤ 506) : PieceOK holes PP (Stair44WalkRun.forward d n) := by
  have orig := tickGap_forward_ppi d (15+n) (by omega)
  rw [forward_append d 15 1 n,wires_append] at orig
  apply walk (P := Stair44WalkRun.forward d n) (free := fun q hq => (Stair44WalkSites.routed_free d n bound q hq).1)
  intro q hq
  rw [Stair44WalkRun.forward,wires_append,Finset.mem_union] at hq
  exact hq.elim (rebased (P := Rolling1588TickGap.forward d 1 15) _ firstTable (fun x hx => orig x (Finset.mem_union_left _ hx)) q)
    (rebased (P := Rolling1588TickGap.forward d 16 n) _ restTable (fun x hx => orig x (Finset.mem_union_right _ hx)) q)
  
theorem backward (d : Bool) (n : Nat) (bound : 16+n ≤ 506) : PieceOK holes PP (Stair44WalkRun.backward d n) := by
  have orig := reverse_ppi d (15+n) (by omega)
  rw [reverse_append d 15 1 n,wires_append] at orig
  apply walk (P := Stair44WalkRun.backward d n) (free := fun q hq => (Stair44WalkSites.routed_free d n bound q hq).2)
  intro q hq
  rw [Stair44WalkRun.backward,wires_append,Finset.mem_union] at hq
  exact hq.elim (rebased (P := Rolling1588.reverse d 16 n) _ restTable (fun x hx => orig x (Finset.mem_union_left _ hx)) q)
    (rebased (P := Rolling1588.reverse d 1 15) _ firstTable (fun x hx => orig x (Finset.mem_union_right _ hx)) q)

set_option exponentiation.threshold 1024 in
private theorem nativeFits (x : Wire) (hx : x ∈ wires (FrontierEntry1591NativeH.inverse base)) :
    valid (Stair44WalkMap.first x) = true := by
  have h := (FrontierEntry1591Native.support base base_pool_nodup).2
    (FrontierEntry1591NativeH.wires_sub base base_pool_nodup hx)
  have m : x ≠ base 1797 ∧ x ∈ insert (base 511) (NativeFirstDirect.prefixSites base).toFinset :=
    Finset.mem_erase.mp h
  rcases Finset.mem_insert.mp m.2 with eq | inside
  · rw [eq]; decide +kernel
  · have table : (NativeFirstDirect.prefixSites base).all
        (fun z => decide (z = base 1797) || valid (Stair44WalkMap.first z)) = true := by decide +kernel
    have t := List.all_eq_true.mp table x (List.mem_toFinset.mp inside)
    simp only [Bool.or_eq_true,decide_eq_true_eq] at t
    exact t.resolve_left m.1

theorem native : PieceOK holes PP (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)) := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace _) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact nativeFits _ hx

end ECDSAAdd.Entrant.Stair44PhaseSites

end

section

/-! Five-wire square-tail routing on the public e9dca31f staircase.
The comparator and its successor use different scratch lifetimes. -/
section
namespace ECDSAAdd.Entrant.E1Reflected.Square31
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
def afterCompare (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  (parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++E1WholeKAdd52Research.flagKAdd52 w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]


theorem split (w : Nat → Wire) (g : Wire) (k : Nat) :
    merged w g k = comparePart w g k ++ afterCompare w g k := by
  simp only [merged, afterCompare, List.append_assoc]
def mS5 (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 258 ++ [w 513, w 514] ++ wireBlock w 770 515 ++ wireBlock w 1540 258 ++
    [w 721, w 722, g]

theorem in_m5 (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : (i < 258 ∨ i = 513 ∨ i = 514) ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨
      i = 721 ∨ i = 722) : w i ∈ mS5 w g := by
  have hA : ∀ a n : Nat, a ≤ i → i < a + n → w i ∈ wireBlock w a n := fun a n h1 h2 =>
    List.mem_map.mpr ⟨i, by simp only [List.mem_range'_1]; omega, rfl⟩
  simp only [mS5, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hi with (h|h|h)|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (hA 0 258 (by omega) (by omega)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (congrArg w h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (congrArg w h)))))
  · exact Or.inl (Or.inl (Or.inr (hA 770 515 (by omega) (by omega))))
  · exact Or.inl (Or.inr (hA 1540 258 (by omega) (by omega)))
  · exact Or.inr (Or.inl (congrArg w h))
  · exact Or.inr (Or.inr (Or.inl (congrArg w h)))

theorem blk_m5 (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 258 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀ q ∈ wireBlock w a n, q ∈ mS5 w g := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_m5 w g i (by omega)

theorem g_m5 (w : Nat → Wire) (g : Wire) : g ∈ mS5 w g :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem lsub5 (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀ q ∈ l, q ∈ mS5 w g) :
    l.toFinset ⊆ (mS5 w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub5 (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀ q ∈ i.wires, q ∈ mS5 w g) :
    wires [i] ⊆ (mS5 w g).toFinset := by
  intro q hq
  simp only [wires, Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem afterCompare_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (afterCompare w g k) ⊆ (mS5 w g).toFinset := by
  have B := blk_m5 w g
  have I := in_m5 w g
  have G := g_m5 w g
  have mskH (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have cx (a b : Nat) (ha : (a < 258 ∨ a = 513 ∨ a = 514) ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : (b < 258 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : (b < 258 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mS5 w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mS5 w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hNot : wires (notRegister (kR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mS5 w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub5 <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mS5 w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub5 w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mS5 w g).toFinset := by
    have sub := E1ResourceBridge52Research.flag_support52 w
    rw [← kAdd_literal w] at sub
    apply sub.trans
    refine Finset.union_subset hKOld ?_
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr (I 1028 (by omega)))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mS5 w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub5; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mS5 w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub5 w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mS5 w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mS5 w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mS5 w g).toFinset := (hAddT_wires w).trans hH
  simp only [afterCompare,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩
end ECDSAAdd.Entrant.E1Reflected.Square31
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 4000000
def placed (p : Program) := renameProgram (pmapR Baselines.layout) p
def comparePhase (k : Fp) := placed (E1Reflected.comparePart base (base 2400) k.val)
def suffix (k : Fp) := placed (E1Reflected.Square31.afterCompare base (base 2400) k.val)
def moves : List (Wire × Wire) := (List.range 5).map fun i => (4835+i, pmapR Baselines.layout (base (258+i)))
def candidate (k : Fp) := hostRename StairSquareEntryR.entryPairs (comparePhase k) ++ hostRename moves (suffix k)
theorem stock_split (k : Fp) : entryR Baselines.layout k = comparePhase k ++ suffix k := by
  unfold entryR comparePhase suffix placed
  rw [E1Reflected.Square31.split]
  simp only [renameProgram, List.map_append]
attribute [local irreducible] wires E1Reflected.Square31.afterCompare E1Reflected.comparePart E1Reflected.merged pmapR Baselines.layout
theorem hosts_clear (k : Fp) : ∀ t ∈ moves, t.2 ∉ wires (suffix k) := by
  intro t ht used
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hi' := List.mem_range.mp hi
  unfold suffix placed at used
  rw [renameProgram_support] at used
  obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp used
  have orig : y ∈ wires (E1Reflected.merged base (base 2400) k.val) := by
    rw [E1Reflected.Square31.split, wires_append]
    apply Finset.mem_union_right
    exact hy
  have hh : base (258+i) ∈ S := List.mem_toFinset.mpr
    (E1Merge.in_mSites base (base 2400) (258+i) (by omega))
  have same := pmap_inj Baselines.layout Baselines.layout_widths Baselines.layout_nodup
    y (mergedR_S k.val orig) _ hh eq
  have mem := List.mem_toFinset.mp (E1Reflected.Square31.afterCompare_support _ _ _ hy)
  rw [same] at mem
  simp only [E1Reflected.Square31.mS5,wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_map,List.mem_range'_1] at mem
  rcases mem with (((h|h|h)|h)|h)|h|h|h
  all_goals first
    | obtain ⟨j,hj,ej⟩ := h; have := base_injective ej; omega
    | have := base_injective h; omega
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairSquareHolesCore
open ECDSAAdd Arithmetic
def permutation : List (Wire × Wire) → Equiv.Perm Wire
  | [] => Equiv.refl _
  | (a,b)::ps => (permutation ps).trans (Equiv.swap a b)
theorem fused (ps : List (Wire × Wire)) (p : Program) :
    hostRename ps p = renameProgram (permutation ps) p := by
  induction ps with
  | nil =>
    change p = renameProgram id p
    have ec (c : Correction) : renameCorrection id c = c := by cases c <;> rfl
    have ei (i : Instr) : renameInstr id i = i := by
      cases i <;> simp [renameInstr,funext ec]
    simp [renameProgram,funext ei]
  | cons ab ps ih =>
    rw [hostRename, ih, renameProgram_comp]
    rfl
theorem decode (ps : List (Wire × Wire)) (p : Program) (m : List Bool) (s : State) :
    pullState (permutation ps) (run (hostRename ps p) m s) =
        run p m (pullState (permutation ps) s) := by
  rw [fused]
  exact run_rename _ (permutation ps).injective _ _ _
end ECDSAAdd.Entrant.StairSquareHolesCore
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open Arithmetic Secp256k1 E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem counts (k : Fp) : toffoliCount (candidate k) = toffoliCount (entryR Baselines.layout k) ∧
    measurementCount (candidate k) = measurementCount (entryR Baselines.layout k) ∧
    Challenge.gateSlots (candidate k) = Challenge.gateSlots (entryR Baselines.layout k) := by
  rw [stock_split]
  simp only [candidate,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (hostRename_counts _ _).1,(hostRename_counts _ _).2,hostRename_slots,and_self]
theorem transport (k : Fp) (m : List Bool) (s : State)
    (compareRun : ∀ t, run (hostRename StairSquareEntryR.entryPairs (comparePhase k)) t s =
                         run (comparePhase k) t s)
    (clean : ∀ t, pullState (permutation moves) (run (comparePhase k) t s) =
                  run (comparePhase k) t s) :
    pullState (permutation moves) (run (candidate k) m s) = run (entryR Baselines.layout k) m s := by
  rw [stock_split]
  simp only [candidate,run_append,(hostRename_counts _ _).2,compareRun,decode,clean]
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore
set_option maxHeartbeats 1600000
attribute [local irreducible] wires run E1Reflected.merged E1Reflected.comparePart
  E1Reflected.Square31.afterCompare pmapR Baselines.layout
abbrev cleanIndex (i : Nat) : Prop := i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨
  (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722
theorem atPool (i : Nat) (hi : cleanIndex i) : pmapR Baselines.layout (base i) ∈ Baselines.layout.dialogPool := by
  apply pmap_pool _ Baselines.layout_widths Baselines.layout_nodup
  · exact List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by unfold cleanIndex at hi; omega))
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold cleanIndex at hi
    omega
  · intro e
    have := base_injective e
    unfold cleanIndex at hi
    omega
theorem compareZero (k : Fp) (s : State) (m : List Bool)
    (hc : regValue Baselines.layout.dialogPool s.basis = 0)
    (i : Nat) (hi : cleanIndex i) (lo : 256 ≤ i) (nf : i ≠ 514) :
    (run (comparePhase k) m s).basis (pmapR Baselines.layout (base i)) = false := by
  let f := pmapR Baselines.layout
  let t := pullState f s
  have clean (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (atPool j hj)
  have bk (a n : Nat) (h : a+n ≤ 514) : ∀ q ∈ wireBlock base a n, t.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact clean j (Or.inl (by omega))
  have ns (j : Nat) (hj : 256 ≤ j) : base j ∉ E1Reflected.srcR base := by
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hv
    have := base_injective e
    omega
  have diff (u v : Nat) (ne : u ≠ v) : base u ≠ base v := fun e => ne (base_injective e)
  have cf := E1Reflected.cfCompare base (base 2400) base_pool_nodup t.basis (t.basis (base 514))
    k.val _ (by have := k.val_lt; change k.val < p at this; have := E1Reflected.p_val; omega)
    rfl (bk 256 256 (by decide)) (clean 513 (Or.inl (by decide)))
    (ns 2400 (by decide)) (diff _ _ (by decide)) t m
    ⟨(regValue_zero _ _).mpr (bk 0 256 (by decide)), rfl, fun _ _ _ => rfl⟩
  have sup : wires (E1Reflected.comparePart base (base 2400) k.val) ⊆ S := by
    intro q hq
    apply mergedR_S k.val
    rw [E1Reflected.Square31.split,wires_append]
    exact Finset.mem_union_left _ hq
  have hS : base i ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at hi; omega))
  have mapped := run_rename_pool f S (pmap_inj _ Baselines.layout_widths Baselines.layout_nodup)
    _ sup m t s rfl (fun _ _ => rfl)
  exact ((mapped.2 _ hS).trans (cf.2.2.2 _ (ns i lo) (diff _ _ nf))).trans (clean i hi)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum
set_option linter.unusedSimpArgs false
theorem compare_support (w : Nat → Wire) (g : Wire) (k : Nat) : wires (comparePart w g k) ⊆ (mS5 w g).toFinset := by
  have B := blk_m5 w g
  have I := in_m5 w g
  have G := g_m5 w g
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]; exact lsub5 w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mS5 w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub5; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mS5 w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
  exact hC
end ECDSAAdd.Entrant.E1Reflected
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore StairSquareEntryR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem placement : [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),(258,4373),
    (259,4374),(260,4375),(261,4376),(262,4377),(514,4629)].all
      (fun (i,q) => pmapR Baselines.layout (base i) == q) = true := by decide +kernel
attribute [local irreducible] wires run E1Reflected.merged E1Reflected.comparePart
  E1Reflected.Square31.afterCompare pmapR Baselines.layout
theorem compareFree (k : Fp) : host512 ∉ wires (comparePhase k) := by
  intro hu
  unfold comparePhase placed at hu
  rw [renameProgram_support] at hu
  obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp hu
  have inS : y ∈ S := by
    apply mergedR_S k.val
    rw [E1Reflected.Square31.split,wires_append]
    exact Finset.mem_union_left _ hy
  have ib : base 512 ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites _ _ _ (Or.inl (by decide)))
  have same := pmap_inj L0 Baselines.layout_widths Baselines.layout_nodup _ inS _ ib (eq.trans StairSquareEntryR.pmapR_512.symm)
  have mem := List.mem_toFinset.mp (E1Reflected.compare_support base (base 2400) k.val hy)
  exact E1Reflected.base512_not_m5 (same ▸ mem)
theorem compareExact (k : Fp) (s : State) (hc : regValue L0.dialogPool s.basis=0) (m : List Bool) :
    run (hostRename entryPairs (comparePhase k)) m s = run (comparePhase k) m s := by
  apply hostRename_run_eq
  all_goals intro ab hab; simp only [entryPairs,List.mem_singleton] at hab; subst ab
  · rw [← StairSquareEntryR.pmapR_511]
    exact (regValue_zero _ _).mp hc _ (atPool 511 (Or.inl (by decide)))
  · rw [← StairSquareEntryR.pmapR_512]
    exact (regValue_zero _ _).mp hc _ (atPool 512 (Or.inl (by decide)))
  · rw [← StairSquareEntryR.pmapR_511]
    exact compareZero k s m hc 511 (Or.inl (by decide)) (by decide) (by decide)
  · exact compareFree k
theorem samePerm (ps : List (Wire × Wire)) (s : State)
    (eq : ∀ a ∈ ps, s.basis a.1 = s.basis a.2) : pullState (permutation ps) s = s := by
  have h (q : Wire) : s.basis (permutation ps q) = s.basis q := by
    induction ps generalizing q with
    | nil => rfl
    | cons a ps ih =>
      have eq1 := eq a List.mem_cons_self
      have eq2 := ih (fun x hx => eq x (List.mem_cons_of_mem _ hx)) q
      let v := permutation ps q
      change s.basis (Equiv.swap a.1 a.2 v) = s.basis q
      by_cases h1 : v=a.1
      · rw [h1,Equiv.swap_apply_left,←eq1,←h1]; exact eq2
      by_cases h2 : v=a.2
      · rw [h2,Equiv.swap_apply_right,eq1,←h2]; exact eq2
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact eq2
  exact State.extensionality _ _ rfl (funext h)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] wires run pmapR Baselines.layout
theorem afterCompareClean (k : Fp) (s : State) (hc : regValue Baselines.layout.dialogPool s.basis=0)
    (m : List Bool) : pullState (permutation moves) (run (comparePhase k) m s) = run (comparePhase k) m s := by
  apply samePerm
  intro pair hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have h := List.mem_range.mp hi
  change (run (comparePhase k) m s).basis (4835+i) =
         (run (comparePhase k) m s).basis (pmapR Baselines.layout (base (258+i)))
  rw [compareZero k s m hc (258+i) (Or.inl (by omega)) (by omega) (by omega)]
  let raw := [1542,1026,1541,721,722]
  have elem : (raw[i]!,4835+i) ∈ [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),
      (258,4373),(259,4374),(260,4375),(261,4376),(262,4377),(514,4629)] := by
    interval_cases i <;> decide
  have bound : cleanIndex (raw[i]!) ∧ 256≤raw[i]! ∧ raw[i]!≠514 := by interval_cases i <;> decide
  have pm : pmapR Baselines.layout (base (raw[i]!)) = 4835+i :=
    eq_of_beq (List.all_eq_true.mp placement _ elem)
  rw [← pm]
  exact compareZero k s m hc _ bound.1 bound.2.1 bound.2.2
theorem decoded (k : Fp) (s : State) (hc : regValue Baselines.layout.dialogPool s.basis=0) (m : List Bool) :
    pullState (permutation moves) (run (candidate k) m s) = run (entryR Baselines.layout k) m s :=
  transport k m s (compareExact k s hc) (afterCompareClean k s hc)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run E1Reflected.merged pmapR Baselines.layout
def exitClean := [1542,1541,721,722,258,259,260,261,262,514,500,501]
theorem stockExit (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) (i : Nat) (hi : i∈exitClean) :
    (run (entryR Baselines.layout k) m s).basis (pmapR Baselines.layout (base i)) = false := by
  let f := pmapR Baselines.layout
  let t := pullState f s
  have cl (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (atPool j hj)
  have blk (a n : Nat) (h : a+n ≤ 515 ∨ (1026 ≤ a ∧ a+n ≤ 1285) ∨ (1540 ≤ a ∧ a+n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact cl j (by unfold cleanIndex; omega)
  have xv : regValue (E1Reflected.xR base) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (f q))=X
    rw [regValue_pull,pmap_x Baselines.layout Baselines.layout_widths Baselines.layout_nodup,hx]
  have kv : regValue (E1Reflected.kR base) t.basis=X := by
    rw [E1Reflected.kR_x base base_pool_nodup,xv,blk 1026 2 (by decide)]; simp
  have c (i : Nat) (h : cleanIndex i) := cl i h
  have tri := E1Reflected.merged_triple base (base 2400) base_pool_nodup g2400 k.val k.isLt t.basis X hX
    (fun j a b => cl j (Or.inl (by omega))) (cl 513 (Or.inl (by decide)))
    ((regValue_zero _ _).mp (blk 1540 257 (by decide))) (cl 1797 (by decide)) t m
    ⟨blk 0 258 (by decide),kv,blk 1029 256 (by decide),cl 1028 (by decide),cl 514 (by decide),
      cl 721 (by decide),cl 722 (by decide),fun _ _ => rfl⟩
  have range : cleanIndex i := by simp [exitClean] at hi; unfold cleanIndex; omega
  have isS : base i ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at range; omega))
  have mapped := run_rename_pool f S (pmap_inj _ Baselines.layout_widths Baselines.layout_nodup) _
    (mergedR_S k.val) m t s rfl (fun _ _ => rfl)
  rw [entryR,mapped.2 _ isS]
  obtain ⟨_,_,_,_,hf,hg,hp,frame⟩ := tri.2
  by_cases eq1 : i=721
  · subst i; exact hg
  by_cases eq2 : i=722
  · subst i; exact hp
  by_cases eq3 : i=514
  · subst i; exact hf
  apply (frame (base i) ?_).trans (cl i range)
  simp [exitClean] at hi
  simp only [E1Reflected.mutL,E1Reflected.hR,E1Reflected.kR,E1Reflected.tR,wireBlock,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_range'_1,not_or]
  repeat' apply And.intro
  all_goals first
    | intro ⟨j,hj,ej⟩; have := base_injective ej; omega
    | intro ej; have := base_injective ej; omega
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def physicalMoves : List (Wire × Wire) := [(4835,4373),(4836,4374),(4837,4375),(4838,4376),(4839,4377)]
theorem moves_eq : moves = physicalMoves := by decide +kernel
def routed (k : Fp) := candidate k ++ swapBits 4374 4629
def landing : Equiv.Perm Wire := Equiv.swap 4836 4629
def touchedSites : List Wire := [4835,4373,4836,4374,4837,4375,4838,4376,4839,4377,4629]
def zeroSites : List Wire := [4835,4373,4374,4837,4375,4838,4376,4839,4377,4629]
def beforeTransfer (q : Wire) := (permutation physicalMoves).symm (Equiv.swap 4374 4629 q)
theorem finiteCheck : touchedSites.all (fun q =>
    beforeTransfer q == landing q || (zeroSites.contains (beforeTransfer q) && zeroSites.contains (landing q))) := by decide +kernel
theorem offSites (q : Wire) (hq : q ∉ touchedSites) : beforeTransfer q = landing q := by
  simp [touchedSites] at hq
  simp [beforeTransfer, physicalMoves, permutation, landing, Equiv.swap_apply_def, *]
theorem realSwap (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    run (swapBits a b) m s = pullState (Equiv.swap a b) s := by
  apply congrArg₂ State.mk
  · rfl
  · funext i
    by_cases h : i=a
    · subst i; cases h1:s.basis a <;> cases h2:s.basis b <;>
        simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,hab,Ne.symm hab,h1,h2]
    by_cases k : i=b
    · subst i; cases h1:s.basis a <;> cases h2:s.basis b <;>
        simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,hab,Ne.symm hab,h1,h2]
    · simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,h,k]
attribute [local irreducible] wires run E1Reflected.merged pmapR Baselines.layout
theorem stockZeros (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    ∀ q ∈ zeroSites, (run (entryR Baselines.layout k) m s).basis q = false := by
  intro q hq
  have e : ∃ i ∈ exitClean, (i,q) ∈ [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),
      (258,4373),(259,4374),(260,4375),(261,4376),(262,4377),(514,4629)] := by
    simp only [zeroSites,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨1542,by decide,by decide⟩
    · exact ⟨258,by decide,by decide⟩
    · exact ⟨259,by decide,by decide⟩
    · exact ⟨1541,by decide,by decide⟩
    · exact ⟨260,by decide,by decide⟩
    · exact ⟨721,by decide,by decide⟩
    · exact ⟨261,by decide,by decide⟩
    · exact ⟨722,by decide,by decide⟩
    · exact ⟨262,by decide,by decide⟩
    · exact ⟨514,by decide,by decide⟩
  obtain ⟨i,hi,eq⟩ := e
  have p : pmapR Baselines.layout (base i) = q := eq_of_beq (List.all_eq_true.mp placement _ eq)
  rw [← p]
  exact stockExit k s m X hx hX hc i hi
theorem fullRun (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    run (routed k) m s = pullState landing (run (entryR Baselines.layout k) m s) := by
  rw [routed,run_append,realSwap _ _ (by decide),run_take]
  have d := decoded k s hc m
  rw [moves_eq] at d
  apply State.extensionality
  · have eq := congrArg State.phase d
    exact eq
  · funext q
    let v := beforeTransfer q
    have val := congrArg (fun t : State => t.basis v) d
    change (run (candidate k) m s).basis (permutation physicalMoves v) =
        (run (entryR Baselines.layout k) m s).basis v at val
    simp only [v,beforeTransfer,Equiv.apply_symm_apply] at val
    change (run (candidate k) m s).basis (Equiv.swap 4374 4629 q) =
      (run (entryR Baselines.layout k) m s).basis (landing q)
    rw [val]
    change (run (entryR Baselines.layout k) m s).basis (beforeTransfer q) = _
    by_cases hq : q ∈ touchedSites
    · have h := List.all_eq_true.mp finiteCheck q hq
      simp only [Bool.or_eq_true,beq_iff_eq,Bool.and_eq_true,List.contains_iff_mem] at h
      rcases h with eq|⟨ha,hb⟩
      · rw [eq]
      · rw [stockZeros k s m X hx hX hc _ ha,stockZeros k s m X hx hX hc _ hb]
    · rw [offSites q hq]
theorem walkPortZeros (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    ∀ q ∈ ([4835,4837,4615,4616] : List Wire), (run (entryR Baselines.layout k) m s).basis q = false := by
  have geo : [(1542,4835),(1541,4837),(500,4615),(501,4616)].all
      (fun (i,q) => pmapR Baselines.layout (base i) == q) = true := by decide +kernel
  intro q hq
  have e : ∃ i ∈ exitClean, (i,q) ∈ [(1542,4835),(1541,4837),(500,4615),(501,4616)] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact ⟨1542,by decide,by decide⟩
    · exact ⟨1541,by decide,by decide⟩
    · exact ⟨500,by decide,by decide⟩
    · exact ⟨501,by decide,by decide⟩
  obtain ⟨i,hi,hm⟩ := e
  have pm : pmapR Baselines.layout (base i)=q := eq_of_beq (List.all_eq_true.mp geo _ hm)
  rw [←pm]
  exact stockExit k s m X hx hX hc i hi
end ECDSAAdd.Entrant.StairEntryRehost
end

end

section

namespace ECDSAAdd.Entrant.StairArchiveNativeCut
open Arithmetic CodecBitSliceVerify StairArchiveRelease StairArchiveSlots StairArchiveNativeRows
open StairArchiveInactive

def enter (rev : Bool) : Stage := if rev then .enter1 else .enter0
def shift (rev : Bool) : Stage := if rev then .switch1 else .switch0
def leave (rev : Bool) : Stage := if rev then .leave1 else .leave0
def fromStage (rev last : Bool) := if last then shift rev else enter rev
def toStage (rev last : Bool) := if last then leave rev else shift rev

def canonical (ls rs : Bool) : Cols := native ls false ++ native rs true
def middle := canonical false true
def before (rev last : Bool) := if last then middle else canonical (!rev) (!rev)
def after (rev last : Bool) := if last then canonical rev rev else middle

def agrees (second on : Bool) (a b : Cols) := (List.range 121).all
  (fun q => !(decide (q∈held second) == on) || get a q == get b q)

def checks (rev last : Bool) :=
  let active := rev ^^ last
  let fromC := outputCols (fromStage rev last)
  let toC := inputCols (toStage rev last)
  agrees active false fromC (before rev last) &&
    agrees active false toC (after rev last) && agrees active true fromC toC

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem all_checks (rev last : Bool) : checks rev last = true := by
  cases rev <;> cases last <;> decide +kernel

theorem column (active on : Bool) (a b : Cols) (ok : agrees active on a b = true)
    (q : Nat) (hq : q∈Finset.range 121) (incl : decide (q∈held active)=on) :
    get a q = get b q := by
  have h := List.all_eq_true.mp ok q (List.mem_range.mpr (Finset.mem_range.mp hq))
  simpa only [incl, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] using h

def inside (j : Nat) := (Finset.range 121).image (fieldPort j)

def frame (j row : Nat) (cs : Cols) (s : State) := ∀ q∈Finset.range 121,
  s.basis (fieldPort j q) = (get cs q).testBit row
def exterior (j : Nat) (a b : State) := ∀ q∉inside j, a.basis q = b.basis q

attribute [local irreducible] run packet fieldHook fieldPort inputCols outputCols CodecBitSliceVerify.get savedSites

private theorem xor_cancel (a b c : Bool) (h : (a ^^ c)=(b ^^ c)) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- One administration followed by the real incumbent five-cell arithmetic packet.
    Frames of the ordinary computation are the only arithmetic assumptions. -/
theorem stage_packet (j : Nat) (hstart : j∈starts) (hj : j∈List.range' 1 83)
    (rev last : Bool) (row : Nat) (hr : row<63145) (m n : List Bool) (a ref : State)
    (change : frame j row (inputCols (fromStage rev last)) a)
    (out : exterior j a ref) (phase : a.phase=ref.phase)
    (entryFrame : frame j row (before rev last) ref)
    (endFrame : frame j row (after rev last)
      (run (packet (!rev) (if rev ^^ last then j+1 else j)) n ref)) :
    let c := run (fieldHook j (fromStage rev last)) m a
    let p := packet (!rev) (if rev ^^ last then j+1 else j)
    let s := run p n c
    let t := run p n ref
    s.phase=t.phase ∧ exterior j s t ∧ frame j row (inputCols (toStage rev last)) s := by
  let active := rev ^^ last
  let fromC := outputCols (fromStage rev last)
  let toC := inputCols (toStage rev last)
  let c := run (fieldHook j (fromStage rev last)) m a
  let p := packet (!rev) (if active then j+1 else j)
  have admin := StairArchiveAllPorts.field_run j hj _ row hr m a change
  have hchecks := all_checks rev last
  change (agrees active false fromC (before rev last) &&
    agrees active false toC (after rev last) && agrees active true fromC toC)=true at hchecks
  simp only [Bool.and_eq_true] at hchecks
  have same : ∀ z∉savedSites j active, c.basis z=ref.basis z := by
    intro z hz
    by_cases hz' : z∈inside j
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz'
      have hh : q∉held active := fun h => hz ((held_at j hj active q hq).mpr h)
      exact (admin.2.1 q hq).trans ((congrArg (fun v : Nat => v.testBit row)
        (column _ _ _ _ hchecks.1.1 q hq (decide_eq_false hh))).trans (entryFrame q hq).symm)
    · exact (admin.2.2 z hz').trans (out z hz')
  have body :
      ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) ∧
      (∀ z ∉ savedSites j active, (run p n c).basis z = (run p n ref).basis z) ∧
      (∀ z ∈ savedSites j active, (run p n c).basis z = c.basis z) :=
    advance j hstart (!rev) active n ref c same
  have cphase : c.phase=ref.phase := admin.1.trans phase
  change (run p n c).phase = (run p n ref).phase ∧ exterior j (run p n c) (run p n ref) ∧ frame j row toC (run p n c)
  refine ⟨?_, ?_, ?_⟩
  · have v := body.1
    change ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) at v
    rw [cphase] at v
    exact xor_cancel _ _ _ v
  · intro z hz
    apply body.2.1 z
    intro h
    rw [held_eq j hj active] at h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact hz (Finset.mem_image.mpr ⟨q,held_bounded _ hq,rfl⟩)
  · intro q hq
    by_cases hold : q∈held active
    · exact (body.2.2 _ ((held_at j hj active q hq).mpr hold)).trans
        ((admin.2.1 q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.2 q hq (decide_eq_true hold))))
    · exact (body.2.1 _ (fun z => hold ((held_at j hj active q hq).mp z))).trans
        ((endFrame q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.1.2 q hq (decide_eq_false hold))).symm)

end ECDSAAdd.Entrant.StairArchiveNativeCut

end

section

namespace ECDSAAdd.Entrant.StairSquareKernel26C
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareHolesCore StairSquareKernel26 StairSquareContract
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run wires
theorem domain_cases (q : Wire) (hq : q ∈ StairSqLoopA.hostDomain) :
    q ∈ holes K0 ∨ ∃ k, 99 ≤ k ∧ k < 123 ∧ k ≠ 108 ∧ q=(LowZero18LowK.ktmp K0).getD k 0 := by
  rcases List.mem_append.mp hq with old|fresh
  · exact holes39_cases q old
  · obtain ⟨n,hi,rfl⟩ := List.mem_map.mp fresh
    simp only [List.mem_range'_1] at hi
    exact Or.inl (holes_pool_of L0 hw0 n (by omega) (by omega))

theorem kA_run_eq44 (hs : List Wire) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrA hs body) m t=run (recBrA body) m t := by
  have p := B3CarryPort.pool1540_facts L0 hw0 hn0
  rw [newBrA_eq,recBrA_eq]
  exact branchA_run_eq K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs)
    (regValue K0.core.low t.basis) (regValue K0.core.out t.basis) pre.outLt t m
    rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0 D0 p.1 p.2.1 pre.d0 body hb.support hb.eUfree hb.frame
    (fun ab h => hav _ (psOf_mem hs ab h))

theorem kB_run_eq_of_frame44 (hs : List Wire) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t)
    (frame : ∀ q, q∉K0.core.out → (run (recBrB body) m t).basis q=t.basis q) :
    run (newBrB hs body) m t=run (recBrB body) m t := by
  rw [newBrB_eq,recBrB_eq]
  rw [recBrB_eq] at frame
  exact branchB_run_eq_of_frame K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
    (fun ab h => hav _ (psOf_mem hs ab h)) t m pre.clean pre.prod0 pre.ext0 frame

theorem kB_run_eq44 (hs : List Wire) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrB hs body) m t=run (recBrB body) m t :=
  kB_run_eq_of_frame44 hs body hb hav t m pre (recBrB_correct body hb t m pre).2.2

theorem kC_run_eq44 (hs : List Wire) (body : Program) (hb : BodyCOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrC hs body) m t=run (recBrC body) m t := by
  have p := B3CarryPort.pool1540_facts L0 hw0 hn0
  have bound := low_sum_bound K0 hwK t pre.sum0
  rw [newBrC_eq,recBrC_eq]
  exact branchC_run_eq K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs)
    (regValue K0.core.low t.basis) (regValue K0.core.sum t.basis) (regValue K0.core.out t.basis) pre.outLt t m
    rfl rfl bound rfl pre.prod0 pre.clean pre.ext0 D0 p.1 p.2.1 pre.d0 body hb.support hb.frame
    (fun ab h => hav _ (psOf_mem hs ab h))

theorem kA_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrA hs body) := by
  rw [newBrA_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchA_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchA_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

theorem kB_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrB hs body) := by
  rw [newBrB_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchB_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchB_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

theorem kC_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyCOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrC hs body) := by
  rw [newBrC_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchC_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchC_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

end ECDSAAdd.Entrant.StairSquareKernel26C

end

section

namespace ECDSAAdd.Entrant.Stair44OuterSites
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy Stair44PointMap
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

attribute [local irreducible] wires renameProgram GatePhysical

private theorem stages : ∀q∈stageList,fit (U (outer q)) = true := by
  intro q hq
  rw [U_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    stageList.all (fun r => fit (StairPlaceFast.uB (outer r)))=true) q hq

private theorem outputs : ∀q∈outList,fit (U (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) q)))=true := by
  intro q hq
  rw [U_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    outList.all (fun r => fit (StairPlaceFast.uB (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) r))))=true) q hq

private theorem ys : ∀q∈yList,fit (UG (duringY q))=true := by
  intro q hq
  rw [UG_fast]
  exact List.all_eq_true.mp ysFit q hq

section
variable {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)

theorem initial : PieceOK StairPhysicalInventory.physicalHoles U
    (encode (FlagTop.stageNew layout (.some hc) (FlagEntry.pkW layout) ++
      AboveFieldPointDevelop.encode (.some hc) ++ AboveFieldPointDevelop.eraseB)) := by
  apply lifted
  intro q hq
  rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have mem := ControlStageSupportDevelop.stage_support hc h
    rw [stagePorts_eq] at mem
    exact stages q (List.mem_toFinset.mp mem)
  · exact stages q (aux_stageList ((AboveFieldTagDevelop.encoding_support hc).1 h))
  · exact stages q (aux_stageList (AboveFieldPointDevelop.marker_support.1 h))

theorem finalPart : PieceOK StairPhysicalInventory.physicalHoles U
    (encode (AboveFieldPointDevelop.loadB ++ AboveFieldPointDevelop.decode (.some hc) ++
      ControlPointEncodingDevelop.borrowOut (.some hc))) := by
  apply lifted
  intro q hq
  rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · exact stages q (aux_stageList (AboveFieldPointDevelop.marker_support.2 h))
  · exact stages q (aux_stageList ((AboveFieldTagDevelop.encoding_support hc).2 h))
  · unfold ControlPointEncodingDevelop.borrowOut at h
    rw [renameProgram_support] at h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    have hr := OutSpareDevelop.output_support hc hy
    rw [outPorts_eq] at hr
    exact outputs y (List.mem_toFinset.mp hr)
end

theorem entryY (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (encodeY (ParityUniform.entryYAll layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (EntryFuse.fusedY_support layout layout_widths c
    (ParityUniform.entryYAll_wires layout layout_widths c hq)))

theorem exitY (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (encodeY (ParityUniform.exitYAll layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (ExitFusionResearch.exitY_support layout layout_widths c
    (ParityUniform.exitYAll_wires layout layout_widths c hq)))

private theorem xs : ∀q∈xList,fit (UG (duringX (E1QubitPlacement.pmapR layout q)))=true := by
  intro q hq
  rw [UG_fast]
  exact xsFit q hq

private theorem placedX {P : Program} (h : wires P ⊆ (tSites base (base 2400)).toFinset) :
    ∀x∈wires (renameProgram (E1QubitPlacement.pmapR layout) P), fit (UG (duringX x))=true := by
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact xs y (List.mem_toFinset.mp (h hy))

theorem entryX (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) c)) := by
  apply lifted
  intro x hx
  have sw (w : Wire) (hw : w ∈ wires (FlagEntry.swp (FlagEntry.pkW layout)
      (E1QubitPlacement.pmapR layout (base 514)))) : fit (UG (duringX w))=true := by
    rw [UG_fast]
    exact allSites_sound (by decide +kernel : allSites (fun z => fit (StairPlaceFast.ugB (duringX z)))
      (FlagEntry.swp (FlagEntry.pkW layout) (E1QubitPlacement.pmapR layout (base 514)))=true) w hw
  unfold FlagEntry.entryXNew at hx
  split_ifs at hx
  · rw [wires_append,Finset.mem_union] at hx
    exact hx.elim (sw x) (placedX (tailX_tight base (base 2400) c.val) x)
  · rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hx
    rcases hx with h|h|h
    · exact placedX ccx_tight x h
    · exact sw x h
    · exact placedX (evenTail_tight c.val) x h

def phaseWire (q : Wire) := wireFn2 layout (Rolling1588Lifetime.phaseHost q)
private def piX (q : Wire) := phaseWire (ParityXExitInverse23Kernel.pi q)
private theorem invs : ∀q∈xList,fit (UG (duringX (piX q)))=true := xs

theorem exitX (k : Nat) : ∀q∈wires (ParityXExitInverse23Kernel.x1N k),
    fit (UG (duringX (phaseWire q))) = true := by
  intro x hx
  unfold ParityXExitInverse23Kernel.x1N at hx
  rw [renameProgram_support] at hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  unfold ParityXExit.programN at hb
  rw [wires_append,Finset.mem_union] at hb
  rcases hb with hb|hb
  · exact invs b (List.mem_toFinset.mp (exitMerge_tight base (base 2400) k
      (ParityXExit.programAll_wires _ _ k (ParityXExit.prefix_sub _ _ k hb))))
  · change fit (UG (duringX (piX b)))=true
    rw [UG_fast]
    exact allSites_sound (by decide +kernel : allSites (fun z => fit (StairPlaceFast.ugB (duringX (piX z))))
      (FlagEntry.swp (base 514) (base 722))=true) b hb

end ECDSAAdd.Entrant.Stair44OuterSites

end

section

namespace ECDSAAdd.Entrant.Stair44OuterY
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
open ParityUniform FlagEntry ParityEven Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

private def poolSite (q : Wire) : Prop := q∈layout.dialogPool ∧ q≠pkW layout
private theorem metadata : ∀ ab∈yPairs, poolSite ab.1 ∧ poolSite ab.2 := by unfold poolSite; decide +kernel

private theorem entries (v : State) (flag : Bool) (clean : regValue layout.dialogPool v.basis=0) :
    YClean (put v (pkW layout) flag) := by
  intro ab hab
  have c (q : Wire) (ok : poolSite q) : (put v (pkW layout) flag).basis q=false := by
    have z := (regValue_zero _ _).mp clean q ok.1
    simpa [put,writeBit,Function.update_apply,ok.2] using z
  exact ⟨c _ (metadata ab hab).1,c _ (metadata ab hab).2⟩

private theorem realPool (s : State) (v : State) (clean : regValue layout.dialogPool s.basis = 0)
    (keep : ∀ q,q∉layout.point.y→v.basis q=s.basis q) : regValue layout.dialogPool v.basis=0 := by
  exact (regValue_congr _ _ _ (fun q hq => keep q
    (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans clean

private theorem flag_away : pkW layout ≠ layout.core.generic := by decide +kernel

theorem entry (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis=Y.val) (clean : regValue layout.dialogPool s.basis=0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (entryYAll layout k)) m actual) =
      run (entryYAll layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (entries s flag clean)
  rw [run_put _ _ _ _ _ (pk_not_Y layout layout_widths layout_nodup _ flag_away),
    entryYAll_eq layout layout_widths layout_nodup Y k s m hy clean]
  have fy := EntryFuse.fusedY_correct layout layout_widths layout_nodup Y k s m hy clean
  exact entries _ flag (realPool _ _ clean fy.2.2)

theorem exit (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis=centerWord Y) (clean : regValue layout.dialogPool s.basis=0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (exitYAll layout k)) m actual) =
      run (exitYAll layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (entries s flag clean)
  rw [run_put _ _ _ _ _ (FlagExit.pk_not_exitY layout layout_widths layout_nodup _ flag_away),
    exitYAll_eq layout layout_widths layout_nodup Y k s m m hy clean]
  have fy := ExitFusionResearch.exitY_correct layout layout_widths layout_nodup Y k s m hy clean
  exact entries _ flag (realPool _ _ clean fy.2.2)

end ECDSAAdd.Entrant.Stair44OuterY

end

section

namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] wires run E1Reflected.comparePart E1Reflected.Square31.afterCompare
def compareLabels (w : Nat → Wire) (g : Wire) :=
  [g,w 513,w 514] ++ E1Reflected.xR w ++ E1Reflected.srcR w ++ E1Reflected.cR w
theorem compare_support_tight (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (E1Reflected.comparePart w g k) ⊆ (compareLabels w g).toFinset := by
  have mask := maskedConstant_wires_subset g (E1Reflected.srcR w) k
  have cmp := (compareLt_wires none (E1Reflected.xR w) (E1Reflected.srcR w) (E1Reflected.cR w)
    (w 513) (w 514) (by simp [E1Reflected.srcR,E1Reflected.xR,wireBlock_length])
    (by simp [E1Reflected.cR,E1Reflected.srcR,wireBlock_length])).1
  have left : wires (maskedConstant g (E1Reflected.srcR w) k) ⊆ (compareLabels w g).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (mask hq)
    simp only [compareLabels,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  unfold E1Reflected.comparePart
  rw [wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff,cmp]
  refine ⟨⟨left,?_⟩,left⟩
  intro q h
  simp only [compareLabels,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at *
  tauto
def compareWire (q : Wire) := permutation StairSquareEntryR.entryPairs (pmapR Baselines.layout q)
def suffixWire (q : Wire) := permutation moves (pmapR Baselines.layout q)
def labels := ((compareLabels base (base 2400)).map compareWire ++
    (E1Reflected.Square31.mS5 base (base 2400)).map suffixWire) ++ [4374,4629]
theorem uses_labels (k : Fp) : wires (routed k) ⊆ labels.toFinset := by
  intro q h
  simp only [routed,candidate,comparePhase,suffix,placed,fused,wires_append,renameProgram_support,
    Finset.mem_union,Finset.mem_image] at h
  simp only [labels,List.mem_toFinset,List.mem_append,List.mem_map]
  rcases h with ((⟨x,⟨y,hy,rfl⟩,rfl⟩ | ⟨x,⟨y,hy,rfl⟩,rfl⟩) | h)
  · exact Or.inl (Or.inl ⟨y,List.mem_toFinset.mp (compare_support_tight base (base 2400) k.val hy),rfl⟩)
  · exact Or.inl (Or.inr ⟨y,List.mem_toFinset.mp (E1Reflected.Square31.afterCompare_support _ _ _ hy),rfl⟩)
  · right
    simpa [Arithmetic.swapBits,wires,Instr.wires,or_comm,or_left_comm,or_assoc] using h
end ECDSAAdd.Entrant.StairEntryRehost

end

section

namespace ECDSAAdd.Entrant.StairArchiveTen
open CodecBitSliceVerify StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch

def first (j : Nat) (rev : Bool) := packet (!rev) (if rev then j+1 else j)
def second (j : Nat) (rev : Bool) := packet (!rev) (if rev then j else j+1)

def ten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (first j rev ++ (fieldHook j (shift rev) ++
    (second j rev ++ fieldHook j (leave rev))))

/-- Segment-local observation times of the two real arithmetic calls. -/
def tapeA (j : Nat) (rev : Bool) (m : List Bool) := m.drop (measurementCount (fieldHook j (enter rev)))
def tapeS (j : Nat) (rev : Bool) (m : List Bool) := (tapeA j rev m).drop (measurementCount (first j rev))
def tapeB (j : Nat) (rev : Bool) (m : List Bool) := (tapeS j rev m).drop (measurementCount (fieldHook j (shift rev)))
def tapeL (j : Nat) (rev : Bool) (m : List Bool) := (tapeB j rev m).drop (measurementCount (second j rev))

def refMiddle (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (first j rev) (tapeA j rev m) s
def refExit (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (second j rev) (tapeB j rev m) (refMiddle j rev m s)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem ten_run (j : Nat) (hs : j∈starts) (hj : j∈List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row<63145) (m : List Bool) (a r : State)
    (arch : frame j row (inputCols (enter rev)) a)
    (same : exterior j a r) (ph : a.phase = r.phase)
    (before_ : frame j row (canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (refMiddle j rev m r))
    (after_ : frame j row (canonical rev rev) (refExit j rev m r)) :
    let actual := run (ten j rev) m a
    let final := refExit j rev m r
    actual.phase=final.phase ∧ exterior j actual final ∧ frame j row (outputCols (leave rev)) actual := by
  let a0 := run (fieldHook j (enter rev)) m a
  let a1 := run (first j rev) (tapeA j rev m) a0
  let a2 := run (fieldHook j (shift rev)) (tapeS j rev m) a1
  let a3 := run (second j rev) (tapeB j rev m) a2
  let a4 := run (fieldHook j (leave rev)) (tapeL j rev m) a3
  have f : a1.phase=(refMiddle j rev m r).phase ∧ exterior j a1 (refMiddle j rev m r) ∧
      frame j row (inputCols (shift rev)) a1 := by
    simpa only [fromStage, toStage, before, after, Bool.false_eq_true, if_false, Bool.xor_false,
      first, refMiddle] using stage_packet j hs hj rev false row hr m (tapeA j rev m) a r
        arch same ph before_ (by simpa only [after, Bool.false_eq_true, if_false, Bool.xor_false, first, refMiddle] using middle_)
  have z : a3.phase=(refExit j rev m r).phase ∧ exterior j a3 (refExit j rev m r) ∧
      frame j row (inputCols (leave rev)) a3 := by
    have eq : (if rev ^^ true then j+1 else j) = (if rev then j else j+1) := by cases rev <;> rfl
    simpa only [fromStage, toStage, before, after, if_true, eq, second, refExit] using
      stage_packet j hs hj rev true row hr (tapeS j rev m) (tapeB j rev m) a1 (refMiddle j rev m r)
        f.2.2 f.2.1 f.1 middle_ (by simpa only [after, if_true, eq, second, refExit] using after_)
  have last := StairArchiveAllPorts.field_run j hj (leave rev) row hr (tapeL j rev m) a3 z.2.2
  have shape : run (ten j rev) m a = a4 := by
    simp only [ten, run_append, run_take]
    rfl
  rw [shape]
  exact ⟨last.1.trans z.1, fun q hq => (last.2.2 q hq).trans (z.2.1 q hq), last.2.1⟩

end ECDSAAdd.Entrant.StairArchiveTen

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open Arithmetic Secp256k1 CompressedPointDialog MappedCompressed StairSquareContract StairSquareAssembly
set_option maxHeartbeats 1500000
attribute [local irreducible] run wires

/-- The three branches use the same expanded inner-S bank; the tail leaves the
one live high bit on the carrier consumed by the following integer stage. -/
def program (k : Fp) : Program :=
  let hs := StairSqLoopA.hostDomain
  placedN (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs) ++
    StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))

abbrev hs := StairSqLoopA.hostDomain
theorem coreOK : CoreOK L0 (coreN (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs)) := by
  let sub : hs.Sublist StairSqLoopA.hostDomain := List.Sublist.refl _
  have a := StairSquareBodyOK.bodyA_ok44 hs sub
  have b := StairSqBodyB.bodyB_ok44 hs sub
  have c := StairSquareBodyOK.bodyC_ok44 hs sub
  exact coreN_coreOK _ _ _ _ _ _ a b c
    (StairSquareKernel26C.kC_run_eq44 hs _ c (StairSquareBodyC.bodyC_avoids44 hs sub))
    (StairSquareKernel26C.kB_run_eq44 hs _ b (StairSqBodyB.bodyB_avoids44 hs sub))
    (StairSquareKernel26C.kA_run_eq44 hs _ a (StairSquareBodyA.bodyA_avoids44 hs sub))

/-- On the following stage's physical carrier, the entire square executes the stock operation. -/
theorem fullRunOf (P : Program) (hP : CoreOK L0 P) (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L0 X Y G origin s.basis) :
    run (SquareCarryLoan719BF.place L0 P ++ StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))) m1 s = pullState StairEntryRehost.landing
      (run (SquareCarryLoan719BF.program L0 ++ fastConstAdd L0 L0.point.x k ++ E1QubitPlacement.tickF L0) m2 s) := by
  let C := SquareCarryLoan719BF.place L0 P
  let t := run C (m1.take (measurementCount C)) s
  have bound := placeG_boundary L0 hw0 hn0 P hP X Y G origin s (m1.take (measurementCount C)) v
  have clean : regValue L0.dialogPool t.basis = 0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq => bound.2.2 q (((E1QubitPlacement.lay L0 hw0 hn0 q).2.1 hq).1)), v.clean]
  let R := p-1-(X-(if G then Y*Y else 0)+(if G then (C163Low4Offsets.squareK : Fp) else 0)).val
  have pos : 0 < p := by norm_num [p]
  have hR : R < p := by dsimp only [R]; omega
  have boundary := StairEntryRehost.fullRun (k-(C163Low4Offsets.delta : Fp)) t
    (m1.drop (measurementCount C)) R bound.2.1 hR clean
  have oldTail : TailOK L0 (E1ReflectedPlacement.entryR L0) := by
    intro; intros; rfl
  have stock := squareG_base L0 hw0 hn0 P hP _ oldTail k X Y G origin s m1 m2 v
  rw [←stock]
  change run (C ++ _) m1 s = pullState _ (run (C ++ _) m1 s)
  simpa only [run_append] using boundary

theorem fullRun (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L0 X Y G origin s.basis) :
    run (program k) m1 s = pullState StairEntryRehost.landing
      (run (SquareCarryLoan719BF.program L0 ++ fastConstAdd L0 L0.point.x k ++ E1QubitPlacement.tickF L0) m2 s) :=
  fullRunOf _ coreOK k X Y G origin s m1 m2 v

end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44TailBounds
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore StairEntryRehost
abbrev L0 := Baselines.layout
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def e1B (q : Nat) : Nat :=
  StairPlaceFast.swB 1558 736 (StairPlaceFast.swB 1557 738 (StairPlaceFast.swB 1042 737
    (StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
      (StairPlaceFast.swB 527 741 q))))))

private theorem e1_eq (q : Wire) : E1QubitPlacement.sig (E1QubitPlacement.rho q) = e1B q := by
  unfold E1QubitPlacement.sig E1QubitPlacement.phaseHost E1QubitPlacement.nativeSwap
    E1QubitPlacement.rho e1B
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl

/-- `pmapR L0` in closed form (`StairPlaceFast.wireFn2_eqB`). -/
private def pmB (q : Nat) : Nat :=
  StairPlaceFast.pwB (StairPlaceFast.swB 785 1813 (e1B q) - 16)

private theorem pmapR_fast (q : Wire) : pmapR L0 q = pmB q := by
  show wireFn2 Baselines.layout (E1QubitPlacement.sig (E1QubitPlacement.rho q)) = _
  rw [StairPlaceFast.wireFn2_eqB, e1_eq]
  rfl


def good (q : Nat) : Bool :=
  (Nat.ble q 513 || Nat.beq q 4112 || (Nat.ble 4115 q && Nat.blt q 4630) ||
    (Nat.ble 4886 q && Nat.blt q 5144) || (Nat.ble 5399 q && Nat.blt q 5656) || Nat.beq q 9814) &&
  !(Nat.beq q 5515 || Nat.beq q 5655 || Nat.beq q 5400 || Nat.beq q 5401)
private def fastPrefix (x : Wire) := StairPlaceFast.swB 4840 4627 (pmB x)
private def fastSuffix (x : Wire) := StairPlaceFast.swB 4835 4373 (StairPlaceFast.swB 4836 4374
  (StairPlaceFast.swB 4837 4375 (StairPlaceFast.swB 4838 4376 (StairPlaceFast.swB 4839 4377 (pmB x)))))
private theorem prefix_eq (x : Wire) : compareWire x = fastPrefix x := by
  have eq : StairSquareEntryR.entryPairs = [(4840,4627)] := by decide +kernel
  simp only [compareWire,eq,permutation,Equiv.trans_apply,Equiv.refl_apply,fastPrefix,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapR_fast]
private theorem suffix_eq (x : Wire) : suffixWire x = fastSuffix x := by
  simp only [suffixWire,moves_eq,physicalMoves,permutation,Equiv.trans_apply,Equiv.refl_apply,fastSuffix,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapR_fast]
private theorem prefix_good : (compareLabels base (base 2400)).all
    (fun x => good (StairPlaceFast.ugB (fastPrefix x))) = true := by decide +kernel
private theorem suffix_good : (E1Reflected.Square31.mS5 base (base 2400)).all
    (fun x => good (StairPlaceFast.ugB (fastSuffix x))) = true := by decide +kernel
theorem allGood (k : Fp) (q : Wire) (hq : q ∈ wires (routed k)) : good (StairPlaceFast.ugB q) = true := by
  have h := List.mem_toFinset.mp (uses_labels k hq)
  simp only [labels,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with ((⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)|rfl|rfl)
  · rw [prefix_eq]; exact List.all_eq_true.mp prefix_good x hx
  · rw [suffix_eq]; exact List.all_eq_true.mp suffix_good x hx
  · decide +kernel
  · decide +kernel
end ECDSAAdd.Entrant.Stair44TailBounds

end

section

namespace ECDSAAdd.Entrant.Stair44Outer
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly

def kernelPlace (P : Program) := renameProgram (wireFn2 layout) P
def phasePlace (P : Program) := kernelPlace (renameProgram Rolling1588Lifetime.phaseHost P)

def reverseEnd := skywalkArithmeticClear base ++ renameProgram (sig 511) tickR ++
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)
def forwardEnd := Six505.merged6 ++ Six505.packP false ++ ForwardSixPlacement.after false ++ skywalkArithmeticClear base

def divide : Program :=
  phasePlace (Stair44WalkRun.forward true 409) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan) ++
    phasePlace reverseEnd ++ phasePlace (Stair44WalkRun.backward false 490) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (Stair44WalkRun.forward false 489) ++ phasePlace forwardEnd ++
    kernelPlace (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (Stair44WalkRun.backward true 409) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (ParityUniform.entryYAll layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (ParityUniform.exitYAll layout cy)

def borrowGeneric (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (generic cx cy))

def finite (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGeneric cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def program (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finite (.some hc) cx cy)

end ECDSAAdd.Entrant.Stair44Outer

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open Arithmetic Secp256k1 StairSquareAssembly StairSquareContract StairSquareHolesCore
set_option maxHeartbeats 1000000

theorem routedMetrics (k : Fp) :
    toffoliCount (StairEntryRehost.routed k) = toffoliCount (E1ReflectedPlacement.entryR L0 k) ∧
    measurementCount (StairEntryRehost.routed k) = measurementCount (E1ReflectedPlacement.entryR L0 k) ∧
    Challenge.gateSlots (StairEntryRehost.routed k) = Challenge.gateSlots (E1ReflectedPlacement.entryR L0 k) + 3 := by
  obtain ⟨t,m,g⟩ := StairEntryRehost.counts k
  have st : toffoliCount (swapBits 4374 4629) = 0 := rfl
  have sm : measurementCount (swapBits 4374 4629) = 0 := rfl
  have sg : Challenge.gateSlots (swapBits 4374 4629) = 3 := rfl
  simp only [StairEntryRehost.routed,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,t,m,g,st,sm,sg,Nat.add_zero,and_self]

theorem routedPhysical (k : Fp) : GatePhysical (StairEntryRehost.routed k) := by
  have p := E1ReflectedPlacement.entryR_physical L0 Baselines.layout_widths Baselines.layout_nodup k
  rw [StairEntryRehost.stock_split,gatePhysical_append] at p
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨hostRename_physical _ _ p.1,hostRename_physical _ _ p.2⟩,swapBits_physical _ _ (by decide)⟩

theorem changingTail (P : Program) (k : Fp) :
    toffoliCount (P ++ StairEntryRehost.routed k) = toffoliCount (P ++ StairSquareEntryR.entryRH k) ∧
    measurementCount (P ++ StairEntryRehost.routed k) = measurementCount (P ++ StairSquareEntryR.entryRH k) ∧
    Challenge.gateSlots (P ++ StairEntryRehost.routed k) = Challenge.gateSlots (P ++ StairSquareEntryR.entryRH k) + 3 := by
  obtain ⟨t,m,g⟩ := routedMetrics k
  obtain ⟨et,em⟩ := StairSquareEntryR.entryRH_counts k
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    t,m,g,et,em,StairSquareEntryR.entryRH_slots,Nat.add_assoc,and_self]

theorem metrics (k : Fp) :
    toffoliCount (program k) = toffoliCount (A161Generic.squareEntry L0 k) + 328 ∧
    measurementCount (program k) = measurementCount (A161Generic.squareEntry L0 k) ∧
    Challenge.gateSlots (program k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 3 := by
  have h : toffoliCount (program k) = toffoliCount (StairSquareFinal.square hs k) ∧
      measurementCount (program k) = measurementCount (StairSquareFinal.square hs k) ∧
      Challenge.gateSlots (program k) = Challenge.gateSlots (StairSquareFinal.square hs k) + 3 :=
    changingTail _ _
  have c := StairSquareFinal.square_counts hs k
  exact ⟨h.1.trans c.1,h.2.1.trans c.2,h.2.2.le.trans (Nat.add_le_add_right (StairSquareFinal.square_slots_le hs k) 3)⟩

theorem physical (k : Fp) : GatePhysical (program k) := by
  have p := StairSquareFinal.square_physical hs k
  rw [StairSquareFinal.square,squareN,gatePhysical_append] at p
  exact (gatePhysical_append _ _).mpr ⟨p.1,routedPhysical _⟩
end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly StairSquareSites
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires
theorem hs_eq : hs = (List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5 := by decide +kernel
private theorem good_sites (q : Wire) (h : Stair44TailBounds.good q = true) :
    q ∈ StairHoleSupport.recordArena ∧ q ∉ StairHoleSupport.oldHoles ∧ q ∉ hs := by
  have old : ∀ v ∈ StairPhysicalLayout.oldHolesNat, Stair44TailBounds.good v = false := by decide +kernel
  have retired : ∀ v ∈ hs, Stair44TailBounds.good v = false := by rw [hs_eq]; decide +kernel
  refine ⟨?_,fun ho => Bool.noConfusion ((old q (StairPhysicalLayout.oldHoles_eq ▸ ho)).symm.trans h),
    fun hr => Bool.noConfusion ((retired q hr).symm.trans h)⟩
  rw [StairPhysicalLayout.recordArena_eq]
  simp only [StairPhysicalLayout.arenaNat,List.mem_append,List.mem_cons,List.mem_range'_1,
    List.not_mem_nil,or_false]
  simp only [Stair44TailBounds.good,Bool.and_eq_true,Bool.or_eq_true,Nat.ble_eq,Nat.blt_eq,Nat.beq_eq] at h
  rcases h.1 with (((((hq|hq)|hq)|hq)|hq)|hq)
  · cases q with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ n => omega
  all_goals first | (subst q; decide) | omega
theorem tailPiece (k : Fp) : StairSiteAvoidance.PieceOK hs StairSiteAvoidance.UG (StairEntryRehost.routed k) := by
  have spec (q : Wire) (hq : q ∈ wires (StairEntryRehost.routed k)) :=
    good_sites _ (Stair44TailBounds.allGood k q hq)
  have maps (q : Wire) : StairSiteAvoidance.UG q = StairPlaceFast.ugB q := StairPlaceFast.ug_eqB q
  constructor
  · intro q hq
    rw [maps q]
    exact ⟨(spec q hq).1,(spec q hq).2.1⟩
  · intro q hq
    rw [maps q]
    exact (spec q hq).2.2
private theorem fixedPlace : ∀ q ∈ hs, placeFn q = q := by
  rw [hs_eq]
  simp only [LT48K.placeFn_eq]
  decide +kernel
private theorem fixedUG : ∀ q ∈ hs, StairSiteAvoidance.UG q = q := by
  rw [hs_eq]
  change ∀ q ∈ _, Wrapper5.U _ ((Equiv.swap _ _) (StairOuterPlacement.rho Baselines.layout q)) = q
  simp only [StairPlaceFast.ug_eqB]
  decide +kernel
theorem piece (k : Fp) : StairSiteAvoidance.PieceOK hs StairSiteAvoidance.UG (program k) := by
  let sub : hs.Sublist StairSqLoopA.hostDomain := List.Sublist.refl _
  have member : ∀q∈hs, q∈StairSqLoopA.hostDomain := fun _ h => h
  have avC := StairSquareKernel26C.kC_avoids44 hs member _ (StairSquareBodyOK.bodyC_ok44 hs sub)
    (StairSquareBodyC.bodyC_avoids44 hs sub)
  have avB := StairSquareKernel26C.kB_avoids44 hs member _ (StairSqBodyB.bodyB_ok44 hs sub)
    (StairSqBodyB.bodyB_avoids44 hs sub)
  have avA := StairSquareKernel26C.kA_avoids44 hs member _ (StairSquareBodyOK.bodyA_ok44 hs sub)
    (StairSquareBodyA.bodyA_avoids44 hs sub)
  have hostsGood : ∀ h ∈ StairSquareKernel26C.hostsK,
      StairSiteAvoidance.UG (placeFn h) ∈ StairHoleSupport.recordArena ∧
        StairSiteAvoidance.UG (placeFn h) ∉ StairHoleSupport.oldHoles := by
    intro h hh
    obtain ⟨n, h1, h2, rfl⟩ := StairSquareKernel26C.hostsK_pool h hh
    exact host_good n h1 h2
  have arena := placedN_arenaB (StairSquareBodyA.bodyA hs) (StairSqBodyB.bodyB hs)
    (StairSquareBodyC.bodyC hs) (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs) StairSquareKernel26C.hostsK
    (StairSquareBodyA.bodyA_coarse44 hs sub) (StairSquareBodyA.bodyA_fine44 hs sub)
    (StairSquareBodyC.bodyC_fine44 hs sub) (StairSqBodyB.bodyB_support44 hs sub)
    (StairSqBodyB.bodyB_normFlag44 hs sub (StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _)))
    (StairSquareKernel26C.kC_support hs _) (StairSquareKernel26C.kB_support hs _)
    (StairSquareKernel26C.kA_support hs _) hostsGood
  have unplaced := coreN_avoids hs _ _ _ avC avB avA
  apply StairSiteAvoidance.PieceOK.append _ (tailPiece _)
  refine ⟨arena,?_⟩
  intro x hx hxh
  have ex : x = StairSiteAvoidance.UG x := UG_inj (fixedUG _ hxh).symm
  unfold placedN at hx
  rw [placed_wires, Finset.mem_image] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have ey : y = StairSiteAvoidance.UG (placeFn y) := placeFn_inj (ex.trans (fixedPlace _ hxh).symm)
  rw [ey] at hy
  exact unplaced _ hxh hy
end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44PhaseSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairRestSupport Stair44Outer StairConcreteAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

private theorem fromValid {P : Program} (chk : allSites valid P = true) : PieceOK holes PP P := by
  apply Stair44OuterSites.fits
  intro q hq
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace q) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact allSites_sound chk q hq

theorem reverseTail : PieceOK holes PP reverseEnd := by
  unfold reverseEnd
  exact ((fromValid (by decide +kernel)).append (fromValid (by decide +kernel))).append (fromValid (by decide +kernel))

theorem forwardTail : PieceOK holes PP forwardEnd := by
  unfold forwardEnd
  exact (((fromValid (by decide +kernel)).append (fromValid (by decide +kernel))).append (fromValid (by decide +kernel))).append
    (fromValid (by decide +kernel))

theorem exitX (k : Nat) : PieceOK holes UG (Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))) := by
  apply Stair44OuterSites.fits
  intro q hq
  simp only [Stair44PointMap.switchX,phasePlace,kernelPlace,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩ := hq
  exact Stair44OuterSites.exitX k x hx
end ECDSAAdd.Entrant.Stair44PhaseSites

end

section

namespace ECDSAAdd.Entrant.Stair44Physical
open Arithmetic MappedCompressed Secp256k1 Baselines StairPhysicalV3 StairRestSupport
  Stair44Outer StairConcreteAssembly Stair44WalkMap
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
attribute [local irreducible] wires GatePhysical

private theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
  ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩

private theorem firstDom (q : Wire) (h : InDom q) : InDom (first q) := by
  unfold first shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))

private theorem restDom (q : Wire) (h : InDom q) : InDom (rest q) := by
  unfold rest shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))

private theorem fw (d : Bool) (n : Nat) (h : Sound (Rolling1588TickGap.forward d 1 (15+n))) :
    Sound (Stair44WalkRun.forward d n) := by
  rw [forward_append] at h
  obtain ⟨a,b⟩ := parts h
  exact sound_append (sound_rename _ first.injective firstDom a)
    (sound_rename _ rest.injective restDom b)

private theorem bw (d : Bool) (n : Nat) (h : Sound (Rolling1588.reverse d 1 (15+n))) :
    Sound (Stair44WalkRun.backward d n) := by
  rw [reverse_append] at h
  obtain ⟨a,b⟩ := parts h
  exact sound_append (sound_rename _ rest.injective restDom a)
    (sound_rename _ first.injective firstDom b)

private theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

theorem dividePhysical : GatePhysical divide := by
  have eq : InverseFive23.lastPhase15 false = reverseEnd ++
      Rolling1588.reverse false 1 505 ++ FrontierEntry1591NativeH.inverse base := by
    simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
      reverseEnd,List.append_assoc]
  have h := sound_lastPhase15
  rw [eq] at h
  have ⟨a,native⟩ := parts h
  have ⟨tail,walk⟩ := parts a
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 409 sound_forward424),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 490 walk)⟩,phase (sound_rename _ first.injective firstDom native)⟩

theorem multiplyPhysical (k : Nat) : GatePhysical (multiply k) := by
  have eq : Rolling1588TickGap.tailPhase false = Rolling1588TickGap.forward false 1 504 ++ forwardEnd := by
    simp only [Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
      forwardEnd,List.append_assoc]
  have h := sound_tailPhase
  rw [eq] at h
  have ⟨walk,tail⟩ := parts h
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_exitFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw false 489 walk),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 409 sound_reverse424)⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

theorem genericPhysical (cx cy : Fp) : GatePhysical (generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.1.1.1,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical⟩,
    Stair44Square.physical _⟩,multiplyPhysical _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.2.2⟩

theorem physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    let C : Point := .some hc
    have m := AboveFieldPointDevelop.middle_physical C cx cy
    simp only [AboveFieldPointDevelop.middle,gatePhysical_append] at m
    apply gatePhysical_rename _ (Wrapper5.U layout).injective
    simp only [finite,gatePhysical_append]
    refine ⟨⟨gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_,?_⟩,
      gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_⟩
    · simp only [gatePhysical_append]
      exact ⟨⟨FlagTop.stageNew_physical hc,m.1.1.1.1⟩,m.1.1.1.2⟩
    · exact gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ FlagTop.rho_injective _ (genericPhysical cx cy))
    · simp only [gatePhysical_append]
      exact ⟨⟨m.1.2,m.2⟩,ControlPointEncodingDevelop.borrowOut_physical hc⟩
end ECDSAAdd.Entrant.Stair44Physical

end

section

namespace ECDSAAdd.Entrant.Stair44Resources
open Arithmetic Secp256k1 MappedCompressed Baselines StairConcreteAssembly Stair44Outer Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000
attribute [local irreducible] toffoliCount measurementCount gateSlots

/-- All three physical costs ignore wire labels and add across adjacent phases. -/
structure Cost where
  measure : Program → Nat
  append (a b : Program) : measure (a ++ b) = measure a + measure b
  rename (f : Wire → Wire) (a : Program) : measure (renameProgram f a) = measure a
  forward (d : Bool) (n : Nat) : measure (Stair44WalkRun.forward d n) =
    measure (Rolling1588TickGap.forward d 1 (15+n))
  backward (d : Bool) (n : Nat) : measure (Stair44WalkRun.backward d n) =
    measure (Rolling1588.reverse d 1 (15+n))

def tc : Cost := ⟨toffoliCount,toffoliCount_append,fun f a => (renameProgram_counts f a).1,
  fun d n => (Stair44WalkRun.metrics d n).1.1,fun d n => (Stair44WalkRun.metrics d n).2.1⟩
def mc : Cost := ⟨measurementCount,measurementCount_append,fun f a => (renameProgram_counts f a).2,
  fun d n => (Stair44WalkRun.metrics d n).1.2.1,fun d n => (Stair44WalkRun.metrics d n).2.2.1⟩
def slots : Cost := ⟨gateSlots,gateSlots_append,rename_gateSlots,
  fun d n => (Stair44WalkRun.metrics d n).1.2.2,fun d n => (Stair44WalkRun.metrics d n).2.2.2⟩

theorem divide_eq (c : Cost) : c.measure divide = c.measure (hostedEntryRest layout) := by
  simp only [divide,kernelPlace,phasePlace,hostedEntryRest,StairSchedule.stackForward6,
    reverseEnd,InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
    c.append,c.rename,c.forward,c.backward,Nat.add_assoc]

theorem multiply_eq (c : Cost) (k : Nat) : c.measure (multiply k) = c.measure (hostedExitRest layout k) := by
  simp only [multiply,kernelPlace,phasePlace,hostedExitRest,Stair44PointMap.switchX,forwardEnd,
    Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
    StairHostsSchedule.lastXN,StairSchedule.stackReverse15,c.append,c.rename,c.forward,c.backward,Nat.add_assoc]

theorem finite_eq (c : Cost) (C : Point) (cx cy : Fp)
    (sq : c.measure (Stair44Square.program (ReflectionE1.correction cx)) =
      c.measure (StairSquareFinal.squareEntryHL StairSqLoopA.holes layout (ReflectionE1.correction cx))) :
    c.measure (finite C cx cy) = c.measure (hostedFinite C cx cy) := by
  simp only [finite,borrowGeneric,generic,hostedFinite,hostedMiddle,hostedBorrowGeneric,hostedGenericBlock,
    hostedGeneric,hostedSecondStage,Stair44PointMap.encode,Stair44PointMap.encodeY,Stair44PointMap.switchX,
    c.append,c.rename,divide_eq,multiply_eq,sq,Nat.add_assoc]

theorem totals (C : Point) : toffoliCount (program C) ≤ 2169965 ∧ measurementCount (program C) ≤ 1520924 := by
  have h := StairCountsHosted.count_totals C
  change toffoliCount (concreteProgram C) ≤ 2169965 ∧ measurementCount (concreteProgram C) ≤ 1520924 at h
  cases C with
  | zero => exact h
  | @some cx cy hc =>
    let k := ReflectionE1.correction cx
    have old := StairSquareFinal.square_counts StairSqLoopA.holes k
    have new := Stair44Square.metrics k
    have ft := finite_eq tc (.some hc) cx cy (by
      change toffoliCount (Stair44Square.program k) = toffoliCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; exact new.1.trans old.1.symm)
    have fm := finite_eq mc (.some hc) cx cy (by
      change measurementCount (Stair44Square.program k) = measurementCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; exact new.2.1.trans old.2.symm)
    change toffoliCount _ = toffoliCount _ at ft
    change measurementCount _ = measurementCount _ at fm
    simp only [program,concreteProgram,hostedWrapper,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨ft.le.trans h.1,fm.le.trans h.2⟩
open StairSlotsPlan

theorem slotBound (C : Point) : gateSlots (program C) ≤ 50860482 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    let C : Point := .some hc
    let dE := v3Plan.entryDelta v3Costs v3Boundary1806
    let dX := v3Plan.exitDelta v3Costs v3Boundary1806
    have de : gateSlots divide ≤ gateSlots (ParityStageBothInverse23.restEntry layout) + dE := by
      have eq := divide_eq slots
      change gateSlots divide = gateSlots (hostedEntryRest layout) at eq
      rw [eq]
      exact entryRestOf_slots_le checkpointPrimitives hostPlan _ _ v3WalkFacts
        (v3GroupFacts _) (v3BoundaryFacts _) layout
    have dx : gateSlots (multiply cx.val) ≤ gateSlots (ParityXExitInverse23Kernel.restXXN layout cx.val) + dX := by
      have eq := multiply_eq slots cx.val
      change gateSlots (multiply cx.val) = gateSlots (hostedExitRest layout cx.val) at eq
      rw [eq]
      exact exitRestOf_slots_le checkpointPrimitives hostPlan _ _ v3WalkFacts
        (v3GroupFacts _) (v3BoundaryFacts _) layout cx.val
    have sq : gateSlots (Stair44Square.program (ReflectionE1.correction cx)) ≤
        gateSlots (A161Generic.squareEntry layout (ReflectionE1.correction cx)) + 3 :=
      (Stair44Square.metrics (ReflectionE1.correction cx)).2.2
    have gen : gateSlots (generic cx cy) ≤ gateSlots (FlagExit.genericN layout cx cy) + (dE + dX) + 3 := by
      simp only [generic,FlagExit.genericN,FlagExit.secondStageN,Stair44PointMap.encodeY,
        Stair44PointMap.switchX,gateSlots_append,rename_gateSlots]
      omega
    have whole : gateSlots (program C) ≤ gateSlots (AboveFieldPointDevelop.programQ C) + (dE + dX) + 3 := by
      simp only [C,program,finite,borrowGeneric,Stair44PointMap.encode,AboveFieldPointDevelop.programQ,
        AboveFieldPointDevelop.wrapperBorrow,AboveFieldPointDevelop.finiteBorrow,AboveFieldPointDevelop.middle,
        ControlPointEncodingDevelop.borrowGeneric,ControlPointEncodingDevelop.genericBlock,
        gateSlots_append,rename_gateSlots] at ⊢
      omega
    have sum : dE + dX = 344736 := v3_slotDelta_1806
    have old := AboveFieldPointDevelop.program_slots_Q C
    change gateSlots (program C) ≤ 50860482
    omega
end ECDSAAdd.Entrant.Stair44Resources

end

section

namespace ECDSAAdd.Entrant.Stair44FieldSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairConcreteAssembly Stair44Outer
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

private theorem entryTail : PieceOK holes TP (StairHostsSchedule.entryTailPrefix pr hp) := by
  have pk := packEnd_rows
  unfold StairHostsSchedule.entryTailPrefix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact Stair44Groups.hostedGroup44 true 0 1 84 (by decide)
  · exact forwardSegment_ok hsub 87 62 (by decide) (by decide) (by decide) pk.1
  · exact Stair44Groups.hostedGroup44 true 14 85 5 (by decide)
  · exact forwardSegment_ok hsub 62 47 (by decide) (by decide) (by decide) pk.2.1
  · exact Stair44Groups.hostedGroup44 true 23 90 3 (by decide)
  · exact forwardSegment_ok hsub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
  · exact Stair44Groups.hostedGroup44 true 31 93 3 (by decide)
  · exact forwardSegment_ok hsub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
  · exact Stair44Groups.hostedGroup44 true 37 96 2 (by decide)
  · exact forwardSegment_ok hsub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
  · exact Stair44Groups.hostedGroup44 true 42 98 2 (by decide)
  · exact forwardLast_ok hsub

private theorem exitHead : PieceOK holes TP (StairHostsSchedule.exitHeadSuffix pr hp) := by
  have up := unpackEnd_rows
  unfold StairHostsSchedule.exitHeadSuffix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact reverseLast_ok hsub
  · exact Stair44Groups.hostedGroup44 false 42 98 2 (by decide)
  · exact reverseSegment_ok hsub 22 12 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.2
  · exact Stair44Groups.hostedGroup44 false 37 96 2 (by decide)
  · exact reverseSegment_ok hsub 32 22 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.1
  · exact Stair44Groups.hostedGroup44 false 31 93 3 (by decide)
  · exact reverseSegment_ok hsub 47 32 (by decide) (by decide) (by decide) (by decide)
      up.2.2.1
  · exact Stair44Groups.hostedGroup44 false 23 90 3 (by decide)
  · exact reverseSegment_ok hsub 62 47 (by decide) (by decide) (by decide) (by decide)
      up.2.1
  · exact Stair44Groups.hostedGroup44 false 14 85 5 (by decide)
  · exact reverseSegment_ok hsub 87 62 (by decide) (by decide) (by decide) (by decide) up.1
  · exact Stair44Groups.hostedGroup44 false 0 1 84 (by decide)

theorem entry : PieceOK holes KP (StairHostsSchedule.entryFieldHosted pr hp) := by
  have ps := ok_of_all hsub paritySetup_all
  have hx := ok_of_all hsub hostedX_all
  unfold StairHostsSchedule.entryFieldHosted
  refine ((((PieceOK.append ?_ ps).append hx).append ?_).append hx).append ps
  · apply ok_field
    unfold StairHostsSchedule.entryLowPrefix
    refine ((PieceOK.append (StairFirstPacketHosted.hostedFirstPacket_pieceOK holes hsub true) (ok_of_all hsub scratchClear_all)).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    exact ok_borrow (entryTail)
  · apply ok_field
    unfold StairHostsSchedule.entryLowSuffix
    refine ((ok_of_all hsub scratchClear_all).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    apply ok_borrow
    unfold StairHostsSchedule.entryTailSuffix
    exact ((Stair44Groups.hostedGroup44 true 44 100 2 (by decide)).append endpointD |>.append (ok_of_all hsub copyN_all)).append
      canon

theorem exit : PieceOK holes KP (StairHostsSchedule.exitFieldHosted pr hp) := by
  have ps := ok_of_all hsub paritySetup_all
  have hx := ok_of_all hsub hostedX_all
  unfold StairHostsSchedule.exitFieldHosted
  refine ((((ps.append hx).append ?_).append ps).append hx).append ?_
  · apply ok_field
    unfold StairHostsSchedule.exitLowPrefix
    refine ((ok_of_all hsub scratchClear_all).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    apply ok_borrow
    unfold StairHostsSchedule.exitHeadPrefix
    exact ((center.append (ok_of_all hsub copyN_all)).append endpointM).append
      (Stair44Groups.hostedGroup44 false 44 100 2 (by decide))
  · apply ok_field
    unfold StairHostsSchedule.exitLowSuffix
    exact (((ok_of_all hsub scratchClear_all).append (ok_borrow (exitHead))).append
      (ok_of_all hsub scratchUnprefix_all)).append (StairFirstPacketHosted.hostedFirstPacket_pieceOK holes hsub false)

private theorem phase {P : Program} (v : PieceOK holes PP P) : PieceOK holes UG (Stair44Outer.phasePlace P) :=
  ok_kernel (ok_phase v)

theorem divide : PieceOK holes UG Stair44Outer.divide :=
  (((((phase (Stair44PhaseSites.forward true 409 (by decide))).append (phase Stair44FirstRow.pack)).append
    (ok_kernel entry)).append (phase Stair44PhaseSites.reverseTail)).append
    (phase (Stair44PhaseSites.backward false 490 (by decide)))).append (phase Stair44PhaseSites.native)

theorem multiply (k : Nat) : PieceOK holes UG (Stair44Outer.multiply k) :=
  (((((phase (Stair44PhaseSites.forward false 489 (by decide))).append (phase Stair44PhaseSites.forwardTail)).append
    (ok_kernel exit)).append (phase Stair44FirstRow.unpack)).append
    (phase (Stair44PhaseSites.backward true 409 (by decide)))).append (Stair44PhaseSites.exitX k)
end ECDSAAdd.Entrant.Stair44FieldSites

end

section

namespace ECDSAAdd.Entrant.Stair44Release
open Arithmetic Secp256k1 Challenge Baselines StairSiteAvoidance Stair44Outer
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
attribute [local irreducible] wires renameProgram qubits toffoliCount measurementCount gateSlots

abbrev holes := StairPhysicalInventory.physicalHoles

theorem squareSites (k : Fp) : PieceOK holes UG (Stair44Square.program k) := by
  have sub : ∀ q ∈ holes, q ∈ Stair44Square.hs := by
    change ∀ q ∈ StairPhysicalInventory.physicalHoles, _
    rw [StairPhysicalLayout.physicalHoles_eq_nat,Stair44Square.hs_eq]
    decide +kernel
  have s := Stair44Square.piece k
  exact ⟨s.1,fun q hq h => s.2 q hq (sub _ h)⟩

theorem qubitBound (de : PieceOK holes UG divide) (mu : ∀ k, PieceOK holes UG (multiply k))
    (C : Point) : qubits (program C) ≤ 1542 := by
  have listOK := StairCertificate.holeList_of_physical_sub holes
    (by rw [show holes = StairPhysicalLayout.newHolesNat from StairPhysicalLayout.physicalHoles_eq_nat]; decide)
    (fun _ h => h)
  have len : 1586 - holes.length = 1542 := by
    rw [show holes = StairPhysicalLayout.newHolesNat from StairPhysicalLayout.physicalHoles_eq_nat]
    decide
  rw [←len]
  apply StairCertificate.qubits_le_holes _ listOK _
  apply holePlacement_of_ok
  cases C with
  | zero => exact pieceOK_nil holes _
  | @some cx cy hc =>
    apply ok_wrapper
    exact ((Stair44OuterSites.initial hc).append (ok_generic
      ((((((Stair44OuterSites.entryY (-cy)).append (Stair44OuterSites.entryX (-cx))).append de).append
        (squareSites (ReflectionE1.correction cx))).append (mu cx.val)).append (Stair44OuterSites.exitY cy)))).append
      (Stair44OuterSites.finalPart hc)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2169965,1520924,1542,50860482⟩

theorem certificateOf
    (sem : ∀ C b R, Triple (encodes b R) (program C) (encodes b (if b then R+C else R)))
    (de : PieceOK holes UG divide) (mu : ∀ k, PieceOK holes UG (multiply k)) :
    Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (Stair44Physical.physical C)
  toffoli_le C := (normalize_toffoli _).trans (Stair44Resources.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1520924
    rw [normalize_measurements]; exact (Stair44Resources.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1542
    rw [normalize_qubits]; exact qubitBound de mu C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 50860482
    rw [normalize_slots]; exact Stair44Resources.slotBound C
theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (program C) (encodes b (if b then R+C else R))) :
    Certificate entry bounds :=
  certificateOf sem Stair44FieldSites.divide Stair44FieldSites.multiply
end ECDSAAdd.Entrant.Stair44Release

end
