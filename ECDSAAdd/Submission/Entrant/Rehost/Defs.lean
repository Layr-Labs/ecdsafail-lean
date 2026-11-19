import ECDSAAdd.Submission.Entrant.StairMain
/-!
# S2: re-hosting pool 724 (physical 4839) of S1 at top level: shared definitions

S1 = the rival entry e204f403 (pool 723 retired by definition-level re-hosts on pool 300) plus k41 A-.
Its program `StairConcreteAssembly.concreteProgram C` as a flat list of fourteen physical pieces, the
placements, the tracked physical wires and the hosts. In S1 `x1N` carries the extra swap
`base 723 <-> base 300`, so `p8` / `p9` carry it too.
-/
namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed
open StairConcreteAssembly

/-- The concrete layout. -/
abbrev L0 : ControlledPointLayout := Baselines.layout

/-- Placement of the outer pieces. -/
def fU : Wire → Wire := Wrapper5.U L0
/-- Placement of the generic block (`hostedBorrowGeneric`). -/
def fG : Wire → Wire :=
  fun q => Wrapper5.U L0 (Equiv.swap L0.doubleSelect L0.control (FlagTop.rho L0 q))
/-- Placement of kernel labels (`base i`). -/
def fK : Wire → Wire := fun q => fG (wireFn2 L0 q)
/-- Placement of labels of the integer phases. -/
def fP : Wire → Wire := fun q => fK (Rolling1588Lifetime.phaseHost q)

/-! ## Tracked physical wires (C = G dump, `dump/g/touch.tsv`) -/
/-- pool 724: the parked x-flag `FlagEntry.pkW`, a temporary of `entryXNew` / `x1N`, a square bit. -/
def wE : Wire := 4839
/-- pool 723: a temporary of `entryXNew` / `x1N`, `OutFlag.wW` in `borrowOut`, a square bit. -/
def wD : Wire := 4838
/-- generic placement of pool 717 (`base 717`): a measured ancilla of both field passes and of `borrowOut`;
untouched by every piece before the entry field and by the integer phases. -/
def wZ : Wire := 4112
/-- pool 720: host of the phase label `base 1542`, a measured ancilla in every use; untouched after `x1N`. -/
def wA : Wire := 4835
/-- pool 722: host of the phase label `base 1541`; untouched after `x1N`. -/
def wC : Wire := 4837

/-! ## The fourteen physical pieces, in execution order -/
section
variable (C : Point) (cx cy : Fp)

def p0 : Program := renameProgram fU (FlagTop.stageNew L0 C (FlagEntry.pkW L0))
def p1 : Program := renameProgram fU (AboveFieldPointDevelop.encode C)
def p2 : Program := renameProgram fU AboveFieldPointDevelop.eraseB
def p3 : Program := renameProgram fG (ParityUniform.entryYAll L0 (-cy))
def p4 : Program := renameProgram fG (FlagEntry.entryXNew L0 (FlagEntry.pkW L0) (-cx))
/-- The whole division kernel after the caller's fused first tick. -/
def p5 : Program := renameProgram fG (hostedEntryRest L0)
def p6 : Program :=
  renameProgram fG (StairSquareFinal.squareEntryHL StairSqLoopA.holes L0 (ReflectionE1.correction cx))
/-- The multiplication kernel up to and including the reverse integer walk. -/
def p7 : Program :=
  renameProgram fK
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false) ++
      StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan ++
      renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.stackReverse15 checkpointPrimitives))
/-- `x1N` without its final park. -/
def p8 : Program :=
  renameProgram fP (renameProgram (Equiv.swap (base 723) (base 300))
    (renameProgram ParityXExitInverse23Kernel.pi (ParityXExit.prefixAll base (base 2400) cx.val)))
/-- The park of `x1N`: two CNOTs moving the flag onto pool 724. -/
def p9 : Program :=
  renameProgram fP (renameProgram (Equiv.swap (base 723) (base 300))
    (renameProgram ParityXExitInverse23Kernel.pi (FlagEntry.swp (base 514) (base 722))))
def p10 : Program := renameProgram fG (ParityUniform.exitYAll L0 cy)
def p11 : Program := renameProgram fU AboveFieldPointDevelop.loadB
def p12 : Program := renameProgram fU (AboveFieldPointDevelop.decode C)
def p13 : Program := renameProgram fU (ControlPointEncodingDevelop.borrowOut C)

/-- The record program, flat. -/
def flat : Program :=
  p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx ++ p9 ++ p10 cy ++ p11 ++ p12 C ++ p13 C

/-- The first `j` pieces. -/
def pre : Nat → Program
  | 0 => []
  | 1 => p0 C
  | 2 => p0 C ++ p1 C
  | 3 => p0 C ++ p1 C ++ p2
  | 4 => p0 C ++ p1 C ++ p2 ++ p3 cy
  | 5 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx
  | 6 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5
  | 7 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx
  | 8 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7
  | 9 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx
  | 10 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx ++ p9
  | 11 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx ++ p9 ++ p10 cy
  | 12 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx ++ p9 ++ p10 cy ++ p11
  | 13 => p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx ++ p9 ++ p10 cy ++ p11 ++ p12 C
  | _ => flat C cx cy

end

/-- "Wire `w` is zero after the first `j` pieces, on every valid input and every measurement record."
`C = .some hc` with coordinates `cx cy`; boundary `j = 0` is the input, `j = 14` the output. -/
def CleanAt {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (j : Nat) (w : Wire) : Prop :=
  ∀ (b : Bool) (R : Point) (s : State), encodes b R s.basis →
    ∀ m : List Bool, (run (pre (.some hc) cx cy j) m s).basis w = false

end ECDSAAdd.Entrant.Rehost
