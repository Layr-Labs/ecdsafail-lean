import ECDSAAdd.Submission.Entrant.SixCarryBase
import ECDSAAdd.Submission.Entrant.SixCarryPrefixData
namespace ECDSAAdd.Entrant.SixCarryLoopAnchor
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ManyACarryDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ZeroSetDevelop.compileS?
abbrev L := LowAccCarryDevelop.L
abbrev c := LowAccCarryDevelop.c
abbrev ga := LowAccCarryDevelop.ga

def output : Program := ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map (fun cm=>cm.out)).getD []
def build : Program := buildMany 86 ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L) LowAccCarryDevelop.loans88
 L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L)
def loop : Program := build++(output++LowAccCarryDevelop.afterLoop)
def originalBody : Program :=
 ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim
  (ParkCarry10Develop.body L c) LowAccCarryDevelop.bodyWith

theorem one_shape (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 BData301.p0) :
 LowAccCarryDevelop.bodyWith (LowAccCarryDevelop.fromLiteral cm)=
 FullBTemp.prefixP L++(build++(cm.out++LowAccCarryDevelop.afterLoop)) := by
 have h := LowAccCarryDevelop.body_shape (LowAccCarryDevelop.fromLiteral cm)
 have hout : (LowAccCarryDevelop.fromLiteral cm).out=cm.out := by
  delta LowAccCarryDevelop.fromLiteral
  rfl
 rw [hout] at h
 simpa only [LowAccCarryDevelop.beforeLoop,FullBTemp.prefixP,build,List.append_assoc] using h

theorem option_context {α β : Type} (result : Option α) (ok : result.isSome=true)
 (transport : α→β) (body : β→Program) (out : α→Program) (fallback pre : Program)
 (f : Program→Program) (hshape : ∀cm,body (transport cm)=pre++f (out cm)) :
 (result.map transport).elim fallback body=pre++f ((result.map out).getD []) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at ok
 | some cm => exact hshape cm

theorem body_shape : originalBody=FullBTemp.prefixP L++loop := by
 delta originalBody loop output
 exact option_context (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0)
  LowAccCarryDevelop.success_literal LowAccCarryDevelop.fromLiteral LowAccCarryDevelop.bodyWith
  (fun cm=>cm.out) (ParkCarry10Develop.body L c) (FullBTemp.prefixP L)
  (fun out=>build++(out++LowAccCarryDevelop.afterLoop)) one_shape

def strip : Instr→Instr := SixCarryTrace.stripPhase

theorem literal_anchor : (loop.take 11960).map strip=SixCarryPrefixData.program := by
 apply ParkAProgramBool.programEq_sound
 delta loop output build
 rw [LowAccMiddleLiteral.compiler_output_eq]
 decide +kernel
end ECDSAAdd.Entrant.SixCarryLoopAnchor
