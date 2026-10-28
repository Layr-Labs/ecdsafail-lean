import Mathlib.Data.List.Basic
import Lean

namespace ECDSAAdd
open Lean

abbrev Wire := Nat
abbrev BasisState := Wire → Bool

structure State where
  phase : Bool
  basis : BasisState

inductive Correction where
  | Z (target : Wire)
  | CZ (left right : Wire)
  deriving DecidableEq, Repr

/-- 测量只选择即时 Z/CZ 修正；后续算术与测量顺序固定。 -/
inductive Instr where
  | X (target : Wire)
  | CX (control target : Wire)
  | CCX (left right target : Wire)
  | measureX (target : Wire) (onZero onOne : List Correction)
  deriving DecidableEq, Repr

abbrev Program := List Instr

def measurementCount : Program → Nat
  | [] => 0
  | .measureX _ _ _ :: p => 1 + measurementCount p
  | _ :: p => measurementCount p

instance : Coe Correction (List Correction) := ⟨fun c => [c]⟩
macro "skip" : term => `(([] : List Correction))
syntax "if" "meas" term:max "=" num "then" term "else" term : term
macro_rules
  | `(if meas $t = $n:num then $c₁ else $c₀) =>
    if n.getNat == 1 then `(Instr.measureX $t $c₀ $c₁)
    else if n.getNat == 0 then `(Instr.measureX $t $c₁ $c₀)
    else Macro.throwError "测量结果只能是 0 或 1"

syntax "prog" "{" sepBy(term, ";", ";", allowTrailingSep) "}" : term
macro_rules
  | `(prog { $ss;* }) => `(([$ss,*] : Program))

end ECDSAAdd
