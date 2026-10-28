import ECDSAAdd.Framework.Cost
import ECDSAAdd.Math.BitcoinCurve

namespace ECDSAAdd
open Lean

/-- 按寄存器类型读取逻辑值；断言里的 r=v 就展开为此谓词。 -/
class Holds (α : Type) (β : Type) where
  holds : BasisState → α → β → Prop

instance : Holds Wire Bool := ⟨fun st w v => st w = v⟩

def regValue (r : List Wire) (st : BasisState) : Nat :=
  r.foldr (fun w acc => (if st w then 1 else 0) + 2 * acc) 0

instance : Holds (List Wire) Nat := ⟨fun st r n => regValue r st = n⟩

/-- 有限点标志和两个小端坐标寄存器；无穷远点采用全零表示。 -/
structure PointReg where
  finite : Wire
  x : List Wire
  y : List Wire

instance : Holds PointReg Secp256k1.Point where
  holds st r p := match Secp256k1.coordinates p with
    | none => st r.finite = false ∧ regValue r.x st = 0 ∧ regValue r.y st = 0
    | some (x, y) => st r.finite = true ∧ regValue r.x st = x.val ∧ regValue r.y st = y.val

/-- 对所有初始相位和所有测量结果：满足前置条件时，相位恢复且后置条件成立。
这是 monomial 判断；相位恢复必须证明，不由语法保证。 -/
def Triple (P : BasisState → Prop) (c : Program) (Q : BasisState → Prop) : Prop :=
  ∀ (s : State) (m : List Bool), P s.basis →
    (run c m s).phase = s.phase ∧ Q (run c m s).basis

syntax:30 "{{" term,+ "}}" term "{{" term,+ "}}" : term
macro_rules
  | `({{ $ps,* }} $c {{ $qs,* }}) => do
    let st := mkIdent `st
    let conv : TSyntax `term → MacroM (TSyntax `term)
      | `($x = $v) => `(Holds.holds $st $x $v)
      | t => pure t
    let conj (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
      let ts ← ts.mapM conv
      ts[1:].foldlM (fun acc t => `($acc ∧ $t)) ts[0]!
    let p ← conj ps.getElems
    let q ← conj qs.getElems
    `(Triple (fun $st => $p) $c (fun $st => $q))

namespace Triple
variable {P P' Q Q' R : BasisState → Prop} {c d : Program}

/-- 顺序组合：前一段的后置条件是后一段的前置条件。 -/
theorem seq (hc : Triple P c Q) (hd : Triple Q d R) : Triple P (c ++ d) R := by
  intro s m hP
  rw [run_append]
  obtain ⟨hphase, hQ⟩ := hc s (m.take (measurementCount c)) hP
  obtain ⟨hphase', hR⟩ := hd _ (m.drop (measurementCount c)) hQ
  exact ⟨hphase'.trans hphase, hR⟩

/-- 加强前置条件、削弱后置条件。 -/
theorem conseq (hP : ∀ s, P' s → P s) (hc : Triple P c Q)
    (hQ : ∀ s, Q s → Q' s) : Triple P' c Q' := by
  intro s m h
  obtain ⟨hp, hq⟩ := hc s m (hP _ h)
  exact ⟨hp, hQ _ hq⟩

/-- 只依赖程序外部线路的断言可以随程序保持。 -/
theorem frame (hc : Triple P c Q)
    (hR : ∀ s t, (∀ w, w ∉ wires c → s w = t w) → R s → R t) :
    Triple (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) := by
  intro s m h
  obtain ⟨hp, hq⟩ := hc s m h.1
  exact ⟨hp, hq, hR _ _ (fun w hw => (run_preserves_outside c m s w hw).symm) h.2⟩
end Triple
end ECDSAAdd
