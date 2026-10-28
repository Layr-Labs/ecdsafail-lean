import ECDSAAdd.Arithmetic.PointAddSpec
import ECDSAAdd.Arithmetic.PointAddResources
import ECDSAAdd.Arithmetic.SwapRegisters

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 点加共用一套算术布局，额外四线为外部控制与三个最终输出选择位。 -/
structure ControlledPointLayout where
  core : PointAddLayout
  control : Wire
  genericSelect : Wire
  doubleSelect : Wire
  infinitySelect : Wire

namespace ControlledPointLayout

def point (L : ControlledPointLayout) := L.core.input
def temporary (L : ControlledPointLayout) := L.core.output
def selectors (L : ControlledPointLayout) := [L.genericSelect,L.doubleSelect,L.infinitySelect]
def extras (L : ControlledPointLayout) := L.control::L.selectors
def outWork (L : ControlledPointLayout) := L.core.work++L.selectors
def work (L : ControlledPointLayout) := PointAddLayout.pointWires L.temporary++L.outWork
def wires (L : ControlledPointLayout) := L.core.wires++L.extras
def Widths (L : ControlledPointLayout) := L.core.Widths

def selected (L : ControlledPointLayout) : PointAddLayout := { L.core with generic:=L.genericSelect }

theorem core_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.core.wires.Nodup :=
  (List.nodup_append'.mp hn).1

theorem selected_widths (L : ControlledPointLayout) (h : L.Widths) : L.selected.Widths := by
  exact ⟨h.inputX,h.inputY,h.outputX,h.outputY,h.words,h.divisor,h.inverse,h.pool⟩

theorem selected_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.selected.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  simp only [selected,wires,extras,selectors,PointAddLayout.wires,PointAddLayout.work,PointAddLayout.flags,PointAddLayout.words,
    List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem extra_not_core (L : ControlledPointLayout) (hn : L.wires.Nodup) (w : Wire) (hw : w∈L.extras) :
    w∉L.core.wires := fun hc => List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hc hw

end ControlledPointLayout

end ECDSAAdd.Arithmetic
