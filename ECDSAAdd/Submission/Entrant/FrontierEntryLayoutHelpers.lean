import ECDSAAdd.Submission.Entrant.FrontierEntrySignMath

set_option maxHeartbeats 100000
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField

def lastCarry (L : Layout) : Wire := L.carry.getD 255 0

theorem carry_split (L : Layout) (hw : L.Widths) :
    L.carry=L.carry.take 255++[lastCarry L] := by
  have hi : 255<L.carry.length := by rw [hw.2.2];decide
  have h := List.take_succ_eq_append_getElem hi
  have e : L.carry.getD 255 0=L.carry[255] := by simp [List.getD,hi]
  simpa only [show 255+1=256 from rfl,←hw.2.2,List.take_length,←e,lastCarry] using h

def scalarPorts (L : Layout) : List Wire :=
  [L.parity,L.lower,L.cout,L.minus,L.plus,lastCarry L,L.sourceGuard,L.one,L.sign]

theorem allWithLastND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (scalarPorts L++(L.r++L.y++L.carry.take 255)).Nodup := by
  have h := allND L hn
  rw [carry_split L hw] at h
  apply List.nodup_iff_count.mpr
  intro q
  have c := List.nodup_iff_count.mp h q
  simp only [scalarPorts,List.count_cons,List.count_append,List.count_nil] at c ⊢
  omega

theorem scalarPortsND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (scalarPorts L).Nodup := (List.nodup_append'.mp (allWithLastND L hw hn)).1

theorem scalarAway (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈scalarPorts L) : q∉L.r++L.y++L.carry.take 255 :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (allWithLastND L hw hn)).2.2 hq h

theorem lastCarry_mem (L : Layout) (hw : L.Widths) : lastCarry L∈L.carry := by
  rw [carry_split L hw];simp

end ECDSAAdd.Entrant.EntryHalf5
