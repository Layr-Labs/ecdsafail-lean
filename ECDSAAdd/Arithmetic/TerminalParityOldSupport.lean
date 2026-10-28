import ECDSAAdd.Arithmetic.TerminalParityOffsetResources
import ECDSAAdd.Arithmetic.TerminalParitySlimSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityOffset
open BalancedCleanupOffset BalancedField
private theorem offset_head (L : Layout) :
    offsetBits L=({wire:=none,flip:=false} : MappedBit)::(offsetBits L).tail := by
  have zero : offset.testBit 0=false := by decide
  have range : List.range 256=0::(List.range 255).map Nat.succ := List.range_succ_eq_map
  simp only [offsetBits,range,List.map_cons]
  simp only [show ¬((0 : Nat)=1) from by decide,if_false,zero,List.tail_cons]

private theorem tails (L : Layout) (hw : L.Widths) :
    (offsetBits L).tail.length=255 ∧ L.y.tail.length=255 ∧ L.r.tail.length=255 ∧
    L.offsetCarry.tail.length=255 ∧ L.carry.tail.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  simp only [List.length_tail,offsetBits_length,width.2.1,width.2.2.1,hw.2,cy]
  decide

private theorem heads (L : Layout) (hw : L.Widths) :
    ∃ a xs y ys c cs d ds, L.y=a::xs ∧ L.r=y::ys ∧ L.offsetCarry=c::cs ∧ L.carry=d::ds ∧
      xs.length=255 ∧ ys.length=255 ∧ cs.length=255 ∧ ds.length=255 := by
  have width := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have ylen : L.y.length=256 := width.2.2.1
  have rlen : L.r.length=256 := width.2.1
  have clen : L.offsetCarry.length=256 := hw.2
  have dlen : L.carry.length=256 := hw.1.2.2
  cases ey : L.y with
  | nil => simp [ey] at ylen
  | cons a xs =>
    cases er : L.r with
    | nil => simp [er] at rlen
    | cons y ys =>
      cases ec : L.offsetCarry with
      | nil => simp [ec] at clen
      | cons c cs =>
        cases ed : L.carry with
        | nil => simp [ed] at dlen
        | cons d ds =>
          refine ⟨a,xs,y,ys,c,cs,d,ds,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
          all_goals
            simp only [ey,er,ec,ed,List.length_cons] at ylen rlen clen dlen
            omega


theorem support_old (L : Layout) (hw : L.Widths) :
    wires (program L)⊆wires (BalancedCleanupOffsetZero.program L) := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have sub := TerminalParityMeasure.chain_support_slim (offsetBits L).tail xs ys cs ds
    L.one d L.parity (by have h := (tails L hw).1; omega)
      (by omega) (by omega) (by omega)
  have coreSub : wires (core L)⊆wires (BalancedCleanupOffsetZero.core L) := by
    intro q hq
    simp only [core,BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons,
      TerminalParityZeroHead.program,BalancedCleanupOffsetZeroHead.program,
      wires_append,Finset.mem_union] at hq ⊢
    have step : q∈wires (TerminalParityMeasure.chain (offsetBits L).tail xs ys cs ds
        L.one d L.parity) → q∈wires (BalancedCleanupOffsetSlim.chain (offsetBits L).tail
          xs ys cs ds L.one d L.parity) := fun h => sub h
    tauto
  intro q hq
  simp only [program,BalancedCleanupOffsetZero.program,wires_append,Finset.mem_union] at hq ⊢
  have step : q∈wires (core L) → q∈wires (BalancedCleanupOffsetZero.core L) := fun h => coreSub h
  tauto

end ECDSAAdd.Arithmetic.TerminalParityOffset
#print axioms ECDSAAdd.Arithmetic.TerminalParityOffset.support_old
