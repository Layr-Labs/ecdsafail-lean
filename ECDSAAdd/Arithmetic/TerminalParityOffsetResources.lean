import ECDSAAdd.Arithmetic.TerminalParityOffset
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
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

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=509 ∧ measurementCount (program L)=510 := by
  have t := tails L hw
  have h := TerminalParityZeroHead.counts (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [program,core,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,(BalancedCleanupOffsetSlim.front_counts L).1,
    (BalancedCleanupOffsetSlim.front_counts L).2,h.1,h.2,t.2.2.1]
  norm_num

/-- Every actual gate, including measured correction support, stays inside
the original finite layout. This is no claim of a smaller physical allocation. -/
theorem support (L : Layout) (hw : L.Widths) : wires (program L)⊆L.wires.toFinset := by
  let W := L.wires.toFinset
  have member (q : Wire) : q∈W ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry ∨ q∈L.offsetCarry := by
    simp [W,Layout.wires,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have data (q : Wire) (h : q∈L.y++L.r++L.offsetCarry++L.carry) : q∈W := by
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rw [member]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have t := tails L hw
  have aW : a∈W := data a (by simp [ey])
  have yW : y∈W := data y (by simp [er])
  have dW : d∈W := data d (by simp [ed])
  have oneW : L.one∈W := by simp [member]
  have coutW : L.cout∈W := by simp [member]
  have parityW : L.parity∈W := by simp [member]
  have pool := chain_pool_support (offsetBits L).tail xs ys cs ds L.one d L.parity W
    (fun q hq => by
      have mem : q∈mappedWires (offsetBits L) := by rw [offset_head]; exact mapped_tail_member _ _ _ hq
      rw [offsetSources L q mem]
      simp [member])
    (fun q hq => data q (by simp [ey,hq])) (fun q hq => data q (by simp [er,hq]))
    (fun q hq => data q (by simp [ec,hq])) (fun q hq => data q (by simp [ed,hq])) oneW dW parityW
  have tail := (TerminalParityMeasure.chain_support (offsetBits L).tail xs ys cs ds
    L.one d L.parity (by omega) (by omega) (by omega) (by omega)).trans pool
  have small : wires [.X y]⊆W ∧ wires (majority a y L.cout d)⊆W ∧
      wires (eraseCarry a y L.cout d)⊆W := by
    simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,aW,yW,dW,coutW]
  have co : wires (core L)⊆W := by
    simp only [core,ey,er,ec,ed,List.tail_cons,List.headD_cons,
      TerminalParityZeroHead.program,wires_append,Finset.union_subset_iff]
    exact ⟨⟨small.1,small.2.1⟩,tail,small.2.2,small.1⟩
  have old := BalancedCleanupOffsetSlim.support L hw
  rw [BalancedCleanupOffsetSlim.program_sandwich] at old
  simp only [program,wires_append,Finset.union_subset_iff] at old ⊢
  exact ⟨⟨old.1.1,co⟩,old.2⟩

end ECDSAAdd.Arithmetic.TerminalParityOffset
#print axioms ECDSAAdd.Arithmetic.TerminalParityOffset.counts
#print axioms ECDSAAdd.Arithmetic.TerminalParityOffset.support
