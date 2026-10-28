import ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlimProof
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run BalancedCleanupOffsetSlim.chain

def core (L : Layout) : Program :=
  BalancedCleanupOffsetZeroHead.program (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity

def program (L : Layout) : Program := front L++core L++(front L).reverse
attribute [local irreducible] core

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

/-- The skipped carry is replaced by the same known-zero One input in the
actual emitted tail. The two circuits may use completely independent records. -/
theorem core_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (mOld mNew : List Bool) (hz : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (BalancedCleanupOffsetSlim.chain (offsetBits L) L.y L.r L.offsetCarry L.carry
      L.one L.cout L.parity) mOld s=run (core L) mNew s := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have bitlen : (offsetBits L).tail.length=255 := (tails L hw).1
  have nd := L.chainND hn
  rw [ey,er,ec,ed] at nd
  have fresh : ∀w∈mappedWires (offsetBits L).tail,
      w∉L.parity::L.one::L.cout::((a::xs)++(y::ys)++(c::cs)++(d::ds)) := by
    intro w hq
    have mem : w∈mappedWires (offsetBits L) := by
      rw [offset_head]
      exact mapped_tail_member _ _ _ hq
    simpa only [ey,er,ec,ed] using offsetSources_away L hn w mem
  have cleanC : ∀q∈c::cs,s.basis q=false := by simpa only [ec] using hd
  have cleanD : ∀q∈d::ds,s.basis q=false := by simpa only [ed] using hc
  have eq := BalancedCleanupOffsetZeroHead.chain_equiv (offsetBits L).tail xs ys cs ds
    a y c d L.one L.cout L.parity nd fresh (by omega) (by omega) (by omega) (by omega)
    s mOld mNew hz cleanC cleanD
  rw [offset_head,ey,er,ec,ed]
  simpa only [core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using eq

private theorem sandwich_run (P Q : Program) (hz : measurementCount P=0)
    (s : State) (m : List Bool) :
    run (P++Q++P.reverse) m s=run P.reverse [] (run Q m (run P [] s)) := by
  simp only [List.append_assoc]
  rw [run_append,hz,List.take_zero,List.drop_zero,run_append,run_take]
  have zero : measurementCount P.reverse=0 := by rw [measurementCount_reverse,hz]
  have a := run_take P.reverse (m.drop (measurementCount Q)) (run Q m (run P [] s))
  rw [zero,List.take_zero] at a
  exact a.symm

private theorem bank_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.carry++L.offsetCarry) : q∉L.r ∧ q∉L.y ∧ q≠L.lower ∧ q≠L.cout := by
  have nd : (L.r++(L.y++(L.carry++L.offsetCarry))).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (L.allND hn)).2.1
  have r := List.nodup_append'.mp nd
  have y := List.nodup_append'.mp r.2.1
  refine ⟨fun h => List.disjoint_left.mp r.2.2 h (List.mem_append_right _ hq),
    fun h => List.disjoint_left.mp y.2.2 h hq,?_,?_⟩
  · intro e
    exact L.flagAway hn L.lower (by simp) (by simp [←e,List.mem_append.mp hq])
  · intro e
    exact L.flagAway hn L.cout (by simp) (by simp [←e,List.mem_append.mp hq])

/-- Complete wrapper equality on the original canonical contract. The actual
front supplies the clean One/banks; the Clifford reverse ignores record shifts. -/
theorem program_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (program L) m s=run (BalancedCleanupOffsetSlim.program L) m s := by
  let u := run (front L) [] s
  have prepared := front_value L hw hn R Y B hr hy s [] hR hY hS hz hcout
  have flags := L.flagsND hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have oR : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have oY : L.one∉L.y := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have one : u.basis L.one=false := (prepared.2.2.2.2 _ oR oY (by tauto) (by tauto)).trans ho
  have cleanC : ∀q∈L.carry,u.basis q=false := by
    intro q hq
    have a := bank_away L hn q (List.mem_append_left _ hq)
    exact (prepared.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2).trans (hc q hq)
  have cleanD : ∀q∈L.offsetCarry,u.basis q=false := by
    intro q hq
    have a := bank_away L hn q (List.mem_append_right _ hq)
    exact (prepared.2.2.2.2 q a.1 a.2.1 a.2.2.1 a.2.2.2).trans (hd q hq)
  have eq := core_eq L hw hn u m m one cleanC cleanD
  rw [program,BalancedCleanupOffsetSlim.program_sandwich,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,←eq]

/-- Exact cleanup oracle: phase and every site except parity are restored. -/
theorem xor_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ decide (q < |2*R-signedY B Y|))⟩ := by
  rw [program_eq L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd]
  exact BalancedCleanupOffsetSlim.xor_correct L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd

theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  simpa only [hA,Bool.xor_self] using xor_correct L hw hn R Y B hr hy s m hR hY hS hz ho hcout hc hd

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (program L)=510 ∧ measurementCount (program L)=510 := by
  have t := tails L hw
  have h := BalancedCleanupOffsetZeroHead.counts (offsetBits L).tail L.y.tail L.r.tail
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
  have tail := (BalancedCleanupOffsetSlim.chain_support (offsetBits L).tail xs ys cs ds
    L.one d L.parity (by omega) (by omega) (by omega) (by omega)).trans pool
  have small : wires [.X y]⊆W ∧ wires (majority a y L.cout d)⊆W ∧
      wires (eraseCarry a y L.cout d)⊆W := by
    simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,aW,yW,dW,coutW]
  have co : wires (core L)⊆W := by
    simp only [core,ey,er,ec,ed,List.tail_cons,List.headD_cons,
      BalancedCleanupOffsetZeroHead.program,wires_append,Finset.union_subset_iff]
    exact ⟨⟨small.1,small.2.1⟩,tail,small.2.2,small.1⟩
  have old := BalancedCleanupOffsetSlim.support L hw
  rw [BalancedCleanupOffsetSlim.program_sandwich] at old
  simp only [program,wires_append,Finset.union_subset_iff] at old ⊢
  exact ⟨⟨old.1.1,co⟩,old.2⟩
end ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero.core_eq
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero.xor_correct
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero.correct
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero.counts
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZero.support
