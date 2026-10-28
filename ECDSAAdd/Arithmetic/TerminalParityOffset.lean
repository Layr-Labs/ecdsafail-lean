import ECDSAAdd.Arithmetic.TerminalParityZeroBridge
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityOffset
open BalancedCleanupOffset BalancedField
attribute [local irreducible] run

def core (L : Layout) : Program :=
  TerminalParityZeroHead.program (offsetBits L).tail L.y.tail L.r.tail
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


theorem core_eq_old_of_clears (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (mOld mNew : List Bool) (hz : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hclear : (run (BalancedCleanupOffsetZero.core L) mOld s).basis L.parity=false) :
    run (core L) mNew s=run (BalancedCleanupOffsetZero.core L) mOld s := by
  obtain ⟨a,xs,y,ys,c,cs,d,ds,ey,er,ec,ed,lx,ly,lc,ld⟩ := heads L hw
  have bitlen : (offsetBits L).tail.length=255 := (tails L hw).1
  have nd := L.chainND hn
  rw [ey,er,ec,ed] at nd
  have shortND : ([a,y,L.one,L.cout,d,L.parity]++(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have fresh : ∀w∈mappedWires (offsetBits L).tail,
      w∉[a,y,L.one,L.cout,d,L.parity]++(xs++ys++cs++ds) := by
    intro w hq hm
    have mem : w∈mappedWires (offsetBits L) := by
      rw [offset_head]
      exact mapped_tail_member _ _ _ hq
    have away := offsetSources_away L hn w mem
    rw [ey,er,ec,ed] at away
    apply away
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have cleanC : ∀q∈c::cs,s.basis q=false := by simpa only [ec] using hd
  have cleanD : ∀q∈d::ds,s.basis q=false := by simpa only [ed] using hc
  have oldClear : (run (BalancedCleanupOffsetZeroHead.program (offsetBits L).tail xs ys cs ds
      a y L.one L.cout d L.parity) mOld s).basis L.parity=false := by
    simpa only [BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using hclear
  have eq := TerminalParityZeroHead.eq_old_of_clears (offsetBits L).tail xs ys cs ds
    a y L.one L.cout d L.parity shortND fresh (by omega) (by omega) (by omega) (by omega)
    s mOld mNew hz (cleanD d (by simp)) (fun q hq => cleanC q (by simp [hq]))
      (fun q hq => cleanD q (by simp [hq])) oldClear (by intro e; simp [e] at ly)
  simpa only [core,BalancedCleanupOffsetZero.core,ey,er,ec,ed,List.tail_cons,List.headD_cons] using eq

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


theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hcout : s.basis L.cout=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hd : ∀q∈L.offsetCarry,s.basis q=false)
    (hP : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=run (BalancedCleanupOffsetZero.program L) m s := by
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
  have old := BalancedCleanupOffsetZero.correct L hw hn R Y B hr hy s m
    hR hY hS hz ho hcout hc hd hP
  rw [BalancedCleanupOffsetZero.program,sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2] at old
  have oldClear : (run (BalancedCleanupOffsetZero.core L) m u).basis L.parity=false := by
    have bit := congrArg (fun t : State => t.basis L.parity) old
    change (run (front L).reverse [] (run (BalancedCleanupOffsetZero.core L) m u)).basis L.parity=
      (writeBit s.basis L.parity false) L.parity at bit
    have away : L.parity∉wires (front L).reverse := by
      rw [wires_reverse]
      exact front_parity_away L hw hn
    rw [run_preserves_outside (front L).reverse [] (run (BalancedCleanupOffsetZero.core L) m u)
      L.parity away] at bit
    simpa only [writeBit,Function.update_self] using bit
  have eq := core_eq_old_of_clears L hw hn u m m one cleanC cleanD oldClear
  rw [program,BalancedCleanupOffsetZero.program,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,
    sandwich_run _ _ (BalancedCleanupOffsetSlim.front_counts L).2,eq]

end ECDSAAdd.Arithmetic.TerminalParityOffset
#print axioms ECDSAAdd.Arithmetic.TerminalParityOffset.core_eq_old_of_clears
#print axioms ECDSAAdd.Arithmetic.TerminalParityOffset.correct
