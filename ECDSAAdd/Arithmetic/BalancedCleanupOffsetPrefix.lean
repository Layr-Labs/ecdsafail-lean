import ECDSAAdd.Arithmetic.BalancedCleanupOffsetViews
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSupport
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProof
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField

def front (L : Layout) : Program :=
  BalancedCleanup.prepareSign L.toCircuit.toLayout++view L++[.X L.cout]

theorem program_sandwich (L : Layout) : program L=
    front L++chain (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity++
      (front L).reverse := by
  simp only [program,front,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.append_assoc]

theorem front_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (front L) := by
  simp only [front,properProgram_append]
  exact ⟨⟨BalancedCleanup.prepareSign_proper _ (L.cleanupND hn),view_proper L hn⟩,
    by simp [ProperProgram,ProperGate]⟩

theorem front_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (front L) := by
  have a := (BalancedCleanup.clifford_parity_away L.toCircuit.toLayout hw.1 (L.cleanupND hn)).1
  have b := view_parity_away L hw hn
  have ne : L.parity≠L.cout := by
    have f := List.nodup_cons.mp (L.flagsND hn)
    exact fun e => f.1 (by simp [e])
  simpa only [front,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_singleton,Finset.notMem_empty,or_false,not_or] using ⟨⟨a,b⟩,ne⟩

/-- All numeric reads are proved for the actual emitted front circuit.
The frame leaves the second carry bank and all caller metadata intact. -/
theorem front_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (hc : s.basis L.cout=false) :
    let t := run (front L) m s
    regValue L.r t.basis=rawR B R ∧ regValue L.y t.basis=biasedY B R Y ∧
    t.basis L.lower=negative R ∧ t.basis L.cout=true ∧
    (∀q,q∉L.r → q∉L.y → q≠L.lower → q≠L.cout → t.basis q=s.basis q) := by
  let u := run (BalancedCleanup.prepareSign L.toCircuit.toLayout) m s
  let v := run (view L) m u
  let t := run [.X L.cout] m v
  have sign := BalancedCleanup.prepareSign_value L.toCircuit.toLayout hw.1
    (L.cleanupND hn) R hr s m hR hz
  have all := List.nodup_append'.mp (L.allND hn)
  have d := List.nodup_append'.mp (BalancedCleanup.Layout.dataND _ (L.cleanupND hn))
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have cR : L.cout∉L.r := fun h => L.flagAway hn L.cout (by simp) (by simp [h])
  have cY : L.cout∉L.y := fun h => L.flagAway hn L.cout (by simp) (by simp [h])
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by
    have f := L.flagsND hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at f
    tauto
  have cl : L.cout≠L.lower := by
    have f := L.flagsND hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at f
    tauto
  have yu : regValue L.y u.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => sign.2.2 q
      (fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]))
      (fun e => lY (e ▸ hq)))).trans hY
  have su : u.basis L.sign=B := (sign.2.2 _ sR sl).trans hS
  have cu : u.basis L.cout=false := (sign.2.2 _ cR cl).trans hc
  have value := view_value L hw hn R Y B hr hy u m sign.1 yu su sign.2.1
  have cv : v.basis L.cout=false := (value.2.2 _ cR cY).trans cu
  have execute : run (front L) m s=t := by
    have ps := properProgram_measurementCount _ (BalancedCleanup.prepareSign_proper _ (L.cleanupND hn))
    have pv := properProgram_measurementCount _ (view_proper L hn)
    have ep (z : State) : run (BalancedCleanup.prepareSign L.toCircuit.toLayout) (m.take 0) z=
        run (BalancedCleanup.prepareSign L.toCircuit.toLayout) m z := by
          simpa only [ps] using run_take (BalancedCleanup.prepareSign L.toCircuit.toLayout) m z
    have ev (z : State) : run (view L) (m.take 0) z=run (view L) m z := by
      simpa only [pv] using run_take (view L) m z
    simp only [front,List.append_assoc,run_append,ps,pv,List.drop_zero,ep,ev]
    rfl
  rw [execute]
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => by simp [t,v,run,writeBit,show q≠L.cout from fun e => cR (e ▸ hq)])).trans value.1
  · exact (regValue_congr _ _ _ (fun q hq => by simp [t,v,run,writeBit,show q≠L.cout from fun e => cY (e ▸ hq)])).trans value.2.1
  · have lv := (value.2.2 _ lR lY).trans sign.2.1
    simpa [t,run,writeBit,Ne.symm cl] using lv
  · simp [t,run,writeBit,cv]
  · intro q qr qy ql qc
    have kept := (value.2.2 q qr qy).trans (sign.2.2 q qr ql)
    simpa [t,run,writeBit,qc] using kept

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.front_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.front_parity_away
