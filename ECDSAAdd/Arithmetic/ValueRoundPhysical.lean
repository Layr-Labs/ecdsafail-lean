import ECDSAAdd.Arithmetic.ValueBodyPhysical
import ECDSAAdd.Arithmetic.CounterPhysical
import ECDSAAdd.Arithmetic.ValueRound
import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum KaliskiRoundLayout

theorem recordRound_physical (L : KaliskiRoundLayout) (hn : L.wires.Nodup) :
    GatePhysical (recordRound L) := by
  have h := L.record_controls_nodup hn
  have hc := L.record_compare_nodup hn
  have hs : L.bothWork ≠ L.swap := fun e => (List.nodup_cons.mp hc).1 (by simp [e])
  have cmp := compareLt_physical (some L.bothWork) L.v L.u (L.data.reg .carry)
    L.cin L.swap hc.tail (by intro c hh; cases hh; exact hs)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at h
  simp only [recordRound,gatePhysical_append]
  exact ⟨⟨by simp_all [GatePhysical,PhysicalInstr,ProperGate,ne_comm],cmp⟩,
    by simp_all [GatePhysical,PhysicalInstr,ProperGate,ne_comm]⟩

theorem loadActive_physical (L : KaliskiRoundLayout) (hn : L.wires.Nodup) :
    GatePhysical (loadActive L) := by
  have h := (List.nodup_append'.mp (L.controls_data_nodup hn)).1
  simp only [controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at h
  simp_all [loadActive,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem valueRounds_physical (L : KaliskiRoundLayout) (hn : L.wires.Nodup) (i : Nat) :
    GatePhysical (valueRound L i) ∧ GatePhysical (valueUnround L i) := by
  have bodyN : ([L.active,L.swap,L.subtract]++L.data.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp (L.controls_data_nodup hn) w
    simp only [controls,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have body := valueBodies_physical L.data L.active L.swap L.subtract bodyN
  have count := counters_physical L.counter (L.counter_nodup hn)
  have back := counters_physical L.counter.swapCounter
    (L.counter.swapCounter_perm.nodup_iff.mpr (L.counter_nodup hn))
  have zero := zeroControlled_physical L.active L.done (L.data.zeroBits .v) (L.zero_nodup hn)
  have active := counterActiveXor_physical L.comparator L.active i (L.comparator_nodup hn)
  have recd := recordRound_physical L hn
  have load := loadActive_physical L hn
  simp only [valueRound,valueUnround,roundActiveXor,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨load,recd⟩,body.1⟩,count.1⟩,zero⟩,active⟩,
    ⟨⟨⟨⟨⟨active,zero⟩,body.2⟩,back.2⟩,recd⟩,load⟩⟩

end ECDSAAdd.Arithmetic
