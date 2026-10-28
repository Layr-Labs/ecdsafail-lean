import ECDSAAdd.Arithmetic.OneBitRoundSpec

namespace ECDSAAdd.Arithmetic

theorem recoverSwap_counts (L : KaliskiRoundLayout) :
    toffoliCount (recoverSwap L)=1 ∧ measurementCount (recoverSwap L)=0 := by
  exact ⟨rfl,rfl⟩

/-- 正轮测量擦除，逆轮保留CCX重算，计数不再对称。 -/
theorem oneBitRound_counts (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i : Nat) :
    toffoliCount (oneBitRound L i)=12*L.data.width+31 ∧
    measurementCount (oneBitRound L i)=6*L.data.width+29 ∧
    toffoliCount (oneBitUnround L i)=12*L.data.width+32 ∧
    measurementCount (oneBitUnround L i)=6*L.data.width+28 := by
  have h := kaliskiRound_counts L hnd hw i
  have hr := recoverSwap_counts L
  have he := eraseSwap_counts L
  simp only [kaliskiRound,kaliskiUnround,oneBitRound,oneBitUnround,
    toffoliCount_append,measurementCount_append,hr.1,hr.2,he.1,he.2] at *
  omega

private theorem recoverSwap_wires_subset (L : KaliskiRoundLayout) :
    wires (recoverSwap L) ⊆ L.usedWires.toFinset := by
  have hr := L.data.reg_used_mem .r (by decide) (L.head_mem .r)
  change L.r.head!∈L.data.usedWires at hr
  have ha : L.active∈L.counter.wires := by simp [KaliskiRoundLayout.counter,AdderLayout.wires]
  intro w hw
  have hh : w=L.active ∨ w=L.r.head! ∨ w=L.swap := by
    simpa [recoverSwap,wires,Instr.wires,or_assoc,or_left_comm,or_comm] using hw
  rcases hh with rfl | rfl | rfl <;>
    simp [KaliskiRoundLayout.usedWires,hr,ha]

/-- 单轮精确支持不变；线数收益由循环复用同一交换临时位获得。 -/
theorem oneBitRound_wires (L : KaliskiRoundLayout) (hw : L.counter.width=10)
    (hd : 2≤L.data.width) (i : Nat) :
    wires (oneBitRound L i)=L.usedWires.toFinset ∧
    wires (oneBitUnround L i)=L.usedWires.toFinset := by
  have h := kaliskiRound_wires L hw hd i
  have hf : wires (oneBitRound L i)=wires (kaliskiRound L i) ∪ wires (eraseSwap L) := by
    simp only [oneBitRound,kaliskiRound,wires_append]
    ac_rfl
  have hb : wires (oneBitUnround L i)=wires (kaliskiUnround L i) ∪ wires (recoverSwap L) := by
    simp only [oneBitUnround,kaliskiUnround,wires_append]
    ac_rfl
  have he : wires (eraseSwap L)=wires (recoverSwap L) := by
    rw [eraseSwap_wires]
    ext w
    simp [recoverSwap,wires,Instr.wires,or_assoc,or_left_comm,or_comm]
  rw [hf,hb,he,h.1,h.2,Finset.union_eq_left.mpr (recoverSwap_wires_subset L)]
  exact ⟨rfl,rfl⟩

theorem oneBitRound_preserves (L : KaliskiRoundLayout) (hw : L.counter.width=10)
    (hd : 2≤L.data.width) (i : Nat) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉L.usedWires) :
    (run (oneBitRound L i) m s).basis q=s.basis q ∧
    (run (oneBitUnround L i) m s).basis q=s.basis q := by
  have h := oneBitRound_wires L hw hd i
  exact ⟨run_preserves_outside _ _ _ _ (by simpa [h.1] using hq),
    run_preserves_outside _ _ _ _ (by simpa [h.2] using hq)⟩

theorem oneBitRound_qubits (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) (i : Nat) :
    qubitCount (oneBitRound L i)=7*L.data.width+48 ∧
    qubitCount (oneBitUnround L i)=7*L.data.width+48 := by
  have h := oneBitRound_wires L hw hd i
  have ho := kaliskiRound_wires L hw hd i
  simpa only [qubitCount,h.1,h.2,ho.1,ho.2] using kaliskiRound_qubits L hnd hw hd i

end ECDSAAdd.Arithmetic
