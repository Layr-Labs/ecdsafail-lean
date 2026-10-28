import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerSupport

namespace ECDSAAdd.Arithmetic.Paper935

/-- The finite counter and six coefficient selector bits are genuine views of
nonempty physical rows; these checks require no arithmetic input assumption. -/
theorem historicalViews (counter vs : List Wire) (counterNonempty : counter≠[])
    (wide : 8≤vs.length) :
    counter=counter.dropLast++[counter.getLastD 0] ∧
    vs=vs.headD 0::(vs.drop 1 |>.take 6)++vs.drop 7 ∧
    (vs.drop 1 |>.take 6).length=6 ∧ vs.drop 7≠[] := by
  have counterView : counter=counter.dropLast++[counter.getLastD 0] := by
    have hc := List.dropLast_concat_getLast counterNonempty
    have last : counter.getLastD 0=counter.getLast counterNonempty := by
      conv_lhs => rw [←hc]
      exact List.getLastD_concat
    rw [last]
    exact hc.symm
  refine ⟨counterView,?_,?_,?_⟩
  · cases vs with
    | nil => simp at wide
    | cons v vs =>
      simpa only [List.headD_cons,List.drop_succ_cons,List.drop_zero,List.cons_append] using
        congrArg (List.cons v) (List.take_append_drop 6 vs).symm
  · simp only [List.length_take,List.length_drop]
    omega
  · intro empty
    have := congrArg List.length empty
    simp only [List.length_drop,List.length_nil] at this
    omega

/-- A successfully emitted historical slot passes its final quantum address
and ordinary gate checks from persistent input ownership alone. -/
theorem compileHistoricalSlot_checked (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (owned : ([F.one,F.work0,F.work1,F.counter.getLastD 0,F.active,F.parity,F.frozen]++
      F.counter++(Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6)++record).toFinset⊆Q.slot.front.exitArena.live) :
    compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork capacity
    F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
  have physical := compileHistory_instruction_check F.one F.work0 F.work1 (F.counter.getLastD 0)
    F.active F.parity F.frozen F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6)
    Q.history.record Q.detectorWork Q.history hh.2.2
  have support := compileGrowingHistory_support Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork capacity
    F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2 owned
  have bounded := Finset.Subset.trans support Q.detectorArena.bounded
  rw [compileCheckedHistoricalSlot,h]
  dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
  rw [if_pos ⟨physical,bounded⟩]

/-- Once the arithmetic slot has compiled, its growing measured history stage
succeeds from static ownership, ordinary address separation and free capacity.
No history execution, selector or compiler-success oracle is assumed. -/
theorem compileCheckedHistoricalSlot_exists (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (P : PublicSlot)
    (compiled : compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P)
    (counterNonempty : F.counter≠[]) (wide : 8≤P.front.exitBank.fv.wires.length)
    (distinct : ([F.one,F.work0,F.work1,F.active,F.parity,F.frozen]++F.counter++
      (P.front.exitBank.fv.wires.drop 1 |>.take 6)++record).Nodup)
    (owned : ([F.one,F.work0,F.work1,F.active,F.parity,F.frozen]++F.counter++
      (P.front.exitBank.fv.wires.drop 1 |>.take 6)++record).toFinset⊆P.front.exitArena.live)
    (budget : P.front.exitArena.live.card+(capacity-record.length)+max F.counter.length 8≤935) :
    ∃ Q,compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q ∧
      Q.slot=P := by
  have views := historicalViews F.counter P.front.exitBank.fv.wires counterNonempty wide
  have signView : F.counter.getLastD 0∈F.counter := by
    exact (congrArg (fun xs => F.counter.getLastD 0∈xs) views.1).mpr (by simp)
  obtain ⟨B,D,work,H,grown⟩ := compileGrowingHistory_exists P.front.exitArena record capacity
    F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (P.front.exitBank.fv.wires.drop 1 |>.take 6) distinct owned signView (by simpa only [views.2.2.1] using budget)
  let Q : HistoricalSlot := ⟨P,B,D,work,H⟩
  have emitted : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q := by
    rw [compileHistoricalSlot,compiled]
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
    rw [if_pos views,grown]
    rfl
  have withSign : ([F.one,F.work0,F.work1,F.counter.getLastD 0,F.active,F.parity,F.frozen]++F.counter++
      (P.front.exitBank.fv.wires.drop 1 |>.take 6)++record).toFinset⊆P.front.exitArena.live := by
    intro q hq
    apply owned
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    rcases hq with (((hq|hq)|hq)|hq)
    · rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact Or.inl (Or.inl (Or.inr signView)) | simp
    · exact Or.inl (Or.inl (Or.inr hq))
    · exact Or.inl (Or.inr hq)
    · exact Or.inr hq
  exact ⟨Q,compileHistoricalSlot_checked A b record addWidth exitWidth F armed probeWidth offset capacity Q emitted withSign,rfl⟩

end ECDSAAdd.Arithmetic.Paper935
