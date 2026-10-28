import ECDSAAdd.Arithmetic.Paper935.PublicSlotExternalSupport
import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerSupport
import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Growing history and borrowing its detector cannot address an already owned
wire outside the persistent history inputs. -/
theorem compileGrowingHistory_external_support (A B D : Arena) (record work : List Wire) (capacity : Nat)
    (one zz pos sign output port frozen : Wire) (counter coeffBits : List Wire) (H : HistoryLayout)
    (h : compileGrowingHistory A record capacity one zz pos sign output port frozen counter coeffBits=
      some (B,D,work,H)) (q : Wire) (owned : q∈A.live)
    (away : q∉[one,zz,pos,sign,output,port,frozen]++counter++coeffBits++record) :
    q∈B.live ∧ q∉H.record ∧ q∉recordedWires H.program := by
  have hc := compileGrowingHistory_contract A B D record work capacity one zz pos sign output port frozen counter coeffBits H h
  have grow := hc.1
  unfold planHistoryGrow at grow
  obtain ⟨⟨B',extra⟩,hb,he⟩ := Option.bind_eq_some_iff.mp grow
  have eqs : B'=B ∧ record++extra=H.record := by simpa using he
  have bankEq := eqs.1
  subst B'
  have first := (A.borrowMany_live B _ extra hb).1
  have retained : q∈B.live := by rw [first]; exact Finset.mem_union_left _ owned
  have noExtra : q∉extra := by
    have hv := (A.reserve_success extra.toFinset).mp ⟨B,(A.borrowMany_contract B _ extra hb).2.2⟩
    exact fun hq => Finset.disjoint_left.mp hv.2 owned (List.mem_toFinset.mpr hq)
  have noWork : q∉work := by
    have hv := (B.reserve_success work.toFinset).mp ⟨D,(B.borrowMany_contract D _ work hc.2.1).2.2⟩
    exact fun hq => Finset.disjoint_left.mp hv.2 retained (List.mem_toFinset.mpr hq)
  have noRecord : q∉H.record := by
    rw [←eqs.2]
    simp only [List.mem_append,not_or] at away ⊢
    exact ⟨away.2,noExtra⟩
  refine ⟨retained,noRecord,?_⟩
  intro hq
  have hm := compileHistory_support one zz pos sign output port frozen counter coeffBits H.record work H hc.2.2 hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm away
  clear * - hm away noRecord noWork
  tauto

/-- The actual historical slot retains an external owner and keeps both public
streams and the measured history program off that owner's wire. -/
theorem compileHistoricalSlot_external_support (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (q : Wire) (owned : q∈A.live) (noMeta : q∉F.wires)
    (noRows : q∉b.rows.flatMap WindowRow.wires) (noRecord : q∉record) :
    q∈Q.historyArena.live ∧ q∉Q.slot.front.exitBank.rows.flatMap WindowRow.wires ∧
    q∉Q.history.record ∧ q∉recordedWires (Q.program F) ∧ q∉wires (Q.slot.inverse F) := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have pc := compileCheckedPublicSlot_contract A b addWidth exitWidth F armed probeWidth offset Q.slot hc.1
  have counterNonempty : F.counter≠[] := by
    intro he
    have hz := pc.2.1.1
    simp [he] at hz
  have coefficientNonempty : Q.slot.front.exitBank.fv.payload≠[] := by
    intro he
    have hv := hc.2.2.2.1
    simp [WindowRow.wires,he] at hv
  have front := compilePublicSlot_external_support A b addWidth exitWidth F armed probeWidth offset Q.slot pc.1
    counterNonempty coefficientNonempty q owned noMeta noRows
  have noCoeff : q∉(Q.slot.front.exitBank.fv.wires.drop 1).take 6 := by
    intro hh
    apply front.2.1
    have hm := List.mem_of_mem_drop (List.mem_of_mem_take hh)
    simp [WindowBank.rows,hm]
  have signMem : F.counter.getLastD 0∈F.counter := by
    rw [hc.2.1]
    simp
  have noSign : q≠F.counter.getLastD 0 := fun he => noMeta (by
    simp only [SlotRegisters.wires,List.mem_append]
    exact Or.inl (Or.inr (he ▸ signMem)))
  have hist := compileGrowingHistory_external_support Q.slot.front.exitArena Q.historyArena Q.detectorArena
    record Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2 q front.1 (by
      simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at noMeta ⊢
      clear * - noMeta noSign noCoeff noRecord
      tauto)
  refine ⟨hist.1,front.2.1,hist.2.1,?_,front.2.2.2⟩
  simpa only [HistoricalSlot.program,recordedWires_append,embedRecorded_wires,Finset.mem_union,not_or] using
    And.intro front.2.2.1 hist.2.2

end ECDSAAdd.Arithmetic.Paper935
