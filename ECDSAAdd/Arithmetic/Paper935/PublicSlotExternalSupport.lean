import ECDSAAdd.Arithmetic.Paper935.SlotFrontExternalSupport

namespace ECDSAAdd.Arithmetic.Paper935

/-- Borrowed post work cannot touch a pre-owned bit outside all post inputs. -/
theorem compileBorrowedPost_external_support (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (compiled : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (q : Wire) (owned : q∈A.live) (away : q∉[one,zf,frozen,fire,active]++inputs++record)
    : q∉wires P.program ∧ q∉wires P.inverse := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P compiled
  have borrow := A.borrowMany_contract D _ work pair.1
  have reserved := (A.reserve_success work.toFinset).mp ⟨D,borrow.2.2⟩
  have noWork : q∉work := fun hq => Finset.disjoint_left.mp reserved.2 owned (List.mem_toFinset.mpr hq)
  have awayPorts : q∉P.ports := by
    intro hq
    have hm := compilePost_ports armed one zf frozen fire active inputs record work width offset P pair.2
      (List.mem_toFinset.mpr hq)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm away
    clear * - hm away noWork
    tauto
  exact ⟨fun hq => awayPorts (List.mem_toFinset.mp (P.support.1 hq)),
    fun hq => awayPorts (List.mem_toFinset.mp (P.support.2 hq))⟩

/-- The entire actual public slot preserves every pre-owned external bit on
all states and tapes; in particular, it cannot alter the persistent history. -/
theorem compilePublicSlot_external_support (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (compiled : compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P)
    (counterNonempty : F.counter≠[]) (coefficientNonempty : P.front.exitBank.fv.payload≠[])
    (q : Wire) (owned : q∈A.live) (noMeta : q∉F.wires) (noRows : q∉b.rows.flatMap WindowRow.wires) :
    q∈P.front.exitArena.live ∧ q∉P.front.exitBank.rows.flatMap WindowRow.wires ∧
      q∉wires (P.program F) ∧ q∉wires (P.inverse F) := by
  have frontCompiled := compilePublicSlot_front _ _ _ _ _ _ _ _ _ compiled
  have front := (compileSlotFront_contract A b addWidth exitWidth F P.front frontCompiled).external_support
    P.front A b addWidth exitWidth F counterNonempty coefficientNonempty q owned noMeta noRows
  have postFrame : q∉wires (P.postProgram F) ∧ q∉wires (P.postInverse F) := by
    cases armed with
    | false =>
      have post := (compilePublicSlot_unarmed A b addWidth exitWidth F probeWidth offset P compiled).1
      simp only [PublicSlot.postProgram,PublicSlot.postInverse,post,wires_reverse,and_self]
      intro hq
      apply noMeta
      simp only [retireActivity,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
        or_false] at hq
      simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      clear * - hq
      tauto
    | true =>
      obtain ⟨post,hpost,hcompiled⟩ := compilePublicSlot_armed A b addWidth exitWidth F probeWidth offset P compiled
      simp only [PublicSlot.postProgram,PublicSlot.postInverse,hpost]
      apply compileBorrowedPost_external_support P.front.exitArena P.postArena true F.one F.work0 F.frozen F.work1 F.active
        P.front.exitBank.g.wires F.offset P.postWork probeWidth offset post hcompiled q front.1 _
      intro hq
      have noG : q∉P.front.exitBank.g.wires := by
        intro hg
        apply front.2.1
        simp [WindowBank.rows,hg]
      simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq noMeta
      clear * - hq noMeta noG
      tauto
  refine ⟨front.1,front.2.1,?_,?_⟩
  · simpa only [PublicSlot.program,wires_append,Finset.mem_union,not_or] using
      And.intro front.2.2.1 postFrame.1
  · simpa only [PublicSlot.inverse,wires_append,Finset.mem_union,not_or] using
      And.intro postFrame.2 front.2.2.2

end ECDSAAdd.Arithmetic.Paper935
