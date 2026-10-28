import ECDSAAdd.Arithmetic.Paper935.SlotFrontLocality

namespace ECDSAAdd.Arithmetic.Paper935

/-- Borrowed post work cannot touch a pre-owned bit outside all post inputs. -/
theorem compileBorrowedPost_external (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (compiled : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (q : Wire) (owned : q∈A.live) (away : q∉[one,zf,frozen,fire,active]++inputs++record)
    (s : State) (m : List Bool) : (run P.program m s).basis q=s.basis q := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P compiled
  have borrow := A.borrowMany_contract D _ work pair.1
  have reserved := (A.reserve_success work.toFinset).mp ⟨D,borrow.2.2⟩
  have noWork : q∉work := fun hq => Finset.disjoint_left.mp reserved.2 owned (List.mem_toFinset.mpr hq)
  apply run_preserves_outside
  intro hq
  have hm := compilePost_ports armed one zf frozen fire active inputs record work width offset P pair.2
    (P.support.1 hq)
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm away
  clear * - hm away noWork
  tauto

/-- The entire actual public slot preserves every pre-owned external bit on
all states and tapes; in particular, it cannot alter the persistent history. -/
theorem compilePublicSlot_external (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (compiled : compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P)
    (counterNonempty : F.counter≠[]) (coefficientNonempty : P.front.exitBank.fv.payload≠[])
    (q : Wire) (owned : q∈A.live) (noMeta : q∉F.wires) (noRows : q∉b.rows.flatMap WindowRow.wires) :
    q∈P.front.exitArena.live ∧ q∉P.front.exitBank.rows.flatMap WindowRow.wires ∧
      ∀ s m,(run (P.program F) m s).basis q=s.basis q := by
  have frontCompiled := compilePublicSlot_front _ _ _ _ _ _ _ _ _ compiled
  have front := (compileSlotFront_contract A b addWidth exitWidth F P.front frontCompiled).external_frame
    P.front A b addWidth exitWidth F counterNonempty coefficientNonempty q owned noMeta noRows
  have postFrame : ∀ s m,(run (P.postProgram F) m s).basis q=s.basis q := by
    intro s m
    cases armed with
    | false =>
      have post := (compilePublicSlot_unarmed A b addWidth exitWidth F probeWidth offset P compiled).1
      rw [PublicSlot.postProgram,post]
      apply run_preserves_outside
      intro hq
      apply noMeta
      simp only [retireActivity,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
        or_false] at hq
      simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      clear * - hq
      tauto
    | true =>
      obtain ⟨post,hpost,hcompiled⟩ := compilePublicSlot_armed A b addWidth exitWidth F probeWidth offset P compiled
      rw [PublicSlot.postProgram,hpost]
      apply compileBorrowedPost_external P.front.exitArena P.postArena true F.one F.work0 F.frozen F.work1 F.active
        P.front.exitBank.g.wires F.offset P.postWork probeWidth offset post hcompiled q front.1 _ s m
      intro hq
      have noG : q∉P.front.exitBank.g.wires := by
        intro hg
        apply front.2.1
        simp [WindowBank.rows,hg]
      simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq noMeta
      clear * - hq noMeta noG
      tauto
  refine ⟨front.1,front.2.1,?_⟩
  intro s m
  rw [PublicSlot.program,run_append,run_take,postFrame,front.2.2]

end ECDSAAdd.Arithmetic.Paper935
