import ECDSAAdd.Arithmetic.Paper935.SlotFrontCompiler
import ECDSAAdd.Arithmetic.Paper935.PostCompilerSupport

namespace ECDSAAdd.Arithmetic.Paper935

structure PublicSlot where
  front : SlotFront
  post : Option WindowPostLayout
  postArena : Arena
  postWork : List Wire

/-- The unarmed path allocates no probe/comparison work. The armed path
borrows it only after row shrinkage and counter scratch return. -/
def compilePublicSlot (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) : Option PublicSlot := do
  let front ← compileSlotFront A b addWidth exitWidth F
  if armed then
    let (D,work,P) ← compileBorrowedPost front.exitArena true F.one F.work0 F.frozen F.work1 F.active
      front.exitBank.g.wires F.offset probeWidth offset
    pure ⟨front,some P,D,work⟩
  else pure ⟨front,none,front.exitArena,[]⟩

def PublicSlot.postProgram (P : PublicSlot) (F : SlotRegisters) : Program :=
  match P.post with
  | some post => post.program
  | none => retireActivity F.frozen F.work1 F.active

def PublicSlot.postInverse (P : PublicSlot) (F : SlotRegisters) : Program :=
  match P.post with
  | some post => post.inverse
  | none => (retireActivity F.frozen F.work1 F.active).reverse

def PublicSlot.program (P : PublicSlot) (F : SlotRegisters) : Program :=
  P.front.program F++P.postProgram F

def PublicSlot.inverse (P : PublicSlot) (F : SlotRegisters) : Program :=
  P.postInverse F++P.front.inverse F

theorem compilePublicSlot_front (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (armed : Bool) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compilePublicSlot A b addWidth exitWidth F armed probeWidth offset=some P) :
    compileSlotFront A b addWidth exitWidth F=some P.front := by
  unfold compilePublicSlot at h
  obtain ⟨front,hf,h⟩ := Option.bind_eq_some_iff.mp h
  cases armed with
  | false => cases h; exact hf
  | true =>
    obtain ⟨⟨D,work,post⟩,_,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact hf

theorem compilePublicSlot_unarmed (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compilePublicSlot A b addWidth exitWidth F false probeWidth offset=some P) :
    P.post=none ∧ P.postArena=P.front.exitArena ∧ P.postWork=[] ∧
    P.postProgram F=retireActivity F.frozen F.work1 F.active := by
  unfold compilePublicSlot at h
  obtain ⟨front,_,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem compilePublicSlot_armed (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth offset : Nat) (P : PublicSlot)
    (h : compilePublicSlot A b addWidth exitWidth F true probeWidth offset=some P) :
    ∃ post,P.post=some post ∧
      compileBorrowedPost P.front.exitArena true F.one F.work0 F.frozen F.work1 F.active
        P.front.exitBank.g.wires F.offset probeWidth offset=some (P.postArena,P.postWork,post) := by
  unfold compilePublicSlot at h
  obtain ⟨front,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨D,work,post⟩,hp,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨post,rfl,hp⟩

/-- The actual unarmed stream is three proper gates and needs no borrowed
workspace, independently of row widths or successful arithmetic values. -/
theorem unarmedPost_resources (F : SlotRegisters)
    (hf : F.frozen≠F.active) (hw : F.work1≠F.active) :
    ProperProgram (retireActivity F.frozen F.work1 F.active) ∧
    measurementCount (retireActivity F.frozen F.work1 F.active)=0 ∧
    wires (retireActivity F.frozen F.work1 F.active)⊆[F.frozen,F.work1,F.active].toFinset := by
  constructor
  · simp [retireActivity,ProperProgram,ProperGate,hf,hw]
  · constructor
    · rfl
    · intro q hq
      simpa [retireActivity,wires,Instr.wires,or_assoc,or_left_comm,or_comm] using hq

end ECDSAAdd.Arithmetic.Paper935
