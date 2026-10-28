import ECDSAAdd.Arithmetic.Paper935.WindowRows

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical views of the four signed divstep rows. -/
structure WindowBank where
  f : WindowRow
  g : WindowRow
  fv : WindowRow
  gv : WindowRow
  deriving DecidableEq, Repr

def WindowBank.rows (b : WindowBank) : List WindowRow := [b.f,b.g,b.fv,b.gv]

def WindowBank.requests (b : WindowBank) (w : RowWindow) : List (WindowRow × Nat) :=
  [(b.f,w.f),(b.g,w.g),(b.fv,w.fv),(b.gv,w.gv)]

def WindowBank.Encodes (b : WindowBank) (s : BasisState) (z : ECDSAAdd.Divsteps.ZState) : Prop :=
  b.f.value s=z.f ∧ b.g.value s=z.g ∧ b.fv.value s=z.fv ∧ b.gv.value s=z.gv

def WindowBank.Widths (b : WindowBank) (w : RowWindow) : Prop :=
  b.f.payload.length=w.f ∧ b.g.payload.length=w.g ∧
  b.fv.payload.length=w.fv ∧ b.gv.payload.length=w.gv

/-- The public planner's actual output, with the four row names retained. -/
def WindowBank.Planned (b out : WindowBank) (w : RowWindow) (A C : Arena) (p : Program) : Prop :=
  planWindowRows A (b.requests w)=some (C,out.rows,p)

theorem WindowBank.resize_correct (b out : WindowBank) (w : RowWindow)
    (A C : Arena) (p : Program) (h : b.Planned out w A C p)
    (s : State) (m : List Bool) (z : ECDSAAdd.Divsteps.ZState)
    (hr : A.Ready s.basis) (hz : b.Encodes s.basis z) (hf : w.Fits z) :
    rowsOwned C out.rows ∧ C.Ready (run p m s).basis ∧
    out.Encodes (run p m s).basis z ∧ out.Widths w ∧
    (∀ q∈A.live,q∉b.rows.flatMap WindowRow.wires →
      q∈C.live ∧ (run p m s).basis q=s.basis q) := by
  have fits : ∀ r∈b.requests w,PayloadFits r.2 (r.1.value s.basis) := by
    intro r hh
    simp only [requests,List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · simpa only [hz.1] using hf.1
    · simpa only [hz.2.1] using hf.2.1
    · simpa only [hz.2.2.1] using hf.2.2.1
    · simpa only [hz.2.2.2] using hf.2.2.2
  have hc := planWindowRows_correct (b.requests w) A C out.rows p h s m hr fits
  refine ⟨hc.1,hc.2.1,?_,?_,?_⟩
  · have hv := hc.2.2.1
    simpa [rows,requests,Encodes,hz.1,hz.2.1,hz.2.2.1,hz.2.2.2] using hv
  · simpa [rows,requests,Widths] using hc.2.2.2.1
  · simpa [rows,requests] using hc.2.2.2.2

theorem WindowBank.resize_resources (b out : WindowBank) (w : RowWindow)
    (A C : Arena) (p : Program) (h : b.Planned out w A C p) :
    ProperProgram p ∧ toffoliCount p=0 ∧ measurementCount p=0 ∧ wires p⊆arenaWires :=
  planWindowRows_resources (b.requests w) A C out.rows p h

/-- Resizing uses only proper gates, so reversing this emitted stream is
sound even on states outside the numeric success window. -/
theorem WindowBank.resize_roundtrip (b out : WindowBank) (w : RowWindow)
    (A C : Arena) (p : Program) (h : b.Planned out w A C p)
    (s : State) (m n : List Bool) : run p.reverse n (run p m s)=s :=
  run_reverse_proper p (b.resize_resources out w A C p h).1 s m n

end ECDSAAdd.Arithmetic.Paper935
