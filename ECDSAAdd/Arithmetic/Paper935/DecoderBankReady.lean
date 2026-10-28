import ECDSAAdd.Arithmetic.Paper935.DepthArenaReady
import ECDSAAdd.Arithmetic.Paper935.WindowPaddingSupport
import ECDSAAdd.Arithmetic.Paper935.DecoderWindow

namespace ECDSAAdd.Arithmetic.Paper935

/-- Enough physical payload bits for every depth two through six. Other rows
retain their widths, so no unnecessary data bank is widened. -/
def WindowBank.decoderWidth (b : WindowBank) : RowWindow :=
  ⟨max 6 b.f.payload.length,b.g.payload.length,max 12 b.fv.payload.length,b.gv.payload.length⟩

theorem WindowBank.decoderWidth_fits (b : WindowBank) (s : BasisState)
    (st : ECDSAAdd.Divsteps.ZState) (he : b.Encodes s st) : b.decoderWidth.Fits st := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [←he.1]
    exact (b.f.value_fits s).mono (Nat.le_max_right _ _)
  · rw [←he.2.1]; exact b.g.value_fits s
  · rw [←he.2.2.1]
    exact (b.fv.value_fits s).mono (Nat.le_max_right _ _)
  · rw [←he.2.2.2]; exact b.gv.value_fits s

/-- Derive actual decoder availability after emitted physical padding from
an encoded slot output and the clean shared arena. No decoder-correctness
oracle or pre-existing `Available` premise is used. -/
theorem DepthLayout.available_after_padding (L : DepthLayout) (valid : L.Static)
    (b out : WindowBank) (A C : Arena) (padding : Program)
    (plan : b.Planned out b.decoderWidth A C padding)
    (u : PinState) (tmin index : Nat) (z : List Wire) (s : State) (m : List Bool)
    (ready : A.Ready s.basis) (rows : b.Encodes s.basis (pinStep tmin index u).rows)
    (counter : signedRegValue z s.basis=(pinStep tmin index u).rows.z)
    (frozen : s.basis L.frozen.input=(pinStep tmin index u).frozen)
    (one : s.basis L.one=true)
    (retained : ∀ q∈L.one::L.frozen.input::z,q∈A.live ∧ q∉b.rows.flatMap WindowRow.wires)
    (free : L.cleanWires.toFinset⊆arenaWires\C.live)
    (zview : L.zlo++[L.sign]=z)
    (fview : L.flow::((L.address::L.fdata)++L.ftail)=out.f.wires)
    (vview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=out.fv.wires) :
    L.Available u.rows (ECDSAAdd.run padding m s) := by
  have fit := b.decoderWidth_fits s.basis _ rows
  have result := b.resize_correct out b.decoderWidth A C padding plan s m _ ready rows fit
  have keep (q : Wire) (hq : q∈L.one::L.frozen.input::z) :
      (ECDSAAdd.run padding m s).basis q=s.basis q := by
    obtain ⟨owned,away⟩ := retained q hq
    exact (result.2.2.2.2 q owned away).2
  apply L.available_of_pin valid C out z u tmin index (ECDSAAdd.run padding m s)
    result.2.1 free ((keep L.one (by simp)).trans one) zview fview vview result.2.2.1
  · unfold signedRegValue
    rw [regValue_congr z (ECDSAAdd.run padding m s).basis s.basis (fun q hq => keep q (by simp [hq]))]
    exact counter
  · exact (keep L.frozen.input (by simp)).trans frozen

end ECDSAAdd.Arithmetic.Paper935
