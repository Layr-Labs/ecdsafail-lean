import ECDSAAdd.Arithmetic.Paper935.BorrowedDepth

namespace ECDSAAdd.Arithmetic.Paper935

/-- Borrowing changes ownership, not state. The checked decoder is ready
from the pre-borrow arena invariant and the actual signed row views. -/
theorem compileBorrowedDepth_available (A D : Arena) (one frozen output : Wire)
    (b : WindowBank) (z work : List Wire) (depth : Nat) (L : DepthLayout)
    (h : compileBorrowedDepth A one frozen output z b.f.wires b.fv.wires depth=some (D,work,L))
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (ready : A.Ready s.basis)
    (hone : s.basis one=true)
    (rows : s.basis frozen=false → b.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis frozen=false → signedRegValue z s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    L.Available st s := by
  have pair := compileBorrowedDepth_contract A D one frozen output z b.f.wires b.fv.wires work depth L h
  have hc := compileDepth_contract one frozen output z b.f.wires b.fv.wires work depth L pair.2
  have ids := compileDepth_identity one frozen output z b.f.wires b.fv.wires work depth L pair.2
  have borrow := A.borrowMany_contract D 11 work pair.1
  have reserve := (A.reserve_success work.toFinset).mp ⟨D,borrow.2.2⟩
  have free : L.cleanWires.toFinset⊆arenaWires\A.live := by
    intro q hq
    have hw := compileDepth_clean_subset one frozen output z b.f.wires b.fv.wires work depth L pair.2 hq
    exact Finset.mem_sdiff.mpr ⟨reserve.1 hw,fun hl => Finset.disjoint_left.mp reserve.2 hl hw⟩
  apply L.available_of_bank hc.1 A b z st s ready free
  · rw [ids.1]; exact hone
  · rw [← hc.1.hzview]; exact hc.2.2.1
  · exact hc.2.2.2.1
  · exact hc.2.2.2.2.1
  · rw [ids.2.1]; exact rows
  · rw [ids.2.1]; exact counter

end ECDSAAdd.Arithmetic.Paper935
