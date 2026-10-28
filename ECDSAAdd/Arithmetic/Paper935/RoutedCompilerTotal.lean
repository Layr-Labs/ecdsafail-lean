import ECDSAAdd.Arithmetic.Paper935.RoutedCompiler

namespace ECDSAAdd.Arithmetic.Paper935

theorem routedCandidate_valid (q parity u k active : Wire) (f gv : WindowRow)
    (glow gsign vlow vsign : Wire) (gmid vmid : List Wire)
    (hn : (q::parity::u::k::active::(f.wires++(glow::(gmid++[gsign]))++
      (vlow::(vmid++[vsign]))++gv.wires)).Nodup)
    (fg : f.wires.length=gmid.length+2) (vv : gv.wires.length=vmid.length+2) :
    (RoutedBankLayout.mk q parity u k active f gv glow gmid gsign vlow vmid vsign).Valid := by
  constructor <;>
    simp_all [List.nodup_append',List.disjoint_append_left,List.disjoint_append_right,List.disjoint_comm,eq_comm]

/-- Nonempty paired row views and one ordinary ownership separation check
suffice for compilation; callers need not supply the twelve-field Valid proof. -/
theorem compileRoutedBank_exists (q parity u k active : Wire) (b : WindowBank)
    (hg : b.g.payload≠[]) (hv : b.fv.payload≠[])
    (fg : b.f.payload.length=b.g.payload.length)
    (vv : b.gv.payload.length=b.fv.payload.length)
    (hn : (q::parity::u::k::active::b.rows.flatMap WindowRow.wires).Nodup) :
    ∃ L,compileRoutedBank q parity u k active b=some L := by
  rcases b with ⟨f,⟨gs,gsgn⟩,⟨vs,vsgn⟩,gv⟩
  cases gs with
  | nil => exact (hg rfl).elim
  | cons glow gmid =>
    cases vs with
    | nil => exact (hv rfl).elim
    | cons vlow vmid =>
      have valid := routedCandidate_valid q parity u k active f gv glow gsgn vlow vsgn gmid vmid
        (by simpa [WindowBank.rows,WindowRow.wires,List.append_assoc] using hn)
        (by simpa [WindowRow.wires] using fg)
        (by simpa [WindowRow.wires] using vv)
      refine ⟨RoutedBankLayout.mk q parity u k active f gv glow gmid gsgn vlow vmid vsgn,?_⟩
      simp only [compileRoutedBank,if_pos valid]

end ECDSAAdd.Arithmetic.Paper935
