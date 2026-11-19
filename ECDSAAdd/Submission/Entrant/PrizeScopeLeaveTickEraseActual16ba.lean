import ECDSAAdd.Framework.Cost

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveReadoutFrame

def destination : Instr → Wire
  | .X q | .CX _ q | .CCX _ _ q | .measureX q _ _ => q

theorem preserved (p : Program) (s : State) (m : List Bool) (q : Wire)
    (safe : q∉p.map destination) : (run p m s).basis q=s.basis q := by
  induction p generalizing s m with
  | nil => rfl
  | cons i p ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at safe
    obtain ⟨ne,unwritten⟩:=safe
    cases i <;> simp only [run] <;> rw [ih _ _ unwritten] <;>
      simp only [destination] at ne <;> simp [measureAndCorrect,writeBit,ne]

end ECDSAAdd.Entrant.StairPacket.LeaveReadoutFrame


end
