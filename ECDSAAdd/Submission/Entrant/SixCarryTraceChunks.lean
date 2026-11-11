import ECDSAAdd.Submission.Entrant.SixCarryChunkViews
namespace ECDSAAdd.Entrant.SixCarryTraceChunks
open ECDSAAdd SixCarryFrame
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem noWrite_shift (p pre tail : Program) (start a b q : Nat)
 (hs : p=pre++tail) (hl : pre.length=start) :
 noWriteBetween p (start+a) (start+b) q=noWriteBetween tail a b q := by
 unfold noWriteBetween
 rw [hs,List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,hl]
 simp only [Nat.add_sub_cancel_left,Nat.add_sub_add_left]
end ECDSAAdd.Entrant.SixCarryTraceChunks
