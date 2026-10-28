import ECDSAAdd.Math.Divsteps.Recovery
import ECDSAAdd.Math.Divsteps.SmallDecoders

namespace ECDSAAdd.Divsteps

/-- Bridge depth three to the finite decoder formula. Residue witnesses
explicitly describe the updated integer row and divided coefficient row. -/
theorem depth3_branch (p : Int) (s : ZState) (h : Inv p s)
    (hp : p % 2 = 1) (hz : s.z < 0)
    (hd : padicValInt 2 (zStep s).fv = 3)
    (f q : Fin 4) (hp8 : (p : ZMod 8) = 7)
    (hf : ((zStep s).f : ZMod 8) = (SmallDecoders.oddValue f : ZMod 8))
    (hq : (((zStep s).fv / 8 : Int) : ZMod 8) = (SmallDecoders.oddValue q : ZMod 8)) :
    decide (bbit s = 1) = SmallDecoders.decode3
      (SmallDecoders.oddValue f) (SmallDecoders.oddValue q) := by
  have law := ladder_det h hp hz hd.symm rfl
  norm_num only [Nat.reducePow, Nat.reduceSub, Int.reducePow] at law
  push_cast at law
  rw [hp8, hf, hq] at law
  rw [law, ← SmallDecoders.depth3 f q]
  simp only [bitk, SmallDecoders.bit]
  norm_num only [Nat.reducePow, Int.reducePow]
  push_cast
  rw [decide_eq_decide]
  omega

/-- Bridge depth four to the finite decoder formula. Residue witnesses
explicitly describe the updated integer row and divided coefficient row. -/
theorem depth4_branch (p : Int) (s : ZState) (h : Inv p s)
    (hp : p % 2 = 1) (hz : s.z < 0)
    (hd : padicValInt 2 (zStep s).fv = 4)
    (f q : Fin 8) (hp16 : (p : ZMod 16) = 15)
    (hf : ((zStep s).f : ZMod 16) = (SmallDecoders.oddValue f : ZMod 16))
    (hq : (((zStep s).fv / 16 : Int) : ZMod 16) = (SmallDecoders.oddValue q : ZMod 16)) :
    decide (bbit s = 1) = SmallDecoders.decode4
      (SmallDecoders.oddValue f) (SmallDecoders.oddValue q) := by
  have law := ladder_det h hp hz hd.symm rfl
  norm_num only [Nat.reducePow, Nat.reduceSub, Int.reducePow] at law
  push_cast at law
  rw [hp16, hf, hq] at law
  rw [law, ← SmallDecoders.depth4 f q]
  simp only [bitk, SmallDecoders.bit]
  norm_num only [Nat.reducePow, Int.reducePow]
  push_cast
  rw [decide_eq_decide]
  omega

end ECDSAAdd.Divsteps
