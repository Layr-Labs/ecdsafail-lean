import ECDSAAdd.Arithmetic.PointCandidateSteps

namespace ECDSAAdd.Arithmetic

theorem CandidateValues.subConstant (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (a o : CandidateField)
    (ha : (L.reg a).length=257) (ho : (L.reg o).length=257)
    (haK : a≠.constant) (hoK : o≠.constant)
    (hn : (L.reg a++L.constant++L.reg o++L.pool).Nodup)
    (hA : v a<p) (hK : v .constant=0) (k : Nat) (hk : k<p) :
    Triple (CandidateValues L v G) (pointSubConstant L (L.reg a) (L.reg o) k)
      (CandidateValues L (Function.update v o (v o ^^^ ((v a+p-k)%p))) G) := by
  have hkl : (L.reg .constant).length=257 := h.words L.constant (by simp [PointAddLayout.words])
  have hkb : k<2^(L.reg .constant).length := by rw [hkl]; exact hk.trans (show p<2^257 by norm_num [p, Nat.pow_succ])
  let v1 := Function.update v CandidateField.constant (v .constant ^^^ k)
  let v2 := Function.update v1 o (v1 o ^^^ ((v1 a+p-v1 .constant)%p))
  have h1 := CandidateValues.constant L hnd v G .constant k hkb
  have h2 := CandidateValues.sub L h hnd v1 G a .constant o ha hkl ho hn
    (by simpa [v1,haK] using hA) (by simpa [v1,hK] using hk)
  have h3 := CandidateValues.constant L hnd v2 G .constant k hkb
  have hf : Function.update v2 CandidateField.constant (v2 .constant ^^^ k)=
      Function.update v o (v o ^^^ ((v a+p-k)%p)) := by
    funext f
    by_cases hfo : f=o
    · subst f; simp [v2,v1,hK,haK,hoK]
    · by_cases hfK : f=.constant
      · subst f; simp [v2,v1,hK,haK,hoK,Ne.symm hoK]
      · simp [v2,v1,hK,haK,hoK,hfo,hfK]
  have hall := (h1.seq h2).seq h3
  change Triple (CandidateValues L v G)
    (xorConstant (L.reg .constant) k++
      fieldSub (poolSub L.poolWire (L.reg a) (L.reg .constant) (L.reg o))++
      xorConstant (L.reg .constant) k) _
  rw [← hf]
  exact hall

theorem CandidateValues.square (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool)
    (hn : (L.slope++L.constant.take 256++L.square++L.pool).Nodup)
    (hS : v .slope<p) (hK : v .constant=0) :
    Triple (CandidateValues L v G) (pointSquare L)
      (CandidateValues L (Function.update v .square (v .square ^^^ ((v .slope*v .slope)%p))) G) := by
  have hs : (L.reg .slope).length=257 := h.words L.slope (by simp [PointAddLayout.words])
  have hk : (L.reg .constant).length=257 := h.words L.constant (by simp [PointAddLayout.words])
  have ho : (L.reg .square).length=257 := h.words L.square (by simp [PointAddLayout.words])
  let v1 := Function.update v CandidateField.constant (v .constant ^^^ v .slope)
  let v2 := Function.update v1 CandidateField.square (v1 .square ^^^ ((v1 .slope*v1 .constant)%p))
  have h1 := CandidateValues.copy L hnd v G .slope .constant (by decide) (hs.trans hk.symm)
  have h2 := CandidateValues.mul L h hnd v1 G .slope .constant .square hs (by omega) ho hn
    (by simpa [v1] using hS)
    (by simpa [v1,hK] using hS.trans (show p<2^256 by norm_num [p]))
  have h3 := CandidateValues.copy L hnd v2 G .slope .constant (by decide) (hs.trans hk.symm)
  have hf : Function.update v2 CandidateField.constant (v2 .constant ^^^ v2 .slope)=
      Function.update v .square (v .square ^^^ ((v .slope*v .slope)%p)) := by
    funext f
    cases f <;> simp [v2,v1,hK]
  have hall := (h1.seq h2).seq h3
  change Triple (CandidateValues L v G)
    (copyRegister none (L.reg .slope) (L.reg .constant)++
      fieldMul (poolMul L.poolWire (L.reg .slope) ((L.reg .constant).take 256) (L.reg .square))++
      copyRegister none (L.reg .slope) (L.reg .constant)) _
  rw [← hf]
  exact hall

end ECDSAAdd.Arithmetic
