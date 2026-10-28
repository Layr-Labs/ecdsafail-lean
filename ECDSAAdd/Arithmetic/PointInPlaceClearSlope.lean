import ECDSAAdd.Arithmetic.PointInPlaceConditions

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 第二次除法与零除数例外共同清λ；e/q均由未变的x重算清除。 -/
theorem pointInPlaceClearSlope_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y A k : Fp) (G : Bool) (hY : G=true → Y=A*X)
    (hk : G=true → X=0 → A=k) (hA : G=false → A=0) :
    Triple (PointInPlaceValues L X Y A G false false) (pointInPlaceClearSlope L k)
      (PointInPlaceValues L X Y 0 G false false) := by
  let E := G && decide (X=0)
  let Q := G ^^ E
  let A' := if Q then A-Y/X else A
  have hX : Q=true → X≠0 := by
    intro hq hx
    simp [Q,E,hx] at hq
  have hclear : A'=(if E then k else 0) := by
    cases hg : G
    · simp [A',Q,E,hg,hA hg]
    · by_cases hx : X=0
      · simp [A',Q,E,hg,hx,hk hg hx]
      · have hd : Y/X=A := by rw [hY hg]; exact mul_div_cancel_right₀ A hx
        simp [A',Q,E,hg,hx,hd]
  have h1 := pointStep_zero L hw hn X Y A G false false
  have h2 := pointStep_quotient L hw hn X Y A G E false
  simp only [Bool.false_xor] at h1 h2
  have h3 := pointStep_divideSub L hw hn X Y A G E Q hX
  have h4 := pointStep_clearSlope L hw hn X Y A' G E Q k hclear
  have h5 := pointStep_quotient L hw hn X Y 0 G E Q
  have hQ : ((Q ^^ G) ^^ E)=false := by
    dsimp only [Q]
    generalize E=e
    cases G <;> cases e <;> rfl
  rw [hQ] at h5
  have h6 := pointStep_zero L hw hn X Y 0 G E false
  have hE : (E ^^ (G && decide (X=0)))=false := by simp [E]
  rw [hE] at h6
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [pointInPlaceClearSlope,List.append_assoc] using h

end ECDSAAdd.Arithmetic
