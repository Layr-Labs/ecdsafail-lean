import ECDSAAdd.Arithmetic.EqualConstant

namespace ECDSAAdd.Arithmetic

/-- 两个相等标志之后，用负控制生成普通加法与倍点标志。 -/
def pointBranchFlags (finite equalX equalNegY generic double : Wire) : Program :=
  [.X equalX, .CCX finite equalX generic, .X equalX,
   .X equalNegY, .CCX equalX equalNegY double, .X equalNegY]

theorem pointBranchFlags_correct (f ex ey g d : Wire)
    (hnd : [f,ex,ey,g,d].Nodup) (s : State) (m : List Bool) :
    run (pointBranchFlags f ex ey g d) m s =
      ⟨s.phase,writeBit (writeBit s.basis g (s.basis g ^^ (s.basis f && !s.basis ex)))
        d (s.basis d ^^ (s.basis ex && !s.basis ey))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,not_or,
    List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_true] at hnd
  simp only [pointBranchFlags,run]
  apply congrArg (State.mk s.phase)
  funext w
  rcases hnd with ⟨⟨hfe,hfy,hfg,hfd⟩,⟨hey,heg,hed⟩,⟨hyg,hyd⟩,hgd⟩
  by_cases hwex : w=ex
  · subst w; simp [writeBit, *, Ne.symm]
  · by_cases hwey : w=ey
    · subst w; simp [writeBit, *, Ne.symm]
    · by_cases hwg : w=g
      · subst w; simp [writeBit, *, Ne.symm]
      · by_cases hwd : w=d
        · subst w; simp [writeBit, *, Ne.symm]
        · simp [writeBit, *, Ne.symm]

theorem pointBranchFlags_counts (f ex ey g d : Wire) :
    toffoliCount (pointBranchFlags f ex ey g d)=2 ∧
    measurementCount (pointBranchFlags f ex ey g d)=0 := by
  simp [pointBranchFlags,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
