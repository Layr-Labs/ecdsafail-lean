import ECDSAAdd.Arithmetic.Paper935.HmrFlagChain

namespace ECDSAAdd.Arithmetic.Paper935

/-- Literal three-stage anchor split from engine.py:1466–1483. -/
def hmrFlags (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire) : Program :=
  hmrFlagCell c3 b2 j2 a1 ++ hmrFlagCell a1 b3 j3 a2 ++ hmrFlagCell a2 b4 j4 j5p

def hmrFlagsRelease (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire) : Program :=
  hmrFlagRelease a2 b4 j4 j5p ++ hmrFlagRelease a1 b3 j3 a2 ++ hmrFlagRelease c3 b2 j2 a1

theorem hmrFlags_run (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire)
    (distinct : [c3,b2,b3,b4,j2,a1,j3,a2,j4,j5p].Nodup) (s : State) (m : List Bool)
    (clean : ∀q∈[j2,a1,j3,a2,j4,j5p],s.basis q=false) :
    run (hmrFlags c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p) m s=
    ⟨s.phase,writeBit (writeBit (writeBit (writeBit (writeBit (writeBit s.basis
      j2 (s.basis c3 && s.basis b2))
      a1 (s.basis c3 && !s.basis b2))
      j3 (s.basis c3 && !s.basis b2 && s.basis b3))
      a2 (s.basis c3 && !s.basis b2 && !s.basis b3))
      j4 (s.basis c3 && !s.basis b2 && !s.basis b3 && s.basis b4))
      j5p (s.basis c3 && !s.basis b2 && !s.basis b3 && !s.basis b4)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9⟩,⟨h5_6,h5_7,h5_8,h5_9⟩,⟨h6_7,h6_8,h6_9⟩,⟨h7_8,h7_9⟩,h8_9⟩ := distinct
  have hr0_1 := Ne.symm h0_1
  have hr0_2 := Ne.symm h0_2
  have hr0_3 := Ne.symm h0_3
  have hr0_4 := Ne.symm h0_4
  have hr0_5 := Ne.symm h0_5
  have hr0_6 := Ne.symm h0_6
  have hr0_7 := Ne.symm h0_7
  have hr0_8 := Ne.symm h0_8
  have hr0_9 := Ne.symm h0_9
  have hr1_2 := Ne.symm h1_2
  have hr1_3 := Ne.symm h1_3
  have hr1_4 := Ne.symm h1_4
  have hr1_5 := Ne.symm h1_5
  have hr1_6 := Ne.symm h1_6
  have hr1_7 := Ne.symm h1_7
  have hr1_8 := Ne.symm h1_8
  have hr1_9 := Ne.symm h1_9
  have hr2_3 := Ne.symm h2_3
  have hr2_4 := Ne.symm h2_4
  have hr2_5 := Ne.symm h2_5
  have hr2_6 := Ne.symm h2_6
  have hr2_7 := Ne.symm h2_7
  have hr2_8 := Ne.symm h2_8
  have hr2_9 := Ne.symm h2_9
  have hr3_4 := Ne.symm h3_4
  have hr3_5 := Ne.symm h3_5
  have hr3_6 := Ne.symm h3_6
  have hr3_7 := Ne.symm h3_7
  have hr3_8 := Ne.symm h3_8
  have hr3_9 := Ne.symm h3_9
  have hr4_5 := Ne.symm h4_5
  have hr4_6 := Ne.symm h4_6
  have hr4_7 := Ne.symm h4_7
  have hr4_8 := Ne.symm h4_8
  have hr4_9 := Ne.symm h4_9
  have hr5_6 := Ne.symm h5_6
  have hr5_7 := Ne.symm h5_7
  have hr5_8 := Ne.symm h5_8
  have hr5_9 := Ne.symm h5_9
  have hr6_7 := Ne.symm h6_7
  have hr6_8 := Ne.symm h6_8
  have hr6_9 := Ne.symm h6_9
  have hr7_8 := Ne.symm h7_8
  have hr7_9 := Ne.symm h7_9
  have hr8_9 := Ne.symm h8_9
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at clean
  cases h0 : s.basis c3 <;> cases h1 : s.basis b2 <;> cases h2 : s.basis b3 <;> cases h3 : s.basis b4 <;>
    simp_all [hmrFlags,hmrFlagCell,run,writeBit,Function.update]


def hmrFlagStages (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire) : List HmrFlagStage :=
  [⟨c3,b2,j2,a1⟩,⟨a1,b3,j3,a2⟩,⟨a2,b4,j4,j5p⟩]

theorem hmrFlags_ready (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire)
    (distinct : [c3,b2,b3,b4,j2,a1,j3,a2,j4,j5p].Nodup) (s : BasisState)
    (clean : ∀q∈[j2,a1,j3,a2,j4,j5p],s q=false) :
    HmrFlagReady (hmrFlagStages c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p) s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at distinct
  obtain ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9⟩,⟨h5_6,h5_7,h5_8,h5_9⟩,⟨h6_7,h6_8,h6_9⟩,⟨h7_8,h7_9⟩,h8_9⟩ := distinct
  have hr0_1 := Ne.symm h0_1
  have hr0_2 := Ne.symm h0_2
  have hr0_3 := Ne.symm h0_3
  have hr0_4 := Ne.symm h0_4
  have hr0_5 := Ne.symm h0_5
  have hr0_6 := Ne.symm h0_6
  have hr0_7 := Ne.symm h0_7
  have hr0_8 := Ne.symm h0_8
  have hr0_9 := Ne.symm h0_9
  have hr1_2 := Ne.symm h1_2
  have hr1_3 := Ne.symm h1_3
  have hr1_4 := Ne.symm h1_4
  have hr1_5 := Ne.symm h1_5
  have hr1_6 := Ne.symm h1_6
  have hr1_7 := Ne.symm h1_7
  have hr1_8 := Ne.symm h1_8
  have hr1_9 := Ne.symm h1_9
  have hr2_3 := Ne.symm h2_3
  have hr2_4 := Ne.symm h2_4
  have hr2_5 := Ne.symm h2_5
  have hr2_6 := Ne.symm h2_6
  have hr2_7 := Ne.symm h2_7
  have hr2_8 := Ne.symm h2_8
  have hr2_9 := Ne.symm h2_9
  have hr3_4 := Ne.symm h3_4
  have hr3_5 := Ne.symm h3_5
  have hr3_6 := Ne.symm h3_6
  have hr3_7 := Ne.symm h3_7
  have hr3_8 := Ne.symm h3_8
  have hr3_9 := Ne.symm h3_9
  have hr4_5 := Ne.symm h4_5
  have hr4_6 := Ne.symm h4_6
  have hr4_7 := Ne.symm h4_7
  have hr4_8 := Ne.symm h4_8
  have hr4_9 := Ne.symm h4_9
  have hr5_6 := Ne.symm h5_6
  have hr5_7 := Ne.symm h5_7
  have hr5_8 := Ne.symm h5_8
  have hr5_9 := Ne.symm h5_9
  have hr6_7 := Ne.symm h6_7
  have hr6_8 := Ne.symm h6_8
  have hr6_9 := Ne.symm h6_9
  have hr7_8 := Ne.symm h7_8
  have hr7_9 := Ne.symm h7_9
  have hr8_9 := Ne.symm h8_9
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at clean
  simp_all [hmrFlagStages,HmrFlagReady,HmrFlagStage.advance,writeBit,Function.update]

theorem hmrFlags_release (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire)
    (distinct : [c3,b2,b3,b4,j2,a1,j3,a2,j4,j5p].Nodup) (s : State) (m : List Bool)
    (clean : ∀q∈[j2,a1,j3,a2,j4,j5p],s.basis q=false) :
    run (hmrFlags c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p ++
      hmrFlagsRelease c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p) m s=s := by
  have ready := hmrFlags_ready c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p distinct s.basis clean
  have h := hmrFlagSweep_release (hmrFlagStages c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p) s m ready
  simpa [hmrFlagStages,hmrFlagSweep,hmrFlagUnsweep,hmrFlags,hmrFlagsRelease,List.append_assoc] using h


/-- The source anchor split uses three temporary ANDs; their release consumes
three measurement outcomes, with no additional Toffoli gates. -/
theorem hmrFlags_counts (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire) :
    toffoliCount (hmrFlags c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p ++
      hmrFlagsRelease c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p)=3 ∧
    measurementCount (hmrFlags c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p ++
      hmrFlagsRelease c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p)=3 := ⟨rfl,rfl⟩

theorem hmrFlags_j5p (c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p : Wire)
    (distinct : [c3,b2,b3,b4,j2,a1,j3,a2,j4,j5p].Nodup) (s : State) (m : List Bool)
    (clean : ∀q∈[j2,a1,j3,a2,j4,j5p],s.basis q=false) :
    (run (hmrFlags c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p) m s).basis j5p=
      (s.basis c3 && !s.basis b2 && !s.basis b3 && !s.basis b4) := by
  rw [hmrFlags_run c3 b2 b3 b4 j2 a1 j3 a2 j4 j5p distinct s m clean]
  simp [writeBit]

end ECDSAAdd.Arithmetic.Paper935
