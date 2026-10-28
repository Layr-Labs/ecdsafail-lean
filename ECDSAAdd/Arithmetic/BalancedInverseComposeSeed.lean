import ECDSAAdd.Arithmetic.BalancedInverseComposeWord

set_option maxRecDepth 4096
set_option exponentiation.threshold 512
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Only the seed's four CX gates are reversed. Their exact correlations
clear the three seeded scalar sites without measurements. -/
theorem unseed_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (ho : s.basis L.one=s.basis L.rmsb)
    (hp : s.basis L.parity=(s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0)) :
    run (seedViews L).reverse m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.parity false) L.one false) L.sourceGuard false⟩ := by
  have nd := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  apply State.extensionality
  · simp [seedViews,run]
  · funext q
    by_cases hqg : q=L.sourceGuard <;> by_cases hqo : q=L.one <;> by_cases hqp : q=L.parity <;>
      simp_all [seedViews,run,writeBit,Function.update]

/-- The raw arithmetic postcondition supplies the unseed sign and parity
correlations directly, without a classical circuit oracle. -/
theorem unseed_correlations (L : Layout) (hw : L.Widths)
    (B : Bool) (X Y : Int) (hc : Centered X) (s : State)
    (hx : signedRegValue (rawTarget L) s.basis=X)
    (hy : signedRegValue L.y s.basis=Y)
    (_hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (hp : s.basis L.parity=originalParity (rawSum B X Y)) :
    s.basis L.one=s.basis L.rmsb ∧
    s.basis L.parity=(s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0) := by
  have rlen : L.r.length=256 := (BalancedCleanup.widths L.toLayout hw).2.1
  have lowlen : (L.r0::L.rtail).length=255 := by simp [hw.1]
  have high := regValue_highBit (L.r0::L.rtail) L.rmsb s.basis
  have hraw := hx
  rw [rawTarget,signedRegValue_msb,regValue_append,rlen] at hraw
  have bits : regValue [L.one] s.basis=(s.basis L.one).toNat := by
    cases h : s.basis L.one <;> simp [regValue,h]
  rw [bits] at hraw
  have rshape : (L.r0::L.rtail)++[L.rmsb]=L.r := by
    simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  rw [lowlen,rshape] at high
  have same : s.basis L.one=s.basis L.rmsb := by
    have constant := BalancedField.constants
    unfold Centered at hc
    cases ho : s.basis L.one <;> cases hm : s.basis L.rmsb
    all_goals try rfl
    all_goals simp [ho,hm] at hraw high
    all_goals omega
  constructor
  · exact same
  · have xpar : s.basis L.r0=originalParity X := by
      apply word_parity L.r0 (L.rtail++[L.rmsb,L.one]) s.basis X
      simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using hx
    cases hylo : L.ylow with
    | nil => have h := hw.2.1; simp [hylo] at h
    | cons a as =>
      have ypar : s.basis a=originalParity Y := by
        apply word_parity a (as++[L.ymsb]) s.basis Y
        simpa [BalancedCleanup.Layout.y,hylo] using hy
      rw [hp,raw_parity,xpar]
      simp [hylo,ypar]

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.unseed_run
