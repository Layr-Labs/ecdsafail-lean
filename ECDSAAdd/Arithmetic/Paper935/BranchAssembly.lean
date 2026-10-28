import ECDSAAdd.Arithmetic.Paper935.DepthResidue

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Finite depths 2–6 and the stored cutoff, including coefficient zero,
partition precisely the nonswap class. -/
theorem branchDepth_partition (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1) :
    (decide (2≤padicValInt 2 (zStep st).fv ∧ padicValInt 2 (zStep st).fv≤6) ^^
      decide ((2:Int)^7 ∣ (zStep st).fv)) = !decide (0≤st.z ∧ st.g%2=1) := by
  simp only [historyCutoff_valuation]
  have hval := (sigma_class hi hp).2.1
  have hzero : (zStep st).fv=0 → padicValInt 2 (zStep st).fv=0 := by
    intro h; simp [h,padicValInt]
  by_cases hs : 0≤st.z ∧ st.g%2=1
  · have hd := hval.mp hs
    have hn : (zStep st).fv≠0 := by intro hz; have := hzero hz; omega
    simp [hn,hd,hs]
  · have h4 := (sigma_class hi hp).2.2 hs
    have hlo : (zStep st).fv=0 ∨ 2≤padicValInt 2 (zStep st).fv :=
      (historyCutoff_valuation _ 2).mp (by norm_num; exact h4)
    by_cases hz : (zStep st).fv=0
    · simp [hz,padicValInt,hs]
    · have hd := hlo.resolve_left hz
      by_cases hh : padicValInt 2 (zStep st).fv≤6
      · have h7 : ¬7≤padicValInt 2 (zStep st).fv := by omega
        simp [hz,hs,hd,hh,h7]
      · have h7 : 7≤padicValInt 2 (zStep st).fv := by omega
        simp [hz,hs,hh,h7]

/-- The original branch is assembled from the negative-counter decoder,
swap, and a newly fired freeze. The nonzero premise excludes a missed earlier
termination; it is an explicit success condition, not a consequence of layout. -/
theorem branchAssembly_value (st : ZState) (hf : st.f%2=1)
    (frozen armed : Bool) (hfg : frozen=true → st.g=0)
    (hfirst : frozen=false → armed=true → (zStep st).g=0 → st.g≠0) :
    let fire := !frozen && armed && decide ((zStep st).g=0)
    let sigma := !frozen && decide (0≤st.z ∧ st.g%2=1)
    let pred := !(frozen || fire) && !sigma && decide ((zStep st).z≤0) && decide (bbit st=1)
    (pred ^^ sigma ^^ (fire && !sigma)) = decide (bbit st=1) := by
  dsimp only
  cases hz : frozen with
  | true =>
    have hg := hfg hz
    simp [bbit,hg]
  | false =>
    by_cases hfire : armed=true ∧ (zStep st).g=0
    · have hb := bbit_of_freeze hf (hfirst hz hfire.1 hfire.2) hfire.2
      by_cases hs : 0≤st.z ∧ st.g%2=1 <;> simp [hfire.1,hfire.2,hb,hs]
    · have hfire0 : (armed && decide ((zStep st).g=0))=false := by
        cases armed <;> simp_all
      by_cases hs : 0≤st.z ∧ st.g%2=1
      · simp [hs,hfire0,bbit_of_swap hf hs]
      · by_cases hp : (zStep st).z≤0
        · simp [hfire0,hs,hp]
        · have hb := bbit_of_ramp hs (by omega : 1≤(zStep st).z)
          simp [hfire0,hs,hp,hb]

end ECDSAAdd.Arithmetic.Paper935
