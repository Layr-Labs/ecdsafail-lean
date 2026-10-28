import ECDSAAdd.Arithmetic.Paper935.TaggedStep

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem state_eq (a b : State) (hp : a.phase=b.phase)
    (hb : ∀ w,a.basis w=b.basis w) : a=b := by
  have hh : a.basis=b.basis := funext hb
  cases a; cases b; cases hp; cases hh; rfl

/-- A zero branch-enable makes the measured row program the identity. -/
theorem branchRow_idle (q c u k : Wire) (a b : List Wire)
    (hn : (q::c::u::k::(a++b)).Nodup) (hl : a.length=b.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis c=false) : run (branchRow q c u k a b) m s=s := by
  have h := branchRow_run q c u k a b hn hl s m hu hk
  have hv : regValue b (run (branchRow q c u k a b) m s).basis=regValue b s.basis := by
    simpa only [branchWord,hc,Bool.false_eq_true,ite_false] using h.2.2
  apply state_eq _ _ h.1
  intro w
  by_cases hw : w∈b
  · exact (regValue_eq_iff _ _ _).mp hv w hw
  · exact h.2.1 w hw

theorem branchPair_idle (q c u k : Wire) (a b x y : List Wire)
    (hn1 : (q::c::u::k::(a++b)).Nodup) (hn2 : (q::c::u::k::(x++y)).Nodup)
    (hl1 : a.length=b.length) (hl2 : x.length=y.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis c=false) : run (branchPair q c u k a b x y) m s=s := by
  rw [branchPair,run_append,run_take,branchRow_idle q c u k a b hn1 hl1 s m hu hk hc]
  exact branchRow_idle q c u k x y hn2 hl2 s _ hu hk hc

private theorem reg_eq_of_signed (xs : List Wire) (s t : BasisState)
    (h : signedRegValue xs s=signedRegValue xs t) : regValue xs s=regValue xs t := by
  have hh := congrArg (fun x : Int => x%((2^xs.length:Nat):Int)) h
  simp only [signedRegValue,signedDecode_emod] at hh
  have hs := regValue_lt xs s
  have ht := regValue_lt xs t
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hs),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ht)] at hh
  exact_mod_cast hh

theorem doubleSigned_idle (c low sign : Wire) (mid : List Wire)
    (hn : (c::low::(mid++[sign])).Nodup) (s : State) (m : List Bool)
    (hc : s.basis c=false) : run (doubleSigned c low sign mid) m s=s := by
  have h := doubleSigned_correct c low sign mid hn s m (by simp [hc])
  have hv := reg_eq_of_signed (low::(mid++[sign])) _ _
    (show signedRegValue (low::(mid++[sign])) (run (doubleSigned c low sign mid) m s).basis=
      signedRegValue (low::(mid++[sign])) s.basis by simpa only [hc,Bool.false_eq_true,ite_false] using h.2.2)
  apply state_eq _ _ h.1
  intro w
  by_cases hw : w∈low::(mid++[sign])
  · exact (regValue_eq_iff _ _ _).mp hv w hw
  · exact h.2.1 w hw

theorem routeRows_idle (q : Wire) (f g fv gv : List Wire)
    (hl : f.length=g.length) (hv : fv.length=gv.length)
    (hn : (q::((f++fv)++(g++gv))).Nodup)
    (s : State) (m : List Bool) (hq : s.basis q=false) :
    run (routeRows q f g fv gv) m s=s := by
  have h := swapRegisters_correct q (f++fv) (g++gv) (by simp [hl,hv]) hn s m
  simp only [hq,Bool.false_eq_true,ite_false] at h
  apply state_eq _ _ h.1
  intro w
  by_cases ha : w∈f++fv
  · exact (regValue_eq_iff _ _ _).mp h.2.2.1 w ha
  by_cases hb : w∈g++gv
  · exact (regValue_eq_iff _ _ _).mp h.2.2.2 w hb
  exact h.2.1 w ha hb

theorem finishRows_idle (active glow gsign vlow vsign : Wire) (vmid : List Wire)
    (hn : (active::vlow::(vmid++[vsign])).Nodup) (s : State) (m : List Bool)
    (ha : s.basis active=false) (hs : s.basis gsign=false) :
    run (finishRows active glow gsign vlow vsign vmid) m s=s := by
  rw [finishRows,run_append,run_take,doubleSigned_idle active vlow vsign vmid hn s m ha]
  apply state_eq
  · rfl
  · intro w
    simp [skywalkSignedHalf,run,hs,writeBit]

theorem rowStage_idle (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis parity=false) (ha : s.basis active=false) (hs : s.basis gsign=false) :
    run (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv) m s=s := by
  rw [rowStage,run_append,run_take,branchPair_idle q parity u k f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hn1 hn2 (by simpa using hl1) (by simpa using hl2.symm) s m hu hk hc]
  exact finishRows_idle active glow gsign vlow vsign vmid hvn s _ ha hs

theorem activeStep_idle (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis parity=false) (ha : s.basis active=false) (hs : s.basis gsign=false)
    (hq : s.basis q=false) (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0) :
    run (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry) m s=s := by
  have hrow (ms : List Bool) := rowStage_idle q parity u k active glow gsign vlow vsign
    f gmid vmid gv hn1 hn2 hvn hl1 hl2 s ms hu hk hc ha hs
  have hroute := routeRows_idle q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
    (by simpa using hl1) (by simpa using hl2.symm) hr s m hq
  rw [activeStep,run_append,run_take,routedStage,run_append,run_take,hroute,hrow]
  exact counterUpdate_frozen active q zero z carry hcn hzero hcarry s _ ha hq hz0 hcarry0

theorem taggedStep_idle (q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (htn : [zsign,glow,parity,q].Nodup)
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis parity=false) (ha : s.basis active=false) (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=0)
    (hq : s.basis q=false) (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0) :
    run (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s=s := by
  have hglow : s.basis glow=false := (signedRegValue_even_iff glow (gmid++[gsign]) s.basis).mp (by rw [hg]; rfl)
  have hs : s.basis gsign=false := by
    by_contra h
    have hh := (signedRegValue_neg_iff (glow::gmid) gsign s.basis).mpr (Bool.eq_true_of_not_eq_false h)
    simp only [List.cons_append] at hh
    rw [hg] at hh
    omega
  have ht : run (branchTags zsign glow parity q) m s=s := by
    rw [branchTags_correct zsign glow parity q htn s m hc hq]
    apply state_eq
    · rfl
    · intro w
      by_cases hwq : w=q
      · subst w; simp [writeBit,hglow,hq]
      by_cases hwp : w=parity
      · subst w; simp [writeBit,hglow,hc,hwq]
      simp [writeBit,hwq,hwp]
  rw [taggedStep,run_append,run_take,ht]
  exact activeStep_idle q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry
    hn1 hn2 hvn hl1 hl2 hr hcn hzero hcarry s _ hu hk hc ha hs hq hz0 hcarry0

/-- Relabelling a zero g row does not change its represented value. -/
theorem halfView_zero (glow gsign : Wire) (gmid : List Wire) (s : BasisState)
    (hg : signedRegValue (glow::(gmid++[gsign])) s=0) :
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) s=0 := by
  have he := congrArg (fun x : Int => x%((2^(glow::(gmid++[gsign])).length:Nat):Int)) hg
  simp only [signedRegValue,signedDecode_emod,Int.zero_emod] at he
  have hb := regValue_lt (glow::(gmid++[gsign])) s
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb)] at he
  have hz : regValue (glow::(gmid++[gsign])) s=0 := by exact_mod_cast he
  have hv : regValue (skywalkHalfView glow (gmid++[gsign])) s=0 := by
    apply (regValue_zero _ s).mpr
    intro w hw
    apply (regValue_zero _ s).mp hz w
    simp only [skywalkHalfView,List.mem_append,List.mem_cons] at hw ⊢
    tauto
  unfold signedRegValue
  rw [hv]
  simp [signedDecode]

end ECDSAAdd.Arithmetic.Paper935
