import ECDSAAdd.Arithmetic.CuccaroNormalizedMod

set_option maxHeartbeats 8000000

namespace ECDSAAdd.Arithmetic

structure CuccaroNormalizedModValues (L : CuccaroNormalizedModLayout)
    (S O W : Nat) (C NF MF : Bool) (s : BasisState) : Prop where
  source : regValue L.normalize.a s=S
  out : regValue L.modular.z s=O
  work : regValue L.normalize.scratch s=W
  cin : s L.cin=C
  normFlag : s L.normFlag=NF
  modFlag : s L.modFlag=MF

private theorem normalized_nodup (L : CuccaroNormalizedModLayout)
    (hnd : L.wires.Nodup) : L.normalize.wires.Nodup ∧ L.modular.wires.Nodup := by
  constructor <;> apply List.nodup_iff_count.mpr <;> intro q
  · have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  · have h := List.nodup_iff_count.mp hnd q
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.wires,CuccaroModLayout.z,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega

private theorem normalized_outside (L : CuccaroNormalizedModLayout)
    (hnd : L.wires.Nodup) :
    (∀q∈L.out++[L.outHigh,L.modFlag],q∉L.normalize.wires) ∧
      L.normFlag∉L.modular.wires := by
  constructor
  · intro q hq hm
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      List.count_cons,List.count_append,List.count_nil] at h h1 h2
    omega
  · intro hm
    have h := List.nodup_iff_count.mp hnd L.normFlag
    have h2 := List.count_pos_iff.mpr hm
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.wires,CuccaroModLayout.z,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at h h2
    omega

theorem cuccaroNormalizedModAdd_spec (L : CuccaroNormalizedModLayout)
    (n c p S O : Nat) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (hpdef : p=2^n-c) (hc : 0<c) (hcn : c<2^n) (hcp : c<p)
    (hS : S<2^n) (hO : O<p) :
    Triple (CuccaroNormalizedModValues L S O 0 false false false)
      (cuccaroNormalizedModAdd L c p)
      (CuccaroNormalizedModValues L S ((S%p+O)%p) 0 false false false) := by
  have nd := normalized_nodup L hnd
  have away := normalized_outside L hnd
  have norm0 := cuccaroNormalize_spec L.normalize n c S (L.normalize_widths n hw)
    nd.1 hc hcn (by simpa [hpdef] using hcp) hS
  let K := decide (p≤S)
  -- Reprove the lifted normalization explicitly so output and the modular flag
  -- are carried by the frame rather than assumed by the leaf theorem.
  have normLift : Triple (CuccaroNormalizedModValues L S O 0 false false false)
      (cuccaroNormalize L.normalize c)
      (CuccaroNormalizedModValues L (S%p) O 0 false K false) := by
    intro st m h
    obtain ⟨ph,hv⟩ := norm0 st m ⟨h.source,h.work,h.cin,h.normFlag⟩
    have outKeep : regValue L.modular.z (run (cuccaroNormalize L.normalize c) m st).basis=O := by
      rw [← h.out]
      apply regValue_congr; intro q hq
      have hout : q∈L.out∨q=L.outHigh := by
        simpa [CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hq
      exact cuccaroNormalize_preserves_outside L.normalize c st m q
        (away.1 q (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto))
    have mfKeep := cuccaroNormalize_preserves_outside L.normalize c st m L.modFlag
      (away.1 L.modFlag (by simp))
    have srcv : regValue L.normalize.a (run (cuccaroNormalize L.normalize c) m st).basis=S%p := by
      simpa [hpdef] using hv.a
    have nfv : (run (cuccaroNormalize L.normalize c) m st).basis L.normFlag=K := by
      simpa [K,hpdef] using hv.flag
    exact ⟨ph,⟨srcv,outKeep,hv.scratch,hv.cin,nfv,mfKeep.trans h.modFlag⟩⟩
  have mod0 := cuccaroModAdd_spec L.modular n p (S%p) O
    (L.modular_widths n hw) nd.2 (by omega) (by rw [hpdef]; omega)
    (Nat.mod_lt _ (by omega)) hO
  have modLift : Triple (CuccaroNormalizedModValues L (S%p) O 0 false K false)
      (cuccaroModAdd L.modular p)
      (CuccaroNormalizedModValues L (S%p) ((S%p+O)%p) 0 false K false) := by
    intro st m h
    obtain ⟨ph,hv⟩ := mod0 st m ⟨h.source,h.out,h.work,h.cin,h.modFlag⟩
    have nf := cuccaroModAdd_preserves_outside L.modular n p
      (L.modular_widths n hw) st m L.normFlag away.2
    exact ⟨ph,⟨hv.a,hv.z,hv.scratch,hv.cin,nf.trans h.normFlag,hv.flag⟩⟩
  intro st records h
  let P := cuccaroNormalize L.normalize c
  let Q := cuccaroModAdd L.modular p
  let R := cuccaroNormalizeClear L.normalize c
  let u := run P (records.take (measurementCount P)) st
  let rest := records.drop (measurementCount P)
  let v := run Q (rest.take (measurementCount Q)) u
  let out := run R (rest.drop (measurementCount Q)) v
  obtain ⟨pu,hu⟩ := normLift st (records.take (measurementCount P)) h
  obtain ⟨pv,hv⟩ := modLift u (rest.take (measurementCount Q)) hu
  have samePhase : v.phase=u.phase := pv
  have sameNormAll : ∀q∈L.normalize.wires,v.basis q=u.basis q := by
    intro q hq
    by_cases ha : q∈L.normalize.a
    · exact (regValue_eq_iff _ _ _).mp (hv.source.trans hu.source.symm) q ha
    by_cases hwq : q∈L.normalize.scratch
    · exact (regValue_eq_iff _ _ _).mp (hv.work.trans hu.work.symm) q hwq
    by_cases hcq : q=L.cin
    · subst q; exact hv.cin.trans hu.cin.symm
    by_cases hfq : q=L.normFlag
    · subst q; exact hv.normFlag.trans hu.normFlag.symm
    exfalso
    simp only [CuccaroNormalizedModLayout.normalize,CuccaroNormalizeLayout.wires,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    tauto
  have sameNorm : ∀q∈wires P.reverse,v.basis q=u.basis q := by
    intro q hq
    rw [wires_reverse] at hq
    exact sameNormAll q (List.mem_toFinset.mp (cuccaroNormalize_wires_subset L.normalize c hq))
  have loc := run_proper_congr P.reverse
    (properProgram_reverse P (cuccaroNormalize_proper L.normalize c nd.1)) v u
    (rest.drop (measurementCount Q)) [] samePhase sameNorm
  have rt := cuccaroNormalize_roundtrip L.normalize c nd.1 st
    (records.take (measurementCount P)) []
  have outPhase : out.phase=st.phase := by
    exact loc.1.trans (congrArg State.phase rt)
  have restoreBit (q : Wire) (hq : q∈L.normalize.wires) : out.basis q=st.basis q := by
    by_cases hsupp : q∈wires P
    · have eq := loc.2 q (by rwa [wires_reverse])
      exact eq.trans (congrArg (fun x => x.basis q) rt)
    · have e1 : (run R (rest.drop (measurementCount Q)) v).basis q=v.basis q := by
        apply run_preserves_outside
        dsimp [R]
        rw [cuccaroNormalizeClear,wires_reverse]
        exact hsupp
      have e2 := sameNormAll q hq
      have e3 := run_preserves_outside P (records.take (measurementCount P)) st q hsupp
      exact e1.trans (e2.trans e3)
  have outSource : regValue L.normalize.a out.basis=S :=
    (regValue_congr _ _ _ (fun q hq => restoreBit q (by
      simp only [CuccaroNormalizeLayout.wires,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false]
      exact Or.inl (Or.inl hq)))).trans h.source
  have outWork : regValue L.normalize.scratch out.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => restoreBit q (by
      simp only [CuccaroNormalizeLayout.wires,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false]
      exact Or.inl (Or.inr hq)))).trans h.work
  have outCin : out.basis L.cin=false :=
    (restoreBit L.cin (by simp [CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch])).trans h.cin
  have outNF : out.basis L.normFlag=false :=
    (restoreBit L.normFlag (by simp [CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires])).trans h.normFlag
  have outTarget : regValue L.modular.z out.basis=(S%p+O)%p := by
    rw [← hv.out]
    apply regValue_congr; intro q hq
    have hout : q∈L.out∨q=L.outHigh := by
      simpa [CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hq
    exact cuccaroNormalizeClear_preserves_outside L.normalize c v
      (rest.drop (measurementCount Q)) q
      (away.1 q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rcases hout with hout|hout
        · exact Or.inl hout
        · exact Or.inr (Or.inl hout)))
  have outMF : out.basis L.modFlag=false :=
    (cuccaroNormalizeClear_preserves_outside L.normalize c v
      (rest.drop (measurementCount Q)) L.modFlag (away.1 L.modFlag (by simp))).trans hv.modFlag
  have exec : run (cuccaroNormalizedModAdd L c p) records st=out := by
    simp [cuccaroNormalizedModAdd,P,Q,R,u,v,out,rest,run_append]
  rw [exec]
  exact ⟨outPhase,⟨outSource,outTarget,outWork,outCin,outNF,outMF⟩⟩


theorem cuccaroNormalizedModSub_spec (L : CuccaroNormalizedModLayout)
    (n c p S O : Nat) (hw : L.Widths n) (hnd : L.wires.Nodup)
    (hpdef : p=2^n-c) (hc : 0<c) (hcn : c<2^n) (hcp : c<p)
    (hS : S<2^n) (hO : O<p) :
    Triple (CuccaroNormalizedModValues L S O 0 false false false)
      (cuccaroNormalizedModSub L c p)
      (CuccaroNormalizedModValues L S ((O+p-(S%p))%p) 0 false false false) := by
  have nd := normalized_nodup L hnd
  have away := normalized_outside L hnd
  have norm0 := cuccaroNormalize_spec L.normalize n c S (L.normalize_widths n hw)
    nd.1 hc hcn (by simpa [hpdef] using hcp) hS
  let K := decide (p≤S)
  -- Reprove the lifted normalization explicitly so output and the modular flag
  -- are carried by the frame rather than assumed by the leaf theorem.
  have normLift : Triple (CuccaroNormalizedModValues L S O 0 false false false)
      (cuccaroNormalize L.normalize c)
      (CuccaroNormalizedModValues L (S%p) O 0 false K false) := by
    intro st m h
    obtain ⟨ph,hv⟩ := norm0 st m ⟨h.source,h.work,h.cin,h.normFlag⟩
    have outKeep : regValue L.modular.z (run (cuccaroNormalize L.normalize c) m st).basis=O := by
      rw [← h.out]
      apply regValue_congr; intro q hq
      have hout : q∈L.out∨q=L.outHigh := by
        simpa [CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hq
      exact cuccaroNormalize_preserves_outside L.normalize c st m q
        (away.1 q (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto))
    have mfKeep := cuccaroNormalize_preserves_outside L.normalize c st m L.modFlag
      (away.1 L.modFlag (by simp))
    have srcv : regValue L.normalize.a (run (cuccaroNormalize L.normalize c) m st).basis=S%p := by
      simpa [hpdef] using hv.a
    have nfv : (run (cuccaroNormalize L.normalize c) m st).basis L.normFlag=K := by
      simpa [K,hpdef] using hv.flag
    exact ⟨ph,⟨srcv,outKeep,hv.scratch,hv.cin,nfv,mfKeep.trans h.modFlag⟩⟩
  have mod0 := cuccaroModSub_spec L.modular n p (S%p) O
    (L.modular_widths n hw) nd.2 (by omega) (by rw [hpdef]; omega)
    (Nat.mod_lt _ (by omega)) hO
  have modLift : Triple (CuccaroNormalizedModValues L (S%p) O 0 false K false)
      (cuccaroModSub L.modular p)
      (CuccaroNormalizedModValues L (S%p) ((O+p-(S%p))%p) 0 false K false) := by
    intro st m h
    obtain ⟨ph,hv⟩ := mod0 st m ⟨h.source,h.out,h.work,h.cin,h.modFlag⟩
    have nf := cuccaroModSub_preserves_outside L.modular n p
      (L.modular_widths n hw) st m L.normFlag away.2
    exact ⟨ph,⟨hv.a,hv.z,hv.scratch,hv.cin,nf.trans h.normFlag,hv.flag⟩⟩
  intro st records h
  let P := cuccaroNormalize L.normalize c
  let Q := cuccaroModSub L.modular p
  let R := cuccaroNormalizeClear L.normalize c
  let u := run P (records.take (measurementCount P)) st
  let rest := records.drop (measurementCount P)
  let v := run Q (rest.take (measurementCount Q)) u
  let out := run R (rest.drop (measurementCount Q)) v
  obtain ⟨pu,hu⟩ := normLift st (records.take (measurementCount P)) h
  obtain ⟨pv,hv⟩ := modLift u (rest.take (measurementCount Q)) hu
  have samePhase : v.phase=u.phase := pv
  have sameNormAll : ∀q∈L.normalize.wires,v.basis q=u.basis q := by
    intro q hq
    by_cases ha : q∈L.normalize.a
    · exact (regValue_eq_iff _ _ _).mp (hv.source.trans hu.source.symm) q ha
    by_cases hwq : q∈L.normalize.scratch
    · exact (regValue_eq_iff _ _ _).mp (hv.work.trans hu.work.symm) q hwq
    by_cases hcq : q=L.cin
    · subst q; exact hv.cin.trans hu.cin.symm
    by_cases hfq : q=L.normFlag
    · subst q; exact hv.normFlag.trans hu.normFlag.symm
    exfalso
    simp only [CuccaroNormalizedModLayout.normalize,CuccaroNormalizeLayout.wires,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    tauto
  have sameNorm : ∀q∈wires P.reverse,v.basis q=u.basis q := by
    intro q hq
    rw [wires_reverse] at hq
    exact sameNormAll q (List.mem_toFinset.mp (cuccaroNormalize_wires_subset L.normalize c hq))
  have loc := run_proper_congr P.reverse
    (properProgram_reverse P (cuccaroNormalize_proper L.normalize c nd.1)) v u
    (rest.drop (measurementCount Q)) [] samePhase sameNorm
  have rt := cuccaroNormalize_roundtrip L.normalize c nd.1 st
    (records.take (measurementCount P)) []
  have outPhase : out.phase=st.phase := by
    exact loc.1.trans (congrArg State.phase rt)
  have restoreBit (q : Wire) (hq : q∈L.normalize.wires) : out.basis q=st.basis q := by
    by_cases hsupp : q∈wires P
    · have eq := loc.2 q (by rwa [wires_reverse])
      exact eq.trans (congrArg (fun x => x.basis q) rt)
    · have e1 : (run R (rest.drop (measurementCount Q)) v).basis q=v.basis q := by
        apply run_preserves_outside
        dsimp [R]
        rw [cuccaroNormalizeClear,wires_reverse]
        exact hsupp
      have e2 := sameNormAll q hq
      have e3 := run_preserves_outside P (records.take (measurementCount P)) st q hsupp
      exact e1.trans (e2.trans e3)
  have outSource : regValue L.normalize.a out.basis=S :=
    (regValue_congr _ _ _ (fun q hq => restoreBit q (by
      simp only [CuccaroNormalizeLayout.wires,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false]
      exact Or.inl (Or.inl hq)))).trans h.source
  have outWork : regValue L.normalize.scratch out.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => restoreBit q (by
      simp only [CuccaroNormalizeLayout.wires,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false]
      exact Or.inl (Or.inr hq)))).trans h.work
  have outCin : out.basis L.cin=false :=
    (restoreBit L.cin (by simp [CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.scratch])).trans h.cin
  have outNF : out.basis L.normFlag=false :=
    (restoreBit L.normFlag (by simp [CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires])).trans h.normFlag
  have outTarget : regValue L.modular.z out.basis=(O+p-(S%p))%p := by
    rw [← hv.out]
    apply regValue_congr; intro q hq
    have hout : q∈L.out∨q=L.outHigh := by
      simpa [CuccaroNormalizedModLayout.modular,CuccaroModLayout.z] using hq
    exact cuccaroNormalizeClear_preserves_outside L.normalize c v
      (rest.drop (measurementCount Q)) q
      (away.1 q (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        rcases hout with hout|hout
        · exact Or.inl hout
        · exact Or.inr (Or.inl hout)))
  have outMF : out.basis L.modFlag=false :=
    (cuccaroNormalizeClear_preserves_outside L.normalize c v
      (rest.drop (measurementCount Q)) L.modFlag (away.1 L.modFlag (by simp))).trans hv.modFlag
  have exec : run (cuccaroNormalizedModSub L c p) records st=out := by
    simp [cuccaroNormalizedModSub,P,Q,R,u,v,out,rest,run_append]
  rw [exec]
  exact ⟨outPhase,⟨outSource,outTarget,outWork,outCin,outNF,outMF⟩⟩

private theorem normalized_outside_views (L : CuccaroNormalizedModLayout)
    (q : Wire) (hq : q∉L.wires) :
    q∉L.normalize.wires ∧ q∉L.modular.wires := by
  constructor <;> intro hm <;> apply hq
  · simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,
      CuccaroNormalizeLayout.scratch,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hm ⊢
    tauto
  · simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.modular,
      CuccaroModLayout.wires,CuccaroModLayout.z,CuccaroModLayout.allWork,
      CuccaroModLayout.scratch,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hm ⊢
    tauto

theorem cuccaroNormalizedModAdd_preserves_outside (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) (s : State) (records : List Bool)
    (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroNormalizedModAdd L c p) records s).basis q=s.basis q := by
  let P := cuccaroNormalize L.normalize c
  let Q := cuccaroModAdd L.modular p
  let R := cuccaroNormalizeClear L.normalize c
  let rest := records.drop (measurementCount P)
  let u := run P (records.take (measurementCount P)) s
  let v := run Q (rest.take (measurementCount Q)) u
  have away := normalized_outside_views L q hq
  have h1 := cuccaroNormalize_preserves_outside L.normalize c s
    (records.take (measurementCount P)) q away.1
  have h2 := cuccaroModAdd_preserves_outside L.modular n p (L.modular_widths n hw) u
    (rest.take (measurementCount Q)) q away.2
  have h3 := cuccaroNormalizeClear_preserves_outside L.normalize c v
    (rest.drop (measurementCount Q)) q away.1
  simpa [cuccaroNormalizedModAdd,P,Q,R,rest,u,v,run_append] using h3.trans (h2.trans h1)

theorem cuccaroNormalizedModSub_preserves_outside (L : CuccaroNormalizedModLayout)
    (n c p : Nat) (hw : L.Widths n) (s : State) (records : List Bool)
    (q : Wire) (hq : q∉L.wires) :
    (run (cuccaroNormalizedModSub L c p) records s).basis q=s.basis q := by
  let P := cuccaroNormalize L.normalize c
  let Q := cuccaroModSub L.modular p
  let R := cuccaroNormalizeClear L.normalize c
  let rest := records.drop (measurementCount P)
  let u := run P (records.take (measurementCount P)) s
  let v := run Q (rest.take (measurementCount Q)) u
  have away := normalized_outside_views L q hq
  have h1 := cuccaroNormalize_preserves_outside L.normalize c s
    (records.take (measurementCount P)) q away.1
  have h2 := cuccaroModSub_preserves_outside L.modular n p (L.modular_widths n hw) u
    (rest.take (measurementCount Q)) q away.2
  have h3 := cuccaroNormalizeClear_preserves_outside L.normalize c v
    (rest.drop (measurementCount Q)) q away.1
  simpa [cuccaroNormalizedModSub,P,Q,R,rest,u,v,run_append] using h3.trans (h2.trans h1)


end ECDSAAdd.Arithmetic
