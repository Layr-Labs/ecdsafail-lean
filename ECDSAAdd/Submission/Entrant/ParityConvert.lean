import ECDSAAdd.Submission.Entrant.ParityCarry
import ECDSAAdd.Submission.Entrant.Prelude

namespace ECDSAAdd.Entrant.ParityConvert
open ECDSAAdd Arithmetic Challenge ParityCarry EntryFuseArithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem prefix_eq (A B Q : Program) (s : State) (m : List Bool)
    (hc : measurementCount A=measurementCount B) (he : run A m s=run B m s) :
    run (A++Q) m s=run (B++Q) m s := by
  simp only [run_append,run_take]
  rw [he,hc]

theorem compare_layout_counts (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    toffoliCount (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)+1=
      toffoliCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    measurementCount (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)=
      measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    gateSlots (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)+5=
      gateSlots (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact comparePrefixNew_counts g a b c K.cin K.flag as bs cs v

theorem old_entry_split (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (k : Nat) :
    EntryFuse.entry K g complement k=
      comparePrefixOld g K.src K.out K.carry K.cin K.flag (complement+k)++
        EntryFuse.entryBody K g k K.out.tail := by
  have hout:K.out=EntryFuse.lowBit K::K.out.tail := by
    obtain ⟨a,as,hs⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,hs]
  have h:=EntryFuse.entry_decompose K g complement k K.out.tail hout
  simpa only [comparePrefixOld,loadNot,unloadNot,EntryFuse.entryCompare,EntryFuse.entryBody,
    EntryFuse.entryMiddle,List.append_assoc] using h

def entryOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k%2=1 then
    comparePrefixNew g K.src K.out K.carry K.cin K.flag (complement+k)++
      EntryFuse.entryBody K g k K.out.tail
  else EntryFuse.entry K g complement k

theorem entryOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) (hn : (g::K.wires).Nodup) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hi : s.basis K.cin=false) :
    run (entryOpt K g k) m s=run (EntryFuse.entry K g complement k) m s := by
  unfold entryOpt
  split_ifs with hk
  · have he:(complement+k)%2=0 := by norm_num [complement,Nat.add_mod,hk]
    rw [old_entry_split K g hw k]
    exact prefix_eq _ _ _ s m (compare_layout_counts K g hw (complement+k)).2.1
      (compare_layout_eq K g hw hn (complement+k) he s m hs hi)
  · rfl

theorem entryOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (entryOpt K g k)+oddSavings k=766 ∧ measurementCount (entryOpt K g k)=767 ∧
    gateSlots (entryOpt K g k)≤gateSlots (EntryFuse.entry K g complement k) := by
  have old:=EntryFuse.entry_counts K g complement k hw
  have delta:=compare_layout_counts K g hw (complement+k)
  have split:=old_entry_split K g hw k
  have ct:=congrArg toffoliCount split
  have cm:=congrArg measurementCount split
  have cg:=congrArg gateSlots split
  unfold entryOpt oddSavings
  split_ifs <;> simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at * <;> omega


open EntryFuse ExitFusionProof Secp256k1 BalancedField

theorem erase_layout_counts (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    toffoliCount (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)+1=
      toffoliCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    measurementCount (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)=
      measurementCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    gateSlots (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)+8=
      gateSlots (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact erasePrefixNew_counts g a a' b b' c K.cin K.flag as bs cs v

def eraseInputOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  if k%2=1 then erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)
  else ExitFusionResearch.eraseInputWrap K g complement k

theorem old_erase_split (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) :
    ExitFusionResearch.eraseInputWrap K g complement k=
      erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k) := by
  simp only [ExitFusionResearch.eraseInputWrap,erasePrefixOld,loadNot,unloadNot,List.append_assoc]

theorem eraseInputOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hw : K.Widths 256) (hn : (g::K.wires).Nodup) (s : State) (m : List Bool)
    (hs : regValue K.src s.basis=0) (hi : s.basis K.cin=false) :
    run (eraseInputOpt K g k) m s=run (ExitFusionResearch.eraseInputWrap K g complement k) m s := by
  unfold eraseInputOpt
  split_ifs with hk
  · have he:(complement+k)%2=0 := by norm_num [complement,Nat.add_mod,hk]
    rw [old_erase_split]
    exact erase_layout_eq K g hw hn (complement+k) he s m hs hi
  · rfl

theorem eraseInputOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (eraseInputOpt K g k)+oddSavings k=toffoliCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    measurementCount (eraseInputOpt K g k)=measurementCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    gateSlots (eraseInputOpt K g k)≤gateSlots (ExitFusionResearch.eraseInputWrap K g complement k) := by
  have delta:=erase_layout_counts K g hw (complement+k)
  rw [old_erase_split]
  unfold eraseInputOpt oddSavings
  split_ifs with hk
  · omega
  · rw [old_erase_split]
    omega

def exitOpt (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  ExitFusionResearch.recoverWrap K g complement k++ExitFusionResearch.undoMiddle K g complement k++
    (ExitFusionResearch.signStage K g k).reverse++eraseInputOpt K g k

theorem exitOpt_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    toffoliCount (exitOpt K g k)+oddSavings k=766 ∧ measurementCount (exitOpt K g k)=766 ∧
    gateSlots (exitOpt K g k)≤gateSlots (ExitFusionResearch.exit K g complement k) := by
  have old:=ExitFusionResearch.exit_counts K g complement k hw
  have delta:=eraseInputOpt_counts K g k hw
  simp only [exitOpt,ExitFusionResearch.exit,toffoliCount_append,measurementCount_append,gateSlots_append] at *
  omega

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩
theorem exitOpt_entry_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis=Y)
    (hy : Y<prime) (hk : k<prime) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitOpt K g k) n (run (EntryFuse.entry K g complement k) m s)=s := by
  obtain ⟨rest,hout⟩ := out_shape K hw
  have pc : prime+complement=2^256 := by norm_num [prime,modulus,complement]
  let m1 := m.take (measurementCount (entryCompare K g complement k))
  let m2 := m.drop (measurementCount (entryCompare K g complement k))
  let t := run (entryCompare K g complement k) m1 s
  have initial : FastConst.Frame K s.basis 0 Y false s.basis := ⟨hsrc,hY,hf,by intro q hq; rfl⟩
  have pre := comparePrefix_correct hn 256 hw s.basis hcarry hcin complement prime k Y pc hk hy s m1 initial
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (prime≤Y+k) else false) t.basis at pre
  have tg : t.basis g=s.basis g := pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th : t.basis K.high=false := (pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have tcin : t.basis K.cin=false := (pre.2.2.2.2 K.cin
    (FastConst.fixed_not_mutable hn K.cin (by simp))).trans hcin
  have tcarry : ∀q∈K.carry,t.basis q=false := by
    intro q hq
    exact (pre.2.2.2.2 q (FastConst.fixed_not_mutable hn q (by simp [hq]))).trans (hcarry q hq)
  have tflag : t.basis K.flag=decide (prime≤Y+(if t.basis g then k else 0)) := by
    rw [tg]
    have h := pre.2.2.2.1
    cases hg : s.basis g <;> simp [hg,show ¬prime≤Y by omega] at h ⊢ <;> exact h
  let A := ExitFusionResearch.recoverWrap K g complement k
  let B := ExitFusionResearch.undoMiddle K g complement k
  let C := (ExitFusionResearch.signStage K g k).reverse
  let D := eraseInputOpt K g k
  obtain ⟨n1,n2,n3,n4,parts⟩ := run_four A B C D n (run (entryBody K g k rest) m2 t)
  have recover : run A n1 (run (entryBody K g k rest) m2 t)=
      run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t :=
    recover_entryBody K g k Y hn hw rest hout t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have undo : run C n3 (run B n2
      (run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t))=t :=
    undo_entryMiddle_inverse K g k hn hw rest hout t _ n2 n3 pre.2.1 th tcin tcarry
  have erase : run D n4 t=s := by
    change run (eraseInputOpt K g k) n4 t=s
    rw [eraseInputOpt_eq K g k hw hn t n4 pre.2.1 tcin]
    exact eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry
  have decomp : EntryFuse.entry K g complement k=entryCompare K g complement k++entryBody K g k rest := by
    rw [entry_decompose K g complement k rest hout]
    simp only [entryBody,entryMiddle,List.append_assoc]
  rw [decomp,run_append]
  change run (A++B++C++D) n (run (entryBody K g k rest) m2 t)=s
  rw [parts,recover,undo,erase]

theorem exitOpt_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis=centerWord H)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    let v := run (exitOpt K g k.val) m s
    v.phase=s.phase ∧ regValue K.out v.basis=(2*H-(if s.basis g then k else 0)).val ∧
      ∀q,q∉K.out → v.basis q=s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let Y : Fp := 2*H-(if s.basis g then k else 0)
  let b := run (xorConstant K.out (regValue K.out s.basis)) [] s
  have clear := xorConstant_correct K.out (FastConst.out_nodup hn) (regValue K.out s.basis)
    (regValue_lt K.out s.basis) s []
  have yBound : Y.val<2^K.out.length := by
    rw [hw.out]
    exact Y.isLt.trans (by norm_num [p])
  let a := run (xorConstant K.out Y.val) [] b
  have load := xorConstant_correct K.out (FastConst.out_nodup hn) Y.val yBound b []
  have av : regValue K.out a.basis=Y.val := by rw [load.2.2,clear.2.2]; simp
  have ap : a.phase=s.phase := load.1.trans clear.1
  have outside (q : Wire) (hq : q∉K.out) : a.basis q=s.basis q :=
    (load.2.1 q hq).trans (clear.2.1 q hq)
  have aSrc : regValue K.src a.basis=0 := by
    rw [regValue_congr _ _ _ (fun q hq => outside q (src_fullOut K g hn q hq)),hsrc]
  have fixedOutside (q : Wire) (hq : q∈K.carry++[K.high,K.cin]) : q∉K.out := by
    intro bad
    exact FastConst.fixed_not_mutable hn q hq (by simp [FastConst.mutable,bad])
  have af : a.basis K.flag=false := (outside _ (FastConst.flag_not_out hn)).trans hf
  have ah : a.basis K.high=false := (outside _ (fixedOutside _ (by simp))).trans hh
  have ac : a.basis K.cin=false := (outside _ (fixedOutside _ (by simp))).trans hcin
  have aCarry : ∀q∈K.carry,a.basis q=false := by
    intro q hq
    exact (outside q (fixedOutside q (by simp [hq]))).trans (hcarry q hq)
  have ag : a.basis g=s.basis g := outside g (FastConst.g_not_out hn)
  have fwd := entry_field_correct K g k Y hn hw a [] av aSrc af ah ac aCarry
  have math : (Y+(if a.basis g then k else 0))/2=H := by
    rw [ag]
    dsimp only [Y]
    rw [sub_add_cancel]
    have two : (2:Fp)≠0 := by decide
    field_simp
  have preimage : run (EntryFuse.entry K g complement k.val) [] a=s := by
    apply State.extensionality
    · exact fwd.1.trans ap
    · funext q
      by_cases hq : q∈K.out
      · have val : regValue K.out (run (EntryFuse.entry K g complement k.val) [] a).basis=regValue K.out s.basis := by
          rw [fwd.2.1,math,hH]
        exact (regValue_eq_iff _ _ _).mp val q hq
      · exact (fwd.2.2 q hq).trans (outside q hq)
  have hy : Y.val<prime := by rw [prime_eq_secp]; exact Y.isLt
  have hk : k.val<prime := by rw [prime_eq_secp]; exact k.isLt
  have inv := exitOpt_entry_inverse K g k.val Y.val hn hw a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap,av,outside⟩


theorem exitOpt_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (s : State) (m n : List Bool)
    (hH : regValue K.out s.basis=centerWord H) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitOpt K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  have a:=exitOpt_field_correct K g k H hn hw s m hH hsrc hf hh hcin hcarry
  have b:=ExitFusionProof.exit_field_correct K g k H hn hw s n hH hsrc hf hh hcin hcarry
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq:q∈K.out
    · exact (regValue_eq_iff K.out _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2 q hq).trans (b.2.2 q hq).symm


theorem cmp_prefix_wires (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    wires (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v)⊆
      wires (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) := by
  have h:=compareLtHeadOne_wires a b c as bs cs cin flag
  simp only [comparePrefixNew,comparePrefixOld,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem cmp_prefix_physical (g a b c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (h : GatePhysical (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)) :
    GatePhysical (comparePrefixNew g (a::as) (b::bs) (c::cs) cin flag v) := by
  simp only [comparePrefixOld,gatePhysical_append] at h
  simp only [comparePrefixNew,gatePhysical_append]
  exact ⟨⟨h.1.1,compareLtHeadOne_physical a b c as bs cs cin flag h.1.2⟩,h.2⟩

theorem era_prefix_wires (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat) :
    wires (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)⊆
      wires (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  have h:=eraseLtHeadZero_wires a a' b b' c as bs cs cin flag
  simp only [erasePrefixNew,erasePrefixOld,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem era_prefix_physical (g a a' b b' c cin flag : Wire) (as bs cs : List Wire) (v : Nat)
    (h : GatePhysical (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)) :
    GatePhysical (erasePrefixNew g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  simp only [erasePrefixOld,gatePhysical_append] at h
  simp only [erasePrefixNew,gatePhysical_append]
  exact ⟨⟨h.1.1,eraseLtHeadZero_physical a a' b b' c as bs cs cin flag h.1.2⟩,h.2⟩

theorem compare_layout_wires (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    wires (comparePrefixNew g K.src K.out K.carry K.cin K.flag v)⊆
      wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact cmp_prefix_wires g a b c K.cin K.flag as bs cs v

theorem compare_layout_physical (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat)
    (h : GatePhysical (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)) :
    GatePhysical (comparePrefixNew g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc] at h ⊢
  exact cmp_prefix_physical g a b c K.cin K.flag as bs cs v h

theorem erase_layout_wires (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat) :
    wires (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v)⊆
      wires (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact era_prefix_wires g a a' b b' c K.cin K.flag as bs cs v

theorem erase_layout_physical (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256) (v : Nat)
    (h : GatePhysical (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)) :
    GatePhysical (erasePrefixNew g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc] at h ⊢
  exact era_prefix_physical g a a' b b' c K.cin K.flag as bs cs v h

theorem entryOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (entryOpt K g k)⊆wires (EntryFuse.entry K g complement k) := by
  unfold entryOpt
  split_ifs
  · rw [old_entry_split K g hw k]
    simp only [wires_append]
    exact Finset.union_subset_union (compare_layout_wires K g hw (complement+k)) (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem entryOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (entryOpt K g k) := by
  have old:=EntryFuse.entry_physical K g complement k hn hw
  unfold entryOpt
  split_ifs
  · rw [old_entry_split K g hw k] at old
    simp only [gatePhysical_append] at old ⊢
    exact ⟨compare_layout_physical K g hw (complement+k) old.1,old.2⟩
  · exact old

theorem eraseInputOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (eraseInputOpt K g k)⊆wires (ExitFusionResearch.eraseInputWrap K g complement k) := by
  unfold eraseInputOpt
  split_ifs
  · rw [old_erase_split]
    exact erase_layout_wires K g hw (complement+k)
  · exact Finset.Subset.refl _

theorem eraseInputOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256)
    (h : GatePhysical (ExitFusionResearch.eraseInputWrap K g complement k)) : GatePhysical (eraseInputOpt K g k) := by
  unfold eraseInputOpt
  split_ifs
  · rw [old_erase_split] at h
    exact erase_layout_physical K g hw (complement+k) h
  · exact h

theorem exitOpt_wires (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw : K.Widths 256) :
    wires (exitOpt K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  have h:=eraseInputOpt_wires K g k hw
  simp only [exitOpt,ExitFusionResearch.exit,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) h

theorem exitOpt_physical (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) : GatePhysical (exitOpt K g k) := by
  have old:=ExitFusionResearch.exit_physical K g complement k hn hw
  simp only [ExitFusionResearch.exit,gatePhysical_append] at old
  simp only [exitOpt,gatePhysical_append]
  exact ⟨old.1,eraseInputOpt_physical K g k hw old.2⟩


def yLayout (L : ControlledPointLayout) : MeasuredCanonicalModLayout := L.recoveryConstant L.point.y

def entryYOpt (L : ControlledPointLayout) (k : Fp) : Program := entryOpt (yLayout L) L.core.generic k.val

def exitYOpt (L : ControlledPointLayout) (k : Fp) : Program := exitOpt (yLayout L) L.core.generic k.val

theorem y_aux_clean (L : ControlledPointLayout) (hw : L.Widths) (s : State)
    (hc : regValue L.dialogPool s.basis=0) (q : Wire)
    (hq : q∈(yLayout L).src++(yLayout L).carry++[(yLayout L).high,(yLayout L).cin,(yLayout L).flag]) :
    s.basis q=false := by
  change q∈(L.recoveryConstant L.point.y).src++(L.recoveryConstant L.point.y).carry++
    [(L.recoveryConstant L.point.y).high,(L.recoveryConstant L.point.y).cin,(L.recoveryConstant L.point.y).flag] at hq
  rw [L.recoveryConstant_pool hw L.point.y] at hq
  exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)

theorem entryYOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (s : State) (m : List Bool) (hc : regValue L.dialogPool s.basis=0) :
    run (entryYOpt L k) m s=run (EntryFuse.fusedY L k) m s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have ci:s.basis K.cin=false:=aux _ (by simp [K])
  have h:=entryOpt_eq K L.core.generic k.val
    (L.recoveryConstant_widths hw L.point.y hw.inputY)
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) s m sz ci
  simpa only [entryYOpt,EntryFuse.fusedY,K,yLayout] using h

theorem exitYOpt_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m n : List Bool)
    (hy : regValue L.point.y s.basis=centerWord Y) (hc : regValue L.dialogPool s.basis=0) :
    run (exitYOpt L k) m s=run (ExitFusionResearch.exitY L k) n s := by
  let K:=yLayout L
  have aux:=y_aux_clean L hw s hc
  have sz:regValue K.src s.basis=0 := (regValue_zero _ _).mpr (fun q hq=>aux q (by simp [K,hq]))
  have h:=exitOpt_eq K L.core.generic k Y
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl))
    (L.recoveryConstant_widths hw L.point.y hw.inputY) s m n hy sz
    (aux _ (by simp [K])) (aux _ (by simp [K])) (aux _ (by simp [K]))
    (fun q hq=>aux q (by simp [K,hq]))
  simpa only [exitYOpt,ExitFusionResearch.exitY,K,yLayout] using h

theorem entryYOpt_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hy : regValue L.point.y s.basis=Y.val)
    (hc : regValue L.dialogPool s.basis=0) :
    let v:=run (entryYOpt L k) m s
    v.phase=s.phase ∧ regValue L.point.y v.basis=centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
      ∀q,q∉L.point.y → v.basis q=s.basis q := by
  dsimp only
  rw [entryYOpt_eq L hw hn k s m hc]
  exact EntryFuse.fusedY_correct L hw hn Y k s m hy hc

theorem exitYOpt_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y k : Fp) (s : State) (m : List Bool) (hy : regValue L.point.y s.basis=centerWord Y)
    (hc : regValue L.dialogPool s.basis=0) :
    let v:=run (exitYOpt L k) m s
    v.phase=s.phase ∧ regValue L.point.y v.basis=(2*Y-(if s.basis L.core.generic then k else 0)).val ∧
      ∀q,q∉L.point.y → v.basis q=s.basis q := by
  dsimp only
  rw [exitYOpt_eq L hw hn Y k s m m hy hc]
  exact ExitFusionResearch.exitY_correct L hw hn Y k s m hy hc

theorem entryYOpt_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryYOpt L k)+oddSavings k.val=766 ∧ measurementCount (entryYOpt L k)=767 ∧
    gateSlots (entryYOpt L k)≤gateSlots (EntryFuse.fusedY L k) := by
  exact entryOpt_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (exitYOpt L k)+oddSavings k.val=766 ∧ measurementCount (exitYOpt L k)=766 ∧
    gateSlots (exitYOpt L k)≤gateSlots (ExitFusionResearch.exitY L k) := by
  exact exitOpt_counts (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

attribute [local irreducible] wires GatePhysical

theorem entryYOpt_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryYOpt L k)⊆wires (EntryFuse.fusedY L k) :=
  entryOpt_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_wires (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (exitYOpt L k)⊆wires (ExitFusionResearch.exitY L k) :=
  exitOpt_wires (yLayout L) L.core.generic k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem entryYOpt_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (entryYOpt L k) :=
  entryOpt_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

theorem exitYOpt_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (exitYOpt L k) :=
  exitOpt_physical (yLayout L) L.core.generic k.val
    (L.recoveryConstant_nodup hw hn L.point.y (Or.inr rfl)) (L.recoveryConstant_widths hw L.point.y hw.inputY)

end ECDSAAdd.Entrant.ParityConvert
