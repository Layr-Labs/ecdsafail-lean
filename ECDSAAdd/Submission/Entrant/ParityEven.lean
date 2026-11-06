import ECDSAAdd.Submission.Entrant.ParityConvert
namespace ECDSAAdd.Entrant.ParityEven
open Arithmetic Secp256k1 Challenge ParityCarry
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem cached_majority (a b cin carry h : Wire) (hn : [a,b,cin,carry].Nodup)
    (hh : carry≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=true) (hp : s.basis h=(!s.basis a && !s.basis b)) :
    run (majority a b cin carry) m s=run [.X carry,.CX h carry] m s := by
  rw [majority_correct a b cin carry hn]
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=carry
  · subst q
    simp only [run,writeBit,Function.update_self,Function.update_of_ne hh.symm]
    rw [hc,hp]
    cases s.basis a <;> cases s.basis b <;> cases s.basis carry <;> rfl
  · simp [run,writeBit,Function.update,hq]

theorem even_shared_product (y k : Nat) (g : Bool)
    (hy : y<EntryFuseArithmetic.prime) (hk : k<EntryFuseArithmetic.prime) (he : k%2=0) :
    (g && decide (((y+(if g then k else 0))%EntryFuseArithmetic.prime)%2=1)) =
      ((g && decide (y%2=1)) ^^ decide (EntryFuseArithmetic.prime≤y+(if g then k else 0))) := by
  rw [EntryFuseArithmetic.output_sign_controlled y k g hy hk]
  have w:=EntryFuseArithmetic.wrap_implies_control y k g hy
  simp only [he,show ¬(0:Nat)=1 by decide,decide_false,Bool.and_false,Bool.xor_false]
  cases g <;> simp_all

def put (s : State) (q : Wire) (v : Bool) : State:=⟨s.phase,writeBit s.basis q v⟩

theorem run_put (P : Program) (m : List Bool) (s : State) (q : Wire) (v : Bool)
    (hq : q∉wires P) : run P m (put s q v)=put (run P m s) q v := by
  have agree:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m (put s q v) s
    (by rfl) (by
      intro w hw
      have ne:w≠q:=fun e=>hq (e ▸ hw)
      simp [put,writeBit,ne])
  apply State.extensionality
  · exact agree.1
  funext w
  by_cases he:w=q
  · subst w
    rw [run_preserves_outside P m (put s q v) q hq]
    simp [put,writeBit]
  · by_cases hw:w∈wires P
    · simpa [put,writeBit,he] using agree.2 w hw
    · rw [run_preserves_outside P m (put s q v) w hw]
      simp [put,writeBit,he,run_preserves_outside P m s w hw]

def compareChainCached (x y carry : List Wire) (cin target h : Wire) : Program :=
  match x,y,carry with
  | a::as,b::bs,c::cs => [.X c,.CX h c]++compareChain none as bs cs c target++eraseCarry a b cin c
  | _,_,_ => compareChain none x y carry cin target

theorem compareChainCached_eq (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire)
    (hn : [a,b,cin,c].Nodup) (hh : c≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=true) (hp : s.basis h=(!s.basis a && !s.basis b)) :
    run (compareChainCached (a::as) (b::bs) (c::cs) cin target h) m s=
      run (compareChain none (a::as) (b::bs) (c::cs) cin target) m s := by
  simp only [compareChainCached,compareChain,List.append_assoc,run_append,measurementCount_append]
  rw [cached_majority a b cin c h hn hh s _ hc hp]
  rfl

theorem compareChainCached_counts (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    toffoliCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)+1=
      toffoliCount (compareChain none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  simp [compareChainCached,compareChain,majority,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount]
  omega

def compareLtCached (x y carry : List Wire) (cin target h : Wire) : Program :=
  notRegister (cin::y)++compareChainCached x y carry cin target h++notRegister (cin::y)

theorem compareLtCached_eq (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire)
    (hn : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup) (hao : a∉cin::b::bs)
    (hho : h∉cin::b::bs) (hhc : c≠h) (s : State) (m : List Bool)
    (hc : s.basis cin=false) (hp : s.basis h=(!s.basis a && s.basis b)) :
    run (compareLtCached (a::as) (b::bs) (c::cs) cin target h) m s=
      run (compareLt none (a::as) (b::bs) (c::cs) cin target) m s := by
  let P:=notRegister (cin::b::bs)
  let t:=run P m s
  have tr:=notRegister_correct (cin::b::bs) hy s m
  have ta:t.basis a=s.basis a := by
    change (run (notRegister (cin::b::bs)) m s).basis a=s.basis a
    rw [tr]
    change (if a∈cin::b::bs then !s.basis a else s.basis a)=s.basis a
    rw [if_neg hao]
  have th:t.basis h=s.basis h := by
    change (run (notRegister (cin::b::bs)) m s).basis h=s.basis h
    rw [tr]
    change (if h∈cin::b::bs then !s.basis h else s.basis h)=s.basis h
    rw [if_neg hho]
  have tb:t.basis b= !s.basis b := by simp [t,P,tr]
  have tc:t.basis cin=true := by simp [t,P,tr,hc]
  have eqn:=compareChainCached_eq a b c as bs cs cin target h hn hhc t m tc
    (by rw [th,ta,tb,Bool.not_not];exact hp)
  have cnt:measurementCount (compareChainCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareChain none (a::as) (b::bs) (c::cs) cin target):=
    (compareChainCached_counts a b c as bs cs cin target h).2
  simp only [compareLtCached,compareLt,List.append_assoc,run_append,run_take]
  change run P _ (run (compareChainCached _ _ _ cin target h) _ (run P _ s))=
    run P _ (run (compareChain none _ _ _ cin target) _ (run P _ s))
  simp only [(notRegister_counts (cin::b::bs)).2,List.drop_zero]
  rw [show run P m s=t from rfl,eqn,cnt]

theorem cached_flag_eq (g b f a : Wire) (hfa : f≠a) (s : State) (m : List Bool)
    (A : Bool) (ha : s.basis a=false) (hprod : (s.basis g && s.basis b)=(A ^^ s.basis f)) :
    run [.CX f a] m (put s a A)=run [.CCX g b a] m s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=a
  · subst q
    simp [run,put,writeBit,Function.update,hfa,ha,hprod]
  · simp [run,put,writeBit,Function.update,hq]

theorem masked_odd_head (g a : Wire) (as : List Wire) (v : Nat) (he : v%2=1)
    (ha : a∉as) (hag : a≠g) (s : State) (m : List Bool) :
    (run (maskedConstant g (a::as) v) m s).basis a=(s.basis a ^^ s.basis g) := by
  simp only [maskedConstant,he,if_true]
  rw [run_append,run_preserves_outside]
  · simp [run,writeBit]
  · intro hm
    have hs:=maskedConstant_wires_subset g as (v/2) hm
    simp only [List.mem_toFinset,List.mem_cons] at hs
    exact hs.elim hag ha

theorem load_odd_not (g a : Wire) (as : List Wire) (v : Nat) (he : v%2=1)
    (hn : (a::as).Nodup) (hag : a≠g) (s : State) (m : List Bool) (ha : s.basis a=false) :
    (run (loadNot g (a::as) v) m s).basis a= !s.basis g := by
  let u:=run (maskedConstant g (a::as) v) m s
  have ua:u.basis a=s.basis g := by
    rw [masked_odd_head g a as v he (List.nodup_cons.mp hn).1 hag s m,ha]
    simp
  have tr:=notRegister_correct (a::as) hn u m
  simp only [loadNot,run_append]
  simp only [run_take]
  simp only [(maskedConstant_counts _ _ _).2,List.drop_zero]
  change (run (notRegister (a::as)) m u).basis a= !s.basis g
  rw [tr]
  simp [ua]

theorem loadNot_outside (g q : Wire) (src : List Wire) (v : Nat) (s : State) (m : List Bool)
    (hqg:q≠g) (hqs:q∉src) : (run (loadNot g src v) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  simp only [loadNot,wires_append,Finset.mem_union,notRegister_wires,List.mem_toFinset] at h
  rcases h with h|h
  · have H:=maskedConstant_wires_subset g src v h
    simp only [List.mem_toFinset,List.mem_cons] at H
    exact H.elim hqg hqs
  · exact hqs h

def comparePrefixCached (g h : Wire) (src out carry : List Wire) (cin flag : Wire) (v : Nat) : Program :=
  loadNot g src v++compareLtCached src out carry cin flag h++unloadNot g src v

theorem compareLtCached_counts (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    toffoliCount (compareLtCached (a::as) (b::bs) (c::cs) cin target h)+1=
      toffoliCount (compareLt none (a::as) (b::bs) (c::cs) cin target) ∧
    measurementCount (compareLtCached (a::as) (b::bs) (c::cs) cin target h)=
      measurementCount (compareLt none (a::as) (b::bs) (c::cs) cin target) := by
  have H:=compareChainCached_counts a b c as bs cs cin target h
  simp only [compareLtCached,compareLt,toffoliCount_append,measurementCount_append]
  omega

theorem comparePrefixCached_eq (g a b c cin flag h : Wire) (as bs cs : List Wire) (v : Nat)
    (he : v%2=1) (hn : (a::as).Nodup) (hag : a≠g)
    (hcg : cin≠g) (hcs : cin∉a::as) (hbg : b≠g) (hbs : b∉a::as)
    (hhg : h≠g) (hhs : h∉a::as) (hhc : c≠h)
    (hport : [a,b,cin,c].Nodup) (hy : (cin::b::bs).Nodup)
    (hao : a∉cin::b::bs) (hho : h∉cin::b::bs)
    (s : State) (m : List Bool) (ha : s.basis a=false) (hc : s.basis cin=false)
    (hp : s.basis h=(s.basis g && s.basis b)) :
    run (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v) m s=
      run (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v) m s := by
  apply middle_eq _ _ _ _ s m (compareLtCached_counts a b c as bs cs cin flag h).2
  intro n
  apply compareLtCached_eq a b c as bs cs cin flag h hport hy hao hho hhc
  · rw [loadNot_outside g cin (a::as) v s m hcg hcs,hc]
  · rw [loadNot_outside g h (a::as) v s m hhg hhs,
      load_odd_not g a as v he hn hag s m ha,
      loadNot_outside g b (a::as) v s m hbg hbs,Bool.not_not]
    exact hp

theorem cached_layout_eq (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he : v%2=1)
    (s : State) (m : List Bool) (hs0 : regValue K.src s.basis=0) (hc0 : s.basis K.cin=false)
    (hp : s.basis K.high=(s.basis g && s.basis (EntryFuse.lowBit K))) :
    run (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) m s=
      run (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) m s := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=layout_core_nodup K g hn
  rw [hs,ho,hc] at H
  have N:(g::K.high::K.cin::(K.src++K.out++K.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have C:=List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at C ⊢
    omega
  rw [hs,ho,hc] at N
  obtain ⟨gf,N⟩:=List.nodup_cons.mp N
  obtain ⟨hf,N⟩:=List.nodup_cons.mp N
  have csFree:= (List.nodup_cons.mp H).1
  have srcND:(a::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have ag:a≠g:=by intro e;exact gf (by simp [←e])
  have bg:b≠g:=by intro e;exact gf (by simp [←e])
  have hg:K.high≠g:=by intro e;exact gf (by simp [←e])
  have ciSrc:K.cin∉a::as:=by
    intro h;exact csFree (List.mem_append_left _ (List.mem_append_left _ h))
  have hiSrc:K.high∉a::as:=by
    intro h;exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have hiOut:K.high∉K.cin::b::bs:=by
    intro h
    rcases List.mem_cons.mp h with h|h
    · exact hf (List.mem_cons.mpr (Or.inl h))
    · exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h)))
  have chi:c≠K.high:=by intro e;exact hf (by simp [←e])
  have bSrc:b∉a::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons.of_append_left).2.2 b h b (by simp) rfl
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  have ph:s.basis K.high=(s.basis g && s.basis b):=by simpa [EntryFuse.lowBit,ho] using hp
  rw [hs,ho,hc]
  exact comparePrefixCached_eq g a b c K.cin K.flag K.high as bs cs v he srcND ag
    (layout_control_cin K g hn) ciSrc bg bSrc hg hiSrc chi
    (heads_nodup a b c K.cin as bs cs H) (right_nodup a b c K.cin as bs cs H)
    (left_outside a b c K.cin as bs cs H) hiOut s m sa hc0 ph

theorem comparePrefixOld_support (g cin flag : Wire) (src out carry : List Wire) (v : Nat)
    (hso : src.length=out.length) (hco : carry.length=out.length) :
    wires (comparePrefixOld g src out carry cin flag v)⊆(g::flag::cin::(src++out++carry)).toFinset := by
  let T:=(g::flag::cin::(src++out++carry)).toFinset
  have hs:src.toFinset⊆T:=by
    intro q h
    simp only [List.mem_toFinset] at h
    simp only [T,List.mem_toFinset,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
  have hm:wires (maskedConstant g src v)⊆T:=by
    intro q h
    have H:=maskedConstant_wires_subset g src v h
    simp only [List.mem_toFinset,List.mem_cons] at H
    rcases H with H|H
    · simp [T,H]
    · exact hs (List.mem_toFinset.mpr H)
  have hc:wires (compareLt none src out carry cin flag)⊆T:=by
    rw [(compareLt_wires none src out carry cin flag hso hco).1]
    intro q h
    simp only [T,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    exact Or.inr h
  simp only [comparePrefixOld,loadNot,unloadNot,wires_append,notRegister_wires]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset hm hs) hc) (Finset.union_subset hs hm)

theorem put_reg (r : List Wire) (s : State) (q : Wire) (v : Bool) (hq:q∉r) :
    regValue r (put s q v).basis=regValue r s.basis := by
  apply regValue_congr
  intro w hw
  have ne:w≠q:=by intro e;exact hq (e ▸ hw)
  simp [put,writeBit,ne]

theorem cachedPrefix_after_compute (K : MeasuredCanonicalModLayout) (g : Wire) (hw : K.Widths 256)
    (hn : (g::K.wires).Nodup) (v : Nat) (he:v%2=1) (s : State) (m : List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false) :
    run ([.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) m s=
      put (run (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) m s)
        K.high (s.basis g && s.basis (EntryFuse.lowBit K)) := by
  have free:K.high∉g::K.flag::K.cin::(K.src++K.out++K.carry):=by
    intro h
    have P:=List.count_pos_iff.mpr h
    have C:=List.nodup_iff_count.mp hn K.high
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,if_true] at C P
    omega
  have hg:K.high≠g:=by intro e;exact free (by simp [e])
  have hci:K.cin≠K.high:=by intro e;exact free (by simp [e])
  have hsrc:K.high∉K.src:=by
    intro h;exact free (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))))
  have hout:K.high∉K.out:=by
    intro h;exact free (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h)))))
  have hlb':EntryFuse.lowBit K≠K.high:=by
    intro e
    apply hout
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    rw [←e]
    simp [EntryFuse.lowBit,h]
  have outside:K.high∉wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v):=by
    intro h
    exact free (List.mem_toFinset.mp (comparePrefixOld_support g K.cin K.flag K.src K.out K.carry v
      (hw.src.trans hw.out.symm) (hw.carry.trans hw.out.symm) h))
  let A:=s.basis g && s.basis (EntryFuse.lowBit K)
  have pre:run [.CCX g (EntryFuse.lowBit K) K.high] m s=put s K.high A:=by
    simp [run,put,A,hh0]
  rw [run_append,run_take]
  simp only [measurementCount,List.drop_zero]
  rw [pre,cached_layout_eq K g hw hn v he (put s K.high A) m
    ((put_reg K.src s K.high A hsrc).trans hs0)
    (by simp [put,writeBit,hci,hc0])
    (by simp [put,writeBit,hg.symm,hlb',A])]
  exact run_put _ m s K.high A outside

def moveCached (h a : Wire) : Program := [.CX h a,.CX a h,.CX h a]

theorem moveCached_eq (h a : Wire) (hne:a≠h) (s : State) (m : List Bool) (A : Bool)
    (hh:s.basis h=false) (ha:s.basis a=false) :
    run (moveCached h a) m (put s h A)=put s a A := by
  apply State.extensionality
  · rfl
  funext q
  by_cases hq:q=h
  · subst q;cases A <;> simp [moveCached,run,put,writeBit,Function.update,hne,hne.symm,hh,ha]
  · by_cases hqa:q=a
    · subst q;cases A <;> simp [moveCached,run,put,writeBit,Function.update,hne,hne.symm,hh,ha]
    · simp [moveCached,run,put,writeBit,Function.update,hq,hqa]

theorem signStage_outside (K : MeasuredCanonicalModLayout) (g q : Wire) (k : Nat)
    (hw:K.Widths 256) (qo:q∉K.out) (qg:q≠g) (qf:q≠K.flag) (qh:q≠K.high) :
    q∉wires (ExitFusionResearch.signStage K g k) := by
  have lb:EntryFuse.lowBit K∈K.out:=by
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,h]
  have sb:EntryFuse.sign K∈K.out:=by
    rw [show K.out=EntryFuse.lowOut K++[EntryFuse.sign K] from (EntryFuse.word_split K.out hw.out).symm]
    simp
  have ql:q≠EntryFuse.lowBit K:=fun e=>qo (e ▸ lb)
  have qs:q≠EntryFuse.sign K:=fun e=>qo (e ▸ sb)
  have ql':q≠ExitFusionResearch.lowBit K:=ql
  have qs':q≠ExitFusionResearch.sign K:=qs
  simp only [ExitFusionResearch.signStage,wires_append]
  rw [(rotate_wires K.out).1]
  unfold ExitFusionResearch.parityControl
  split_ifs <;> simp [wires,Instr.wires,hw.out,qo,qg,qf,qh,ql',qs']

theorem append_eq_states (P R Q : Program) (s t : State) (m : List Bool)
    (count:measurementCount P=measurementCount R) (equal:run P m s=run R m t) :
    run (P++Q) m s=run (R++Q) m t := by
  simp only [run_append,run_take]
  rw [count,equal]

theorem cached_stage_eq (S Q : Program) (h a g b f : Wire) (hne:a≠h) (hfa:f≠a)
    (s : State) (m : List Bool) (A : Bool) (hh:s.basis h=false) (ha:s.basis a=false)
    (outside:a∉wires S)
    (product:((run S m s).basis g && (run S m s).basis b)=(A ^^ (run S m s).basis f)) :
    run (moveCached h a++S++[.CX f a]++Q) m (put s h A)=
      run (S++[.CCX g b a]++Q) m s := by
  have kept:(run S m s).basis a=false:=(run_preserves_outside S m s a outside).trans ha
  have e:run (moveCached h a++S++[.CX f a]) m (put s h A)=run (S++[.CCX g b a]) m s:=by
    simp only [List.append_assoc,run_append,run_take]
    have z:measurementCount (moveCached h a)=0:=rfl
    simp only [z,List.drop_zero]
    rw [moveCached_eq h a hne s m A hh ha,run_put S m s a A outside]
    exact cached_flag_eq g b f a hfa (run S m s) _ A kept product
  apply append_eq_states _ _ Q (put s h A) s m
  · simp [measurementCount_append,moveCached,measurementCount]
  · exact e

def evenBody (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  moveCached K.high (EntryFuse.alpha K)++ExitFusionResearch.signStage K g k++
    [.CX K.flag (EntryFuse.alpha K),.CCX K.flag (EntryFuse.sign K) K.high]++
    EntryFuse.addClearBeta K g EntryFuseArithmetic.complement k++
    EntryFuse.clearWrap K g EntryFuseArithmetic.complement k

theorem evenBody_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (he:k%2=0) (rest:List Wire) (hout:K.out=EntryFuse.lowBit K::rest)
    (s:State) (m:List Bool) (hh:s.basis K.high=false) (ha:regValue K.src s.basis=0)
    (wrap:s.basis K.flag=true→s.basis g=true) :
    run (evenBody K g k) m
      (put s K.high (s.basis g && s.basis (EntryFuse.lowBit K)))=
      run (EntryFuse.entryBody K g k rest) m s := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=
    EntryFuse.controls_distinct K g hn hw
  have go:g∉K.out:=EntryFuse.controls_fullOut K g hn hw g (by simp [EntryFuse.controls]) hgS
  have fo:K.flag∉K.out:=EntryFuse.controls_fullOut K g hn hw K.flag (by simp [EntryFuse.controls]) hfS
  have ao:EntryFuse.alpha K∉K.out:=EntryFuse.controls_fullOut K g hn hw (EntryFuse.alpha K)
    (by simp [EntryFuse.controls]) haS
  have ho:K.high∉K.out:=EntryFuse.controls_fullOut K g hn hw K.high (by simp [EntryFuse.controls]) hhS
  have ac:EntryFuse.alpha K∈K.src:=by
    rw [show K.src=EntryFuse.lowSrc K++[EntryFuse.alpha K] from (EntryFuse.word_split K.src hw.src).symm]
    simp
  have a0:s.basis (EntryFuse.alpha K)=false:=(regValue_zero K.src s.basis).mp ha _ ac
  have outND:K.out.Nodup:=EntryFuse.out_nodup K g hn
  have sign:=EntryFuse.signStage_correct (EntryFuse.lowBit K) g K.flag K.high rest k
    (by rw [←hout];exact hw.out) (by rw [←hout];exact outND)
    (by rw [←hout];exact ho) (by rw [←hout];exact go) (by rw [←hout];exact fo)
    hgH hfH s m hh
  let S:=ExitFusionResearch.signStage K g k
  have eqS:=ExitFusionProof.signStage_eq K g k rest hout
  have tg:(run S m s).basis g=s.basis g:=by
    simpa only [S,eqS,←hout] using sign.2.2.2.2 g (by rw [←hout];exact go) hgH
  have tf:(run S m s).basis K.flag=s.basis K.flag:=by
    simpa only [S,eqS,←hout] using sign.2.2.2.2 K.flag (by rw [←hout];exact fo) hfH
  have ts:(run S m s).basis (EntryFuse.sign K)=
      (s.basis (EntryFuse.lowBit K) ^^ s.basis K.flag):=by
    have ne:¬k%2=1:=by omega
    simpa only [S,eqS,←hout,EntryFuse.sign,ne,if_false,Bool.xor_false] using sign.2.2.1
  have product:((run S m s).basis g && (run S m s).basis (EntryFuse.sign K))=
      ((s.basis g && s.basis (EntryFuse.lowBit K)) ^^ (run S m s).basis K.flag):=by
    rw [tg,tf,ts]
    cases hg:s.basis g <;> cases hb:s.basis (EntryFuse.lowBit K) <;>
      cases hf:s.basis K.flag <;> simp_all
  have outA:EntryFuse.alpha K∉wires S:=signStage_outside K g (EntryFuse.alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  have E:=cached_stage_eq S
    ([.CCX K.flag (EntryFuse.sign K) K.high]++EntryFuse.addClearBeta K g EntryFuseArithmetic.complement k++
      EntryFuse.clearWrap K g EntryFuseArithmetic.complement k)
    K.high (EntryFuse.alpha K) g (EntryFuse.sign K) K.flag hhA.symm hfA s m
    (s.basis g && s.basis (EntryFuse.lowBit K)) hh a0 outA product
  simpa only [evenBody,EntryFuse.entryBody,EntryFuse.entryMiddle,EntryFuse.middle,EntryFuse.makeFlags,
    S,eqS,List.append_assoc,List.cons_append,List.nil_append] using E

theorem cached_prefix_measurements (K : MeasuredCanonicalModLayout) (g : Wire) (hw:K.Widths 256) (v:Nat) :
    measurementCount ([.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v)=
      measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=(compareLtCached_counts a b c as bs cs K.cin K.flag K.high).2
  simp only [hs,ho,hc,comparePrefixCached,comparePrefixOld,measurementCount_append,measurementCount]
  rw [H]
  omega

def entryEven (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat) : Program :=
  [.CCX g (EntryFuse.lowBit K) K.high]++
    comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (EntryFuseArithmetic.complement+k)++
    evenBody K g k

theorem entryEven_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (he:k%2=0) (hy:Y<EntryFuseArithmetic.prime) (hk:k<EntryFuseArithmetic.prime)
    (s:State) (m:List Bool) (hY:regValue K.out s.basis=Y) (hs:regValue K.src s.basis=0)
    (hf:s.basis K.flag=false) (hh:s.basis K.high=false) (hc:s.basis K.cin=false)
    (carry:∀q∈K.carry,s.basis q=false) :
    run (entryEven K g k) m s=run (EntryFuse.entry K g EntryFuseArithmetic.complement k) m s := by
  let c:=EntryFuseArithmetic.complement
  let P:=[Instr.CCX g (EntryFuse.lowBit K) K.high]++
    comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag (c+k)
  let O:=comparePrefixOld g K.src K.out K.carry K.cin K.flag (c+k)
  let n:=measurementCount O
  let t:=run O (m.take n) s
  have cmp:measurementCount P=measurementCount O:=cached_prefix_measurements K g hw (c+k)
  have cp:(c+k)%2=1:=by
    have cmod:c%2=1:=by norm_num [c,EntryFuseArithmetic.complement]
    omega
  have cachedRun:run P (m.take n) s=put t K.high (s.basis g && s.basis (EntryFuse.lowBit K)):=
    cachedPrefix_after_compute K g hw hn (c+k) cp s (m.take n) hs hc hh
  have pc:EntryFuseArithmetic.prime+c=2^256:=by norm_num [c,EntryFuseArithmetic.prime,
    EntryFuseArithmetic.modulus,EntryFuseArithmetic.complement]
  have initial:FastConst.Frame K s.basis 0 Y false s.basis:=⟨hs,hY,hf,by intro q hq;rfl⟩
  have pre:=EntryFuse.comparePrefix_correct hn 256 hw s.basis carry hc c EntryFuseArithmetic.prime k Y
    pc hk hy s (m.take n) initial
  have oe:O=EntryFuse.comparePrefix K g c k:=by
    simp only [O,comparePrefixOld,loadNot,unloadNot,EntryFuse.comparePrefix,List.append_assoc]
  rw [←oe] at pre
  change t.phase=s.phase ∧ FastConst.Frame K s.basis 0 Y
    (if s.basis g then decide (EntryFuseArithmetic.prime≤Y+k) else false) t.basis at pre
  have tg:t.basis g=s.basis g:=pre.2.2.2.2 g (FastConst.g_not_mutable hn)
  have th:t.basis K.high=false:=(pre.2.2.2.2 K.high
    (FastConst.fixed_not_mutable hn K.high (by simp))).trans hh
  have wrap:t.basis K.flag=true→t.basis g=true:=by
    intro hf'
    rw [tg]
    have f:=pre.2.2.2.1
    cases hg:s.basis g <;> simp_all
  have lb:EntryFuse.lowBit K∈K.out:=by
    obtain ⟨b,bs,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [EntryFuse.lowBit,h]
  have tv:t.basis (EntryFuse.lowBit K)=s.basis (EntryFuse.lowBit K):=
    (regValue_eq_iff K.out t.basis s.basis).mp (pre.2.2.1.trans hY.symm) _ lb
  rw [←tg,←tv] at cachedRun
  obtain ⟨rest,hout⟩:=EntryFuse.out_shape K hw
  have decomp:=ParityConvert.old_entry_split K g hw k
  rw [decomp]
  change run (P++evenBody K g k) m s=run (O++EntryFuse.entryBody K g k K.out.tail) m s
  simp only [run_append,cmp]
  change run (evenBody K g k) (m.drop n) (run P (m.take n) s)=
    run (EntryFuse.entryBody K g k K.out.tail) (m.drop n) t
  rw [cachedRun]
  exact evenBody_eq K g k hw hn he K.out.tail
    (by rw [hout];rfl) t (m.drop n) th pre.2.1 wrap

theorem evenBody_counts (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (rest:List Wire) (hout:K.out=EntryFuse.lowBit K::rest) :
    toffoliCount (evenBody K g k)+1=toffoliCount (EntryFuse.entryBody K g k rest) ∧
    measurementCount (evenBody K g k)=measurementCount (EntryFuse.entryBody K g k rest) ∧
    gateSlots (evenBody K g k)=gateSlots (EntryFuse.entryBody K g k rest)+3 := by
  have e:=ExitFusionProof.signStage_eq K g k rest hout
  simp only [evenBody,EntryFuse.entryBody,EntryFuse.entryMiddle,EntryFuse.middle,EntryFuse.makeFlags,
    toffoliCount_append,measurementCount_append,gateSlots_append,e]
  simp only [moveCached,toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots]
  omega

theorem retain_product (g b f a h : Wire) (ga:g≠a) (ba:b≠a) (_fa:f≠a) (ha:h≠a)
    (s:State) (m n:List Bool) (hh:s.basis h=false) (known:s.basis a=(s.basis g && s.basis b)) :
    run [.CX f a,.measureX h [] []] m s=
      put (run [.measureX a [] [.CZ g b]] n s) a
        ((s.basis g && s.basis b) ^^ s.basis f) := by
  rw [EntryFuse.erase_and g b a ga ba s n known]
  apply State.extensionality
  · simp [run,measureAndCorrect,correct,put,writeBit,ha,hh]
  funext q
  by_cases qa:q=a
  · subst q
    simp [run,measureAndCorrect,correct,put,writeBit,Function.update,ha,ha.symm,known]
  · by_cases qh:q=h
    · subst q
      simp [run,measureAndCorrect,correct,put,writeBit,Function.update,ha,hh]
    · simp [run,measureAndCorrect,correct,put,writeBit,Function.update,qa,qh]

theorem compareChainCached_slots (a b c : Wire) (as bs cs : List Wire) (cin target h : Wire) :
    gateSlots (compareChainCached (a::as) (b::bs) (c::cs) cin target h)+4=
      gateSlots (compareChain none (a::as) (b::bs) (c::cs) cin target) := by
  simp [compareChainCached,compareChain,majority,gateSlots_append,
    gateSlots,instructionSlots]
  omega

theorem cached_layout_counts (K : MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    let P:=[Instr.CCX g (EntryFuse.lowBit K) K.high]++
      comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v
    toffoliCount P=toffoliCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    measurementCount P=measurementCount (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) ∧
    gateSlots P+3=gateSlots (comparePrefixOld g K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have H:=compareChainCached_slots a b c as bs cs K.cin K.flag K.high
  have C:=compareChainCached_counts a b c as bs cs K.cin K.flag K.high
  simp only [hs,ho,hc,comparePrefixCached,comparePrefixOld,compareLtCached,compareLt,
    toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots] at *
  omega

theorem entryEven_counts (K : MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (entryEven K g k)+1=766 ∧ measurementCount (entryEven K g k)=767 ∧
    gateSlots (entryEven K g k)=gateSlots (EntryFuse.entry K g EntryFuseArithmetic.complement k) := by
  obtain ⟨rest,hout⟩:=EntryFuse.out_shape K hw
  have C:=cached_layout_counts K g hw (EntryFuseArithmetic.complement+k)
  have B:=evenBody_counts K g k rest hout
  have O:=EntryFuse.entry_counts K g EntryFuseArithmetic.complement k hw
  have split:=ParityConvert.old_entry_split K g hw k
  have tail:K.out.tail=rest:=by rw [hout];rfl
  rw [tail] at split
  have t:=congrArg toffoliCount split
  have m:=congrArg measurementCount split
  have slots:=congrArg gateSlots split
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at t m slots
  unfold entryEven
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  dsimp only at C
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append] at C
  omega

theorem move_borrow (a b cin c h : Wire) (hn:[a,b,cin,c].Nodup) (ch:c≠h)
    (s:State) (m:List Bool) (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run [.CX h c,.CX c h] m (put s h (!s.basis a && s.basis b))=
      run (borrowMajority a b cin c) m s := by
  rw [borrowMajority_correct a b cin c hn]
  apply State.extensionality
  · rfl
  funext q
  by_cases qc:q=c
  · subst q
    cases aa:s.basis a <;> cases bb:s.basis b <;>
      simp [run,put,writeBit,Function.update,ch,ch.symm,carryBit,hc,cz,aa,bb]
  · by_cases qh:q=h
    · subst q
      cases aa:s.basis a <;> cases bb:s.basis b <;>
        simp [run,put,writeBit,Function.update,ch,ch.symm,carryBit,hc,cz,hz,aa,bb]
    · simp [run,put,writeBit,Function.update,qc,qh]

def eraseLtMoved (x y carry : List Wire) (cin target h : Wire) : Program :=
  match x,y,carry with
  | a::a'::as,b::b'::bs,c::cs =>
      [.CX h c,.CX c h]++eraseLtChain (a'::as) (b'::bs) cs c target++eraseBorrow a b cin c
  | _,_,_ => eraseLtChain x y carry cin target

theorem eraseLtMoved_eq (a a' b b' c : Wire) (as bs cs:List Wire) (cin target h:Wire)
    (hn:[a,b,cin,c].Nodup) (ch:c≠h) (s:State) (m:List Bool)
    (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h) m
      (put s h (!s.basis a && s.basis b))=
      run (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) m s := by
  apply append_eq_states _ _ (eraseBorrow a b cin c) _ s m
  · simp [measurementCount_append,measurementCount,borrowMajority,majority]
  · apply append_eq_states _ _ (eraseLtChain (a'::as) (b'::bs) cs c target)
    · simp [measurementCount,borrowMajority,majority,measurementCount_append]
    · exact move_borrow a b cin c h hn ch s m hc cz hz

theorem cleanup_keep_product (K:MeasuredCanonicalModLayout) (g:Wire)
    (hgA:g≠EntryFuse.alpha K) (hsA:EntryFuse.sign K≠EntryFuse.alpha K) (hfA:K.flag≠EntryFuse.alpha K)
    (hgH:g≠K.high) (hsH:EntryFuse.sign K≠K.high) (hfH:K.flag≠K.high)
    (haH:EntryFuse.alpha K≠K.high) (s:State) (m n l:List Bool)
    (ha:s.basis (EntryFuse.alpha K)=false) (hh:s.basis K.high=false) :
    run [.CX K.flag (EntryFuse.alpha K),.measureX K.high [] []] l
      (run [.measureX K.high [] [.CZ K.flag (EntryFuse.sign K)]] n
        (run (EntryFuse.makeFlags K g) m s))=
      put s (EntryFuse.alpha K) ((s.basis g && s.basis (EntryFuse.sign K)) ^^ s.basis K.flag) := by
  let t:=run (EntryFuse.makeFlags K g) m s
  have mf:=EntryFuse.makeFlags_correct K g hgA hsA hfA haH s m ha hh
  have tg:t.basis g=s.basis g:=mf.2.2.2 g hgA hgH
  have tf:t.basis K.flag=s.basis K.flag:=mf.2.2.2 _ hfA hfH
  have ts:t.basis (EntryFuse.sign K)=s.basis (EntryFuse.sign K):=mf.2.2.2 _ hsA hsH
  have beta:t.basis K.high=(t.basis K.flag && t.basis (EntryFuse.sign K)):=by rw [mf.2.2.1,tf,ts]
  have erB:=EntryFuse.erase_and K.flag (EntryFuse.sign K) K.high hfH hsH t n beta
  let u:State:=⟨t.phase,writeBit t.basis K.high false⟩
  have keep (q:Wire) (hq:q≠K.high):u.basis q=t.basis q:=by simp [u,writeBit,hq]
  have alphaKnown:u.basis (EntryFuse.alpha K)=(u.basis g && u.basis (EntryFuse.sign K)):=by
    rw [keep _ haH,keep _ hgH,keep _ hsH,mf.2.1,tg,ts]
  have highZero:u.basis K.high=false:=by simp [u,writeBit]
  have eraseAll:=ExitFusionProof.cleanup_makeFlags_inverse K g hgA hsA hfA hgH hsH hfH haH s m n l ha hh
  change run _ l (run _ n t)=_ at eraseAll ⊢
  rw [erB] at eraseAll ⊢
  have retain:=retain_product g (EntryFuse.sign K) K.flag (EntryFuse.alpha K) K.high
    hgA hsA hfA haH.symm u l l highZero alphaKnown
  change run _ l u=_ at eraseAll ⊢
  rw [retain,eraseAll]
  rw [keep _ hgH,keep _ hsH,keep _ hfH,tg,ts,tf]

open EntryFuse ExitFusionProof EntryFuseArithmetic

def undoMiddleKeep (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) : Program :=
  [.CCX K.flag (EntryFuse.sign K) K.high]++ExitFusionResearch.table K g c k++
    mappedSub (mappedRead (EntryFuse.lowSrc K) false) (EntryFuse.lowOut K) (K.carry.take 254) K.cin++
    ExitFusionResearch.untabled K g c k++[.measureX K.high [] [.CZ K.flag (EntryFuse.sign K)],
      .CX K.flag (EntryFuse.alpha K),.measureX K.high [] []]

private theorem run_three (A B C : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 : List Bool, run (A++B++C) m s=run C m3 (run B m2 (run A m1 s)) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    (m.drop (measurementCount A)).drop (measurementCount B),by simp only [List.append_assoc,run_append]⟩
private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool, run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩

theorem undoMiddleKeep_middle_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (c k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256)
    (s : State) (m n : List Bool)
    (ha0 : s.basis (alpha K)=false) (hh0 : s.basis K.high=false)
    (hcarry : ∀q∈K.carry.take 254,s.basis q=false) (hcin : s.basis K.cin=false) :
    run (undoMiddleKeep K g c k) n (run (middle K g c k) m s)=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have low := low_widths K hw
  have cs (q : Wire) (h : q∈controls K g) : q∉lowSrc K := controls_src K g hn hw q h
  have co (q : Wire) (h : q∈controls K g) : q∉lowOut K := controls_out K g hn hw q h
  have cc (q : Wire) (h : q∈controls K g) : q∉K.carry.take 254 := carry_away K g hn hw q h
  have hctrlSrc : ∀e∈entryMasks K g c k,e.1∉lowSrc K := by
    intro e he; exact cs _ ((mask_controls K g c k).1 e he)
  have hctrlOut : ∀e∈entryMasks K g c k,e.1∉lowOut K := by
    intro e he; exact co _ ((mask_controls K g c k).1 e he)
  have haway : ∀q∈mappedWires (mappedRead (lowSrc K) false),q∉K.cin::(lowOut K++K.carry.take 254) := by
    simpa only [mappedRead_wires] using src_away K g hn hw
  let M := makeFlags K g
  let T := tableAdd K g c k
  let E : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  obtain ⟨m1,m2,m3,forward⟩ := run_three M T E m s
  have mf := makeFlags_correct K g hgA (Ne.symm haS) hfA (Ne.symm hhA) s m1 ha0 hh0
  let s1 := run M m1 s
  let s2 := run T m2 s1
  let s3 := run E m3 s2
  have frame (q : Wire) (hqa : q≠alpha K) (hqh : q≠K.high) : s1.basis q=s.basis q := mf.2.2.2 q hqa hqh
  have clean : ∀q∈K.carry.take 254,s1.basis q=false := by
    intro q hq
    have qa : q≠alpha K := fun e => cc (alpha K) (by simp [controls]) (e ▸ hq)
    have qh : q≠K.high := fun e => cc K.high (by simp [controls]) (e ▸ hq)
    exact (frame q qa qh).trans (hcarry q hq)
  have ci : s1.basis K.cin=false := (frame _ hcA (Ne.symm hhC)).trans hcin
  have ad := tableAdd_correct K g c k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1,low.2.1]) (by rw [low.2.2,low.2.1]) hctrlSrc hctrlOut s1 m2 clean ci
  have f2 : s2.basis K.flag=s.basis K.flag :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ hfA hfH)
  have sg2 : s2.basis (sign K)=s.basis (sign K) :=
    (ad.2.2 _ (co _ (by simp [controls]))).trans (frame _ (Ne.symm haS) (Ne.symm hhS))
  have beta : s2.basis K.high=(s2.basis K.flag && s2.basis (sign K)) := by
    rw [ad.2.2 _ (co _ (by simp [controls])),mf.2.2.1,f2,sg2]
  let A : Program := [.CCX K.flag (sign K) K.high]
  let B := tableSub K g c k
  let C : Program := [.measureX K.high [] [.CZ K.flag (sign K)]]
  let D : Program := [.CX K.flag (alpha K),.measureX K.high [] []]
  obtain ⟨n1,n2,n3,n4,inverse⟩ := run_four A B C D n s3
  have restore : run A n1 s3=s2 := recompute_measured_and K.flag (sign K) K.high hfH
    (Ne.symm hhS) s2 m3 n1 beta
  have sub := tableSub_tableAdd_inverse K g c k (lowSrc_nodup K g hn hw) (adder_nodup K g hn hw)
    haway (by rw [low.1,low.2.1]) (by rw [low.2.2,low.2.1]) hctrlSrc s1 m2 n2 clean ci
  have goal : run (A++B++C++D) n (run (M++T++E) m s)=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag) := by
    rw [forward]
    change run (A++B++C++D) n s3=put s (alpha K) ((s.basis g && s.basis (sign K)) ^^ s.basis K.flag)
    rw [inverse,restore,sub]
    exact cleanup_keep_product K g hgA (Ne.symm haS) hfA hgH (Ne.symm hhS) hfH
      (Ne.symm hhA) s m1 n3 n4 ha0 hh0
  simpa only [middle,addClearBeta,undoMiddleKeep,tableSub,
    M,T,E,A,B,C,D,List.append_assoc] using goal


theorem undo_entryMiddleKeep_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k%2=0)
    (rest : List Wire) (hout : K.out=lowBit K::rest)
    (s : State) (m n r : List Bool) (hsrc : regValue K.src s.basis=0)
    (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) (wrap:s.basis K.flag=true→s.basis g=true) :
    run (ExitFusionResearch.signStage K g k).reverse r
      (run (undoMiddleKeep K g complement k) n
        (run (entryMiddle K g k rest) m s))=put s (alpha K) (s.basis g && s.basis (lowBit K)) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩ :=
    controls_distinct K g hn hw
  have cio : K.cin∉K.out := controls_fullOut K g hn hw K.cin (by simp [controls]) hcS
  have ho : K.high∉K.out := controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have go : g∉K.out := controls_fullOut K g hn hw g (by simp [controls]) hgS
  have fo : K.flag∉K.out := controls_fullOut K g hn hw K.flag (by simp [controls]) hfS
  have am : alpha K∈K.src := by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm]; simp
  have ao : alpha K∉K.out := src_fullOut K g hn _ am
  have a0 : s.basis (alpha K)=false := (regValue_zero K.src s.basis).mp hsrc _ am
  let P := ExitFusionResearch.signStage K g k
  have proper := ExitFusionResearch.signStage_proper K g k hn hw
  have eqP := signStage_eq K g k rest hout
  have zero : measurementCount P=0 := properProgram_measurementCount P proper
  let t := run P [] s
  have first := signStage_correct (lowBit K) g K.flag K.high rest k
    (by rw [←hout]; exact hw.out) (by rw [←hout]; exact FastConst.out_nodup hn)
    (by rw [←hout]; exact ho) (by rw [←hout]; exact go) (by rw [←hout]; exact fo)
    hgH hfH s [] hh
  rw [←eqP] at first
  rw [←hout] at first
  have high : t.basis K.high=false := first.2.2.2.1
  have alphaClean : t.basis (alpha K)=false :=
    (first.2.2.2.2 _ ao (Ne.symm hhA)).trans a0
  have carry : ∀q∈K.carry.take 254,t.basis q=false := by
    intro q hq
    have mem := List.mem_of_mem_take hq
    have qo := carry_fullOut K g hn q mem
    have qh : q≠K.high := by
      intro e
      have bad := carry_away K g hn hw K.high (by simp [controls])
      exact bad (e ▸ hq)
    exact (first.2.2.2.2 q qo qh).trans (hcarry q mem)
  have ci : t.basis K.cin=false := (first.2.2.2.2 _ cio (Ne.symm hhC)).trans hcin
  have middle := undoMiddleKeep_middle_inverse K g complement k hn hw t m n alphaClean high carry ci
  rw [entryMiddle,←eqP,run_append,zero,List.take_zero,List.drop_zero]
  rw [middle]
  have outA:alpha K∉wires P.reverse:=by
    rw [wires_reverse]
    exact signStage_outside K g (alpha K) k hw ao hgA.symm hfA.symm hhA.symm
  rw [run_put P.reverse r t (alpha K) _ outA,run_reverse_proper P proper s [] r]
  have tg:t.basis g=s.basis g:=first.2.2.2.2 g go hgH
  have tf:t.basis K.flag=s.basis K.flag:=first.2.2.2.2 K.flag fo hfH
  have ts:t.basis (sign K)=(s.basis (lowBit K) ^^ s.basis K.flag):=by
    have ne:¬k%2=1:=by omega
    simpa only [ne,if_false,Bool.xor_false] using first.2.2.1
  rw [tg,tf,ts]
  congr 1
  cases hg:s.basis g <;> cases hb:s.basis (lowBit K) <;>
    cases hf:s.basis K.flag <;> simp_all


theorem eraseLtMoved_measurements (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    measurementCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)=
      measurementCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  simp [eraseLtMoved,eraseLtChain,measurementCount_append,borrowMajority,majority,measurementCount]

def erasePrefixMoved (g h:Wire) (src out carry:List Wire) (cin flag:Wire) (v:Nat) : Program :=
  loadNot g src v++eraseLtMoved src out carry cin flag h++unloadNot g src v

theorem erasePrefixMoved_eq (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat)
    (he:v%2=1) (hn:(a::a'::as).Nodup) (hag:a≠g)
    (hcg:cin≠g) (hcs:cin∉a::a'::as) (hbg:b≠g) (hbs:b∉a::a'::as)
    (hhg:h≠g) (hhs:h∉a::a'::as) (ch:c≠h) (ccg:c≠g) (ccs:c∉a::a'::as)
    (hport:[a,b,cin,c].Nodup) (s:State) (m:List Bool)
    (ha:s.basis a=false) (hc:s.basis cin=false) (cz:s.basis c=false) (hz:s.basis h=false) :
    run (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m
      (put s h (s.basis g && s.basis b))=
      run (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v) m s := by
  let P:=loadNot g (a::a'::as) v
  let t:=run P m s
  have outP:h∉wires P:=by
    intro H
    simp only [P,loadNot,wires_append,notRegister_wires,Finset.mem_union,List.mem_toFinset] at H
    rcases H with H|H
    · have R:=maskedConstant_wires_subset g (a::a'::as) v H
      simp only [List.mem_toFinset,List.mem_cons] at R
      exact R.elim hhg (fun r=>hhs (by simpa only [List.mem_cons] using r))
    · exact hhs H
  have ac:t.basis a= !s.basis g:=load_odd_not g a (a'::as) v he hn hag s m ha
  have cb:t.basis b=s.basis b:=loadNot_outside g b _ v s m hbg hbs
  have ci:t.basis cin=false:=(loadNot_outside g cin _ v s m hcg hcs).trans hc
  have ca:t.basis c=false:=(loadNot_outside g c _ v s m ccg ccs).trans cz
  have hi:t.basis h=false:=(loadNot_outside g h _ v s m hhg hhs).trans hz
  have product:(!t.basis a && t.basis b)=(s.basis g && s.basis b):=by rw [ac,cb,Bool.not_not]
  apply append_eq_states _ _ (unloadNot g (a::a'::as) v) _ s m
  · simp only [measurementCount_append]
    rw [eraseLtMoved_measurements]
  · simp only [run_append,run_take]
    have zero:measurementCount P=0:=by simp [P,loadNot,measurementCount_append,
      (maskedConstant_counts _ _ _).2,(notRegister_counts _).2]
    change run (eraseLtMoved _ _ _ cin flag h) (m.drop (measurementCount P)) (run P m _)=
      run (eraseLtChain _ _ _ cin flag) (m.drop (measurementCount P)) (run P m s)
    rw [zero,List.drop_zero,run_put P m s h _ outP,←product]
    exact eraseLtMoved_eq a a' b b' c as bs cs cin flag h hport ch t m ci ca hi

theorem eraseMoved_layout_eq (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat) (he:v%2=1) (s:State) (m:List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false)
    (hcarry:∀q∈K.carry,s.basis q=false) :
    run (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v) m
      (put s K.high (s.basis g && s.basis (lowBit K)))=
      run (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) m s := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have H:=layout_core_take_nodup K g 255 hn
  rw [hs,ho,hc] at H
  have N:(g::K.high::K.cin::(K.src++K.out++K.carry.take 255)).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have C:=List.nodup_iff_count.mp hn q
    have T:=(List.take_sublist 255 K.carry).count_le q
    simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at C ⊢
    omega
  rw [hs,ho,hc] at N
  obtain ⟨gf,N⟩:=List.nodup_cons.mp N
  obtain ⟨hf,N⟩:=List.nodup_cons.mp N
  have csFree:=(List.nodup_cons.mp H).1
  have srcND:(a::a'::as).Nodup:=H.of_cons.of_append_left.of_append_left
  have ag:a≠g:=by intro e;exact gf (by simp [←e])
  have bg:b≠g:=by intro e;exact gf (by simp [←e])
  have hg:K.high≠g:=by intro e;exact gf (by simp [←e])
  have cg:c≠g:=by intro e;exact gf (by simp [←e])
  have ciSrc:K.cin∉a::a'::as:=by
    intro h;exact csFree (List.mem_append_left _ (List.mem_append_left _ h))
  have hiSrc:K.high∉a::a'::as:=by
    intro h;exact hf (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))
  have chi:c≠K.high:=by intro e;exact hf (by simp [←e])
  have bSrc:b∉a::a'::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons.of_append_left).2.2 b h b (by simp) rfl
  have cSrc:c∉a::a'::as:=by
    intro h
    exact (List.nodup_append.mp H.of_cons).2.2 c (List.mem_append_left _ h) c (by simp) rfl
  have sa:s.basis a=false:=(regValue_zero K.src s.basis).mp hs0 a (by rw [hs];simp)
  have cz:s.basis c=false:=hcarry c (List.mem_of_mem_take (by rw [hc];simp))
  have lb:lowBit K=b:=by simp [lowBit,ho]
  rw [lb,hs,ho,hc]
  exact erasePrefixMoved_eq g a a' b b' c K.cin K.flag K.high as bs cs v he srcND ag
    (layout_control_cin K g hn) ciSrc bg bSrc hg hiSrc chi cg cSrc
    (heads_nodup a b c K.cin (a'::as) (b'::bs) cs H) s m sa hc0 cz hh0

def eraseInputMoved (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  moveCached (alpha K) K.high++
    erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)

theorem eraseInputMoved_eq (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (k:Nat) (he:k%2=0) (s:State) (m:List Bool)
    (hs0:regValue K.src s.basis=0) (hc0:s.basis K.cin=false) (hh0:s.basis K.high=false)
    (hcarry:∀q∈K.carry,s.basis q=false) :
    run (eraseInputMoved K g k) m (put s (alpha K) (s.basis g && s.basis (lowBit K)))=
      run (ExitFusionResearch.eraseInputWrap K g complement k) m s := by
  have pc:(complement+k)%2=1:=by
    have C:complement%2=1:=by norm_num [complement]
    omega
  have hhA:K.high≠alpha K:=(EntryFuse.controls_distinct K g hn hw).2.2.2.2.2.2.2.2.2.2.1
  have am:alpha K∈K.src:=by
    rw [show K.src=lowSrc K++[alpha K] from (word_split K.src hw.src).symm];simp
  have az:s.basis (alpha K)=false:=(regValue_zero K.src s.basis).mp hs0 _ am
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [←old]
  unfold eraseInputMoved
  rw [run_append,run_take]
  have z:measurementCount (moveCached (alpha K) K.high)=0:=rfl
  rw [z,List.drop_zero,moveCached_eq (alpha K) K.high hhA s m _ az hh0]
  exact eraseMoved_layout_eq K g hw hn (complement+k) pc s m hs0 hc0 hh0 hcarry

def exitEven (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) : Program :=
  ExitFusionResearch.recoverWrap K g complement k++undoMiddleKeep K g complement k++
    (ExitFusionResearch.signStage K g k).reverse++eraseInputMoved K g k

theorem exitEven_entry_inverse (K : MeasuredCanonicalModLayout) (g : Wire) (k Y : Nat)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k%2=0)
    (s : State) (m n : List Bool) (hY : regValue K.out s.basis=Y)
    (hy : Y<prime) (hk : k<prime) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitEven K g k) n (run (EntryFuse.entry K g complement k) m s)=s := by
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
  let B := undoMiddleKeep K g complement k
  let C := (ExitFusionResearch.signStage K g k).reverse
  let D := eraseInputMoved K g k
  obtain ⟨n1,n2,n3,n4,parts⟩ := run_four A B C D n (run (entryBody K g k rest) m2 t)
  have recover : run A n1 (run (entryBody K g k rest) m2 t)=
      run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t :=
    recover_entryBody K g k Y hn hw rest hout t m2 n1 pre.2.2.1 hy hk pre.2.1 th tcin tcarry tflag
  have wrap:t.basis K.flag=true→t.basis g=true:=by
    intro f
    rw [tg]
    have tf:=pre.2.2.2.1
    cases G:s.basis g <;> simp_all
  have undo : run C n3 (run B n2
      (run (entryMiddle K g k rest) (m2.take (measurementCount (entryMiddle K g k rest))) t))=put t (alpha K) (t.basis g && t.basis (lowBit K)) :=
    undo_entryMiddleKeep_inverse K g k hn hw he rest hout t _ n2 n3 pre.2.1 th tcin tcarry wrap
  have erase : run D n4 (put t (alpha K) (t.basis g && t.basis (lowBit K)))=s :=
    (eraseInputMoved_eq K g hw hn k he t n4 pre.2.1 tcin th tcarry).trans
      (eraseInput_entryCompare_inverse K g k Y hn hw s m1 n4 hY hy hk hsrc hf hcin hcarry)
  have decomp : EntryFuse.entry K g complement k=entryCompare K g complement k++entryBody K g k rest := by
    rw [entry_decompose K g complement k rest hout]
    simp only [entryBody,entryMiddle,List.append_assoc]
  rw [decomp,run_append]
  change run (A++B++C++D) n (run (entryBody K g k rest) m2 t)=s
  rw [parts,recover,undo,erase]


open Secp256k1 BalancedField
theorem exitEven_field_correct (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k.val%2=0)
    (s : State) (m : List Bool) (hH : regValue K.out s.basis=centerWord H)
    (hsrc : regValue K.src s.basis=0) (hf : s.basis K.flag=false) (hh : s.basis K.high=false)
    (hcin : s.basis K.cin=false) (hcarry : ∀q∈K.carry,s.basis q=false) :
    let v := run (exitEven K g k.val) m s
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
  have inv := exitEven_entry_inverse K g k.val Y.val hn hw he a [] m av hy hk aSrc af ah ac aCarry
  rw [preimage] at inv
  dsimp only
  rw [inv]
  exact ⟨ap,av,outside⟩


theorem exitEven_eq (K : MeasuredCanonicalModLayout) (g : Wire) (k H : Fp)
    (hn : (g::K.wires).Nodup) (hw : K.Widths 256) (he:k.val%2=0) (s : State) (m n : List Bool)
    (hH : regValue K.out s.basis=centerWord H) (hsrc : regValue K.src s.basis=0)
    (hf : s.basis K.flag=false) (hh : s.basis K.high=false) (hcin : s.basis K.cin=false)
    (hcarry : ∀q∈K.carry,s.basis q=false) :
    run (exitEven K g k.val) m s=run (ExitFusionResearch.exit K g complement k.val) n s := by
  have a:=exitEven_field_correct K g k H hn hw he s m hH hsrc hf hh hcin hcarry
  have b:=ExitFusionProof.exit_field_correct K g k H hn hw s n hH hsrc hf hh hcin hcarry
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq:q∈K.out
    · exact (regValue_eq_iff K.out _ _).mp (a.2.1.trans b.2.1.symm) q hq
    · exact (a.2.2 q hq).trans (b.2.2 q hq).symm



theorem eraseLtMoved_counts (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    toffoliCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)+1=
      toffoliCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    measurementCount (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)=
      measurementCount (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) ∧
    gateSlots (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)+6=
      gateSlots (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target) := by
  simp [eraseLtMoved,eraseLtChain,borrowMajority,majority,toffoliCount_append,measurementCount_append,
    gateSlots_append,toffoliCount,measurementCount,gateSlots,instructionSlots]
  omega

theorem eraseMoved_layout_counts (K:MeasuredCanonicalModLayout) (g h:Wire) (hw:K.Widths 256) (v:Nat) :
    toffoliCount (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)+1=
      toffoliCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    measurementCount (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)=
      measurementCount (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) ∧
    gateSlots (erasePrefixMoved g h K.src K.out (K.carry.take 255) K.cin K.flag v)+6=
      gateSlots (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have H:=eraseLtMoved_counts a a' b b' c as bs cs K.cin K.flag h
  simp only [hs,ho,hc,erasePrefixMoved,erasePrefixOld,toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem eraseInputMoved_counts (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (eraseInputMoved K g k)+1=toffoliCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    measurementCount (eraseInputMoved K g k)=measurementCount (ExitFusionResearch.eraseInputWrap K g complement k) ∧
    gateSlots (eraseInputMoved K g k)+3=gateSlots (ExitFusionResearch.eraseInputWrap K g complement k) := by
  have H:=eraseMoved_layout_counts K g K.high hw (complement+k)
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [old] at H
  simp only [eraseInputMoved,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp only [moveCached,toffoliCount,measurementCount,gateSlots,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,instructionSlots] at H ⊢
  omega

theorem undoMiddleKeep_counts (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    toffoliCount (undoMiddleKeep K g c k)=toffoliCount (ExitFusionResearch.undoMiddle K g c k) ∧
    measurementCount (undoMiddleKeep K g c k)=measurementCount (ExitFusionResearch.undoMiddle K g c k) ∧
    gateSlots (undoMiddleKeep K g c k)=gateSlots (ExitFusionResearch.undoMiddle K g c k) := by
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,toffoliCount_append,measurementCount_append,gateSlots_append]
  simp [toffoliCount,measurementCount,gateSlots,instructionSlots,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut]

theorem exitEven_counts (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (k:Nat) :
    toffoliCount (exitEven K g k)+1=766 ∧ measurementCount (exitEven K g k)=766 ∧
    gateSlots (exitEven K g k)+3=gateSlots (ExitFusionResearch.exit K g complement k) := by
  have D:=eraseInputMoved_counts K g hw k
  have B:=undoMiddleKeep_counts K g complement k
  have old:=ExitFusionResearch.exit_counts K g complement k hw
  have split:ExitFusionResearch.exit K g complement k=ExitFusionResearch.recoverWrap K g complement k++
      ExitFusionResearch.undoMiddle K g complement k++(ExitFusionResearch.signStage K g k).reverse++
      ExitFusionResearch.eraseInputWrap K g complement k:=rfl
  have slots:=congrArg gateSlots split
  rw [split] at old
  simp only [exitEven,toffoliCount_append,measurementCount_append,gateSlots_append] at old slots ⊢
  omega

attribute [local irreducible] run wires GatePhysical toffoliCount measurementCount gateSlots

theorem compareChainCached_physical (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (compareChain none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareChainCached (a::as) (b::bs) (c::cs) cin target h) := by
  simp only [compareChain,gatePhysical_append] at old
  simp only [compareChainCached,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ch,ch.symm],old.1.2⟩,old.2⟩

theorem compareLtCached_physical (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (compareLt none (a::as) (b::bs) (c::cs) cin target)) :
    GatePhysical (compareLtCached (a::as) (b::bs) (c::cs) cin target h) := by
  simp only [compareLt,gatePhysical_append] at old
  simp only [compareLtCached,gatePhysical_append]
  exact ⟨⟨old.1.1,compareChainCached_physical a b c as bs cs cin target h ch old.1.2⟩,old.2⟩

theorem eraseLtMoved_physical (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) (ch:c≠h)
    (old:GatePhysical (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target)) :
    GatePhysical (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h) := by
  simp only [eraseLtChain,gatePhysical_append] at old
  simp only [eraseLtMoved,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ch,ch.symm],old.1.2⟩,old.2⟩

theorem comparePrefixCached_physical (g a b c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) (ch:c≠h)
    (old:GatePhysical (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)) :
    GatePhysical (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v) := by
  simp only [comparePrefixOld,gatePhysical_append] at old
  simp only [comparePrefixCached,gatePhysical_append]
  exact ⟨⟨old.1.1,compareLtCached_physical a b c as bs cs cin flag h ch old.1.2⟩,old.2⟩

theorem erasePrefixMoved_physical (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) (ch:c≠h)
    (old:GatePhysical (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)) :
    GatePhysical (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v) := by
  simp only [erasePrefixOld,gatePhysical_append] at old
  simp only [erasePrefixMoved,gatePhysical_append]
  exact ⟨⟨old.1.1,eraseLtMoved_physical a a' b b' c as bs cs cin flag h ch old.1.2⟩,old.2⟩

theorem carry_high_ne (K:MeasuredCanonicalModLayout) (g q:Wire) (hn:(g::K.wires).Nodup)
    (hq:q∈K.carry) : q≠K.high := by
  intro e
  have C:=List.nodup_iff_count.mp hn K.high
  have H:=List.count_pos_iff.mpr (e ▸ hq)
  simp only [MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil,
    beq_self_eq_true,if_true] at C
  omega

theorem compareCached_layout_physical (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat)
    (old:GatePhysical (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)) :
    GatePhysical (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v) := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  have ch:=carry_high_ne K g c hn (by rw [hc];simp)
  rw [hs,ho,hc] at old ⊢
  exact comparePrefixCached_physical g a b c K.cin K.flag K.high as bs cs v ch old

theorem eraseMoved_layout_physical (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (v:Nat)
    (old:GatePhysical (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)) :
    GatePhysical (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v) := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  have ch:=carry_high_ne K g c hn (List.mem_of_mem_take (by rw [hc];simp))
  rw [hs,ho,hc] at old ⊢
  exact erasePrefixMoved_physical g a a' b b' c K.cin K.flag K.high as bs cs v ch old

theorem evenBody_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256)
    (hn:(g::K.wires).Nodup) (rest:List Wire) (hout:K.out=lowBit K::rest)
    (old:GatePhysical (entryBody K g k rest)) : GatePhysical (evenBody K g k) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have move:GatePhysical (moveCached K.high (alpha K)):=by
    simp [moveCached,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hhA,hhA.symm]
  have flags:GatePhysical [.CX K.flag (alpha K),.CCX K.flag (sign K) K.high]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hfA,hfS,hfH,hhS.symm]
  simp only [entryBody,entryMiddle,middle,gatePhysical_append] at old
  simp only [evenBody,gatePhysical_append,ExitFusionProof.signStage_eq K g k rest hout]
  exact ⟨⟨⟨⟨move,old.1.1⟩,flags⟩,old.1.2.2⟩,old.2⟩

theorem entryEven_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (entryEven K g k) := by
  have old:=EntryFuse.entry_physical K g complement k hn hw
  rw [ParityConvert.old_entry_split K g hw k] at old
  simp only [gatePhysical_append] at old
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have go:g∉K.out:=controls_fullOut K g hn hw g (by simp [controls]) hgS
  have ho:K.high∉K.out:=controls_fullOut K g hn hw K.high (by simp [controls]) hhS
  have lb:lowBit K∈K.out:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  have gl:g≠lowBit K:=by intro e;exact go (e ▸ lb)
  have lh:lowBit K≠K.high:=by intro e;exact ho (e ▸ lb)
  have pre:GatePhysical [.CCX g (lowBit K) K.high]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,gl,hgH,lh]
  have hout:K.out=lowBit K::K.out.tail:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  simp only [entryEven,gatePhysical_append]
  exact ⟨⟨pre,compareCached_layout_physical K g hw hn (complement+k) old.1⟩,
    evenBody_physical K g k hw hn K.out.tail hout old.2⟩

theorem undoMiddleKeep_physical (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256)
    (old:GatePhysical (ExitFusionResearch.undoMiddle K g c k)) :
    GatePhysical (undoMiddleKeep K g c k) := by
  obtain ⟨hgF,hgH,hgC,hgA,hgS,hfH,hfC,hfA,hfS,hhC,hhA,hhS,hcA,hcS,haS⟩:=controls_distinct K g hn hw
  have tail:GatePhysical [.measureX K.high [] [.CZ K.flag (sign K)],
      .CX K.flag (alpha K),.measureX K.high [] []]:=by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hfH,hfH.symm,hfS,hfS.symm,
      hhS,hhS.symm,hfA]
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,gatePhysical_append,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut] at old ⊢
  exact ⟨old.1,tail⟩

theorem eraseInputMoved_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256)
    (old:GatePhysical (ExitFusionResearch.eraseInputWrap K g complement k)) :
    GatePhysical (eraseInputMoved K g k) := by
  have hhA:K.high≠alpha K:=(controls_distinct K g hn hw).2.2.2.2.2.2.2.2.2.2.1
  have move:GatePhysical (moveCached (alpha K) K.high):=by
    simp [moveCached,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hhA,hhA.symm]
  have eqOld:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [←eqOld] at old
  simp only [eraseInputMoved,gatePhysical_append]
  exact ⟨move,eraseMoved_layout_physical K g hw hn (complement+k) old⟩

theorem exitEven_physical (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (hn:(g::K.wires).Nodup) (hw:K.Widths 256) : GatePhysical (exitEven K g k) := by
  have old:=ExitFusionResearch.exit_physical K g complement k hn hw
  simp only [ExitFusionResearch.exit,gatePhysical_append] at old
  simp only [exitEven,gatePhysical_append]
  exact ⟨⟨⟨old.1.1.1,undoMiddleKeep_physical K g complement k hn hw old.1.1.2⟩,old.1.2⟩,
    eraseInputMoved_physical K g k hn hw old.2⟩

theorem compareChainCached_wires (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (compareChainCached (a::as) (b::bs) (c::cs) cin target h)⊆
      wires (compareChain none (a::as) (b::bs) (c::cs) cin target)∪{h} := by
  have head:wires [.X c,.CX h c]⊆wires (majority a b cin c)∪{h}:=by
    simp [majority,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [compareChainCached,compareChain,wires_append]
  intro q H
  have S:=head (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem compareLtCached_wires (a b c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (compareLtCached (a::as) (b::bs) (c::cs) cin target h)⊆
      wires (compareLt none (a::as) (b::bs) (c::cs) cin target)∪{h} := by
  have core:=compareChainCached_wires a b c as bs cs cin target h
  simp only [compareLtCached,compareLt,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem eraseLtMoved_wires (a a' b b' c:Wire) (as bs cs:List Wire) (cin target h:Wire) :
    wires (eraseLtMoved (a::a'::as) (b::b'::bs) (c::cs) cin target h)⊆
      wires (eraseLtChain (a::a'::as) (b::b'::bs) (c::cs) cin target)∪{h} := by
  have head:wires [.CX h c,.CX c h]⊆wires (borrowMajority a b cin c)∪{h}:=by
    simp [borrowMajority,majority,wires,Instr.wires]
  simp only [eraseLtMoved,eraseLtChain,wires_append]
  intro q H
  have S:=head (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem comparePrefixCached_wires (g a b c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) :
    wires (comparePrefixCached g h (a::as) (b::bs) (c::cs) cin flag v)⊆
      wires (comparePrefixOld g (a::as) (b::bs) (c::cs) cin flag v)∪{h} := by
  have core:=compareLtCached_wires a b c as bs cs cin flag h
  simp only [comparePrefixCached,comparePrefixOld,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem erasePrefixMoved_wires (g a a' b b' c cin flag h:Wire) (as bs cs:List Wire) (v:Nat) :
    wires (erasePrefixMoved g h (a::a'::as) (b::b'::bs) (c::cs) cin flag v)⊆
      wires (erasePrefixOld g (a::a'::as) (b::b'::bs) (c::cs) cin flag v)∪{h} := by
  have core:=eraseLtMoved_wires a a' b b' c as bs cs cin flag h
  simp only [erasePrefixMoved,erasePrefixOld,wires_append]
  intro q H
  have S:=core (a:=q)
  simp only [Finset.mem_union] at H S ⊢
  tauto

theorem compareCached_layout_wires (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    wires (comparePrefixCached g K.high K.src K.out K.carry K.cin K.flag v)⊆
      wires (comparePrefixOld g K.src K.out K.carry K.cin K.flag v)∪{K.high} := by
  obtain ⟨a,as,hs⟩:=list_head K.src (by rw [hw.src];decide)
  obtain ⟨b,bs,ho⟩:=list_head K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head K.carry (by rw [hw.carry];decide)
  rw [hs,ho,hc]
  exact comparePrefixCached_wires g a b c K.cin K.flag K.high as bs cs v

theorem eraseMoved_layout_wires (K:MeasuredCanonicalModLayout) (g:Wire) (hw:K.Widths 256) (v:Nat) :
    wires (erasePrefixMoved g K.high K.src K.out (K.carry.take 255) K.cin K.flag v)⊆
      wires (erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag v)∪{K.high} := by
  obtain ⟨a,a',as,hs⟩:=list_two K.src (by rw [hw.src];decide)
  obtain ⟨b,b',bs,ho⟩:=list_two K.out (by rw [hw.out];decide)
  obtain ⟨c,cs,hc⟩:=list_head (K.carry.take 255) (by simp [hw.carry])
  rw [hs,ho,hc]
  exact erasePrefixMoved_wires g a a' b b' c K.cin K.flag K.high as bs cs v

theorem evenBody_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat)
    (rest:List Wire) (hout:K.out=lowBit K::rest) :
    wires (evenBody K g k)⊆wires (entryBody K g k rest) := by
  have move:wires (moveCached K.high (alpha K))⊆wires (makeFlags K g):=by
    simp [moveCached,makeFlags,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  have flags:wires [.CX K.flag (alpha K),.CCX K.flag (sign K) K.high]⊆wires (makeFlags K g):=by
    simp [makeFlags,wires,Instr.wires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [evenBody,entryBody,entryMiddle,middle,wires_append,ExitFusionProof.signStage_eq K g k rest hout]
  intro q H
  have M:=move (a:=q)
  have F:=flags (a:=q)
  simp only [Finset.mem_union] at H M F ⊢
  tauto

theorem body_control_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (rest:List Wire) :
    ({g,lowBit K,K.high}:Finset Wire)⊆wires (entryBody K g k rest) := by
  simp only [entryBody,entryMiddle,middle,EntryFuse.signStage,moveStage,makeFlags,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem entryEven_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (entryEven K g k)⊆wires (EntryFuse.entry K g complement k) := by
  have hwrd:K.out=lowBit K::K.out.tail:=by
    obtain ⟨a,as,h⟩:=list_head K.out (by rw [hw.out];decide)
    simp [lowBit,h]
  have B:=evenBody_wires K g k K.out.tail hwrd
  have C:=body_control_wires K g k K.out.tail
  have P:=compareCached_layout_wires K g hw (complement+k)
  have pre:wires [.CCX g (lowBit K) K.high]⊆wires (entryBody K g k K.out.tail):=by
    simpa only [wires,Instr.wires,Finset.union_empty] using C
  rw [ParityConvert.old_entry_split K g hw k]
  simp only [entryEven,wires_append]
  intro q H
  have bb:=B (a:=q)
  have pp:=P (a:=q)
  have pr:=pre (a:=q)
  have hi:q=K.high→q∈wires (entryBody K g k K.out.tail):=by
    intro e;apply C; simp [e]
  simp only [Finset.mem_union,Finset.mem_singleton] at H bb pp pr ⊢
  tauto

theorem undoMiddleKeep_wires (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    wires (undoMiddleKeep K g c k)⊆wires (ExitFusionResearch.undoMiddle K g c k) := by
  have tail:wires [.measureX K.high [] [.CZ K.flag (sign K)],
      .CX K.flag (alpha K),.measureX K.high [] []]⊆
      wires [.measureX K.high [] [.CZ K.flag (sign K)],.measureX (alpha K) [] [.CZ g (sign K)]]:=by
    simp [wires,Instr.wires,correctionWires]
    intro q H
    simp only [Finset.mem_insert,Finset.mem_singleton] at H ⊢
    tauto
  simp only [undoMiddleKeep,ExitFusionResearch.undoMiddle,wires_append,
    ExitFusionResearch.lowSrc,ExitFusionResearch.lowOut,EntryFuse.lowSrc,EntryFuse.lowOut]
  exact Finset.union_subset_union (Finset.Subset.refl _) tail

theorem undoMiddle_control_wires (K:MeasuredCanonicalModLayout) (g:Wire) (c k:Nat) :
    ({alpha K,K.high}:Finset Wire)⊆wires (ExitFusionResearch.undoMiddle K g c k) := by
  simp only [ExitFusionResearch.undoMiddle,wires_append]
  intro q H
  simp only [Finset.mem_insert,Finset.mem_singleton] at H
  simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false]
  tauto

theorem eraseInputMoved_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (eraseInputMoved K g k)⊆wires (ExitFusionResearch.eraseInputWrap K g complement k)∪{alpha K,K.high} := by
  have core:=eraseMoved_layout_wires K g hw (complement+k)
  have old:erasePrefixOld g K.src K.out (K.carry.take 255) K.cin K.flag (complement+k)=
      ExitFusionResearch.eraseInputWrap K g complement k:=by
    simp only [erasePrefixOld,loadNot,unloadNot,ExitFusionResearch.eraseInputWrap,List.append_assoc]
  rw [old] at core
  have move:wires (moveCached (alpha K) K.high)⊆({alpha K,K.high}:Finset Wire):=by
    simp [moveCached,wires,Instr.wires]
  simp only [eraseInputMoved,wires_append]
  intro q H
  have M:=move (a:=q)
  have C:=core (a:=q)
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at H M C ⊢
  tauto

theorem exitEven_wires (K:MeasuredCanonicalModLayout) (g:Wire) (k:Nat) (hw:K.Widths 256) :
    wires (exitEven K g k)⊆wires (ExitFusionResearch.exit K g complement k) := by
  have B:=undoMiddleKeep_wires K g complement k
  have D:=eraseInputMoved_wires K g k hw
  have E:=undoMiddle_control_wires K g complement k
  simp only [exitEven,ExitFusionResearch.exit,wires_append]
  intro q H
  have b:=B (a:=q)
  have d:=D (a:=q)
  have e:=E (a:=q)
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at H b d e ⊢
  tauto

end ECDSAAdd.Entrant.ParityEven
