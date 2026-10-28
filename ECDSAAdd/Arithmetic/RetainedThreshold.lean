import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic
open Instr

/-- Exact addition with every low carry retained. The top bit needs no carry:
its omitted overflow is precisely the fixed-width modular wrap. -/
def retainedAddStart : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
    majority a b cin c ++ (retainedAddStart (a'::as) (b'::bs) cs c ++ [CX a b,CX cin b])
  | [a], [b], _, cin => [CX a b,CX cin b]
  | _, _, _, _ => []

/-- Unsum low-to-high before erasing any retained carry, then erase high-to-low.
Both full original operands are restored before the first carry measurement. -/
def retainedAddFinish : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
    [CX cin b,CX a b] ++ (retainedAddFinish (a'::as) (b'::bs) cs c ++ eraseCarry a b cin c)
  | [a], [b], _, cin => [CX cin b,CX a b]
  | _, _, _, _ => []

theorem retainedAdd_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (retainedAddStart x y carry cin)=y.length-1 ∧
    measurementCount (retainedAddStart x y carry cin)=0 ∧
    toffoliCount (retainedAddFinish x y carry cin)=0 ∧
    measurementCount (retainedAddFinish x y carry cin)=y.length-1 := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      cases bs with
      | nil =>
        have hnil : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hx)
        subst as
        simp [retainedAddStart,retainedAddFinish,toffoliCount,measurementCount]
      | cons b' bs' =>
        cases as with
        | nil => simp at hx
        | cons a' as' =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (a'::as') cs c (by simpa using hx) (by simpa using hc)
            have hstart : retainedAddStart (a::a'::as') (b::b'::bs') (c::cs) cin=
                majority a b cin c ++ (retainedAddStart (a'::as') (b'::bs') cs c ++ [CX a b,CX cin b]) := rfl
            have hfinish : retainedAddFinish (a::a'::as') (b::b'::bs') (c::cs) cin=
                [CX cin b,CX a b] ++ (retainedAddFinish (a'::as') (b'::bs') cs c ++ eraseCarry a b cin c) := rfl
            have ht : toffoliCount (retainedAddStart (a'::as') (b'::bs') cs c)=bs'.length := by
              simpa only [List.length_cons,Nat.add_sub_cancel] using h.1
            have hm : measurementCount (retainedAddFinish (a'::as') (b'::bs') cs c)=bs'.length := by
              simpa only [List.length_cons,Nat.add_sub_cancel] using h.2.2.2
            have hmajorityT : toffoliCount (majority a b cin c)=1 := rfl
            have hmajorityM : measurementCount (majority a b cin c)=0 := rfl
            have hsumT : toffoliCount [CX a b,CX cin b]=0 := rfl
            have hsumM : measurementCount [CX a b,CX cin b]=0 := rfl
            have hunsumT : toffoliCount [CX cin b,CX a b]=0 := rfl
            have hunsumM : measurementCount [CX cin b,CX a b]=0 := rfl
            have heraseT : toffoliCount (eraseCarry a b cin c)=0 := rfl
            have heraseM : measurementCount (eraseCarry a b cin c)=1 := rfl
            simp only [hstart,hfinish,toffoliCount_append,measurementCount_append,
              ht,hm,h.2.1,h.2.2.1,hmajorityT,hmajorityM,hsumT,hsumM,
              hunsumT,hunsumM,heraseT,heraseM,List.length_cons]
            refine ⟨?_,trivial,trivial,?_⟩ <;> omega

theorem retainedAdd_support (x y carry : List Wire) (cin : Wire) :
    wires (retainedAddStart x y carry cin) ⊆ (cin::x++y++carry).toFinset ∧
    wires (retainedAddFinish x y carry cin) ⊆ (cin::x++y++carry).toFinset := by
  induction x generalizing y carry cin with
  | nil => simp [retainedAddStart,retainedAddFinish,wires]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [retainedAddStart,retainedAddFinish,wires]
      | cons b bs =>
        cases bs with
        | nil =>
          constructor <;> intro q hq <;>
            simp only [retainedAddStart,retainedAddFinish,wires,Instr.wires,Finset.mem_union,
              Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq ⊢ <;> tauto
        | cons b' bs' => simp [retainedAddStart,retainedAddFinish,wires]
    | cons a' as' =>
      cases y with
      | nil => simp [retainedAddStart,retainedAddFinish,wires]
      | cons b bs =>
        cases bs with
        | nil => simp [retainedAddStart,retainedAddFinish,wires]
        | cons b' bs' =>
          cases carry with
          | nil => simp [retainedAddStart,retainedAddFinish,wires]
          | cons c cs =>
            have h := ih (b'::bs') cs c
            constructor <;> intro q hq
            · simp only [retainedAddStart,wires_append,Finset.mem_union] at hq
              have hm : wires (majority a b cin c) ⊆ {a,b,cin,c} := by
                intro w hw
                simp [majority,wires,Instr.wires] at hw ⊢
                tauto
              simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
              rcases hq with hmq|(ht|hs)
              · have he := hm hmq
                simp only [Finset.mem_insert,Finset.mem_singleton] at he
                tauto
              · have he := List.mem_toFinset.mp (h.1 ht)
                simp only [List.mem_cons,List.mem_append,or_assoc] at he
                tauto
              · simp [wires,Instr.wires] at hs
                tauto
            · simp only [retainedAddFinish,wires_append,Finset.mem_union] at hq
              simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
              rcases hq with hs|(ht|he)
              · simp [wires,Instr.wires] at hs
                tauto
              · have he := List.mem_toFinset.mp (h.2 ht)
                simp only [List.mem_cons,List.mem_append,or_assoc] at he
                tauto
              · rw [eraseCarry_wires] at he
                simp only [Finset.mem_insert,Finset.mem_singleton] at he
                tauto

private theorem retained_sum_inverse (a b cin : Wire) (hab : a≠b) (hcb : cin≠b)
    (s : State) (r1 r2 : List Bool) :
    run [CX cin b,CX a b] r2 (run [CX a b,CX cin b] r1 s)=s := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=b
  · subst q
    simp [writeBit,hab,hcb]
  · simp [writeBit,hq]

/-- Full source/target/work/phase restoration, with independent records. -/
theorem retainedAdd_roundtrip (x y carry : List Wire) (cin : Wire)
    (hn : (cin::x++y++carry).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (r1 r2 : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) :
    run (retainedAddFinish x y carry cin) r2 (run (retainedAddStart x y carry cin) r1 s)=s := by
  induction y generalizing x carry cin s r1 r2 with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      have hcnt := List.nodup_iff_count.mp hn
      have hab : a≠b := by
        intro he
        subst a
        have h := hcnt b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hcb : cin≠b := by
        intro he
        subst cin
        have h := hcnt b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      cases bs with
      | nil =>
        have hnil : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hx)
        subst as
        exact retained_sum_inverse a b cin hab hcb s r1 r2
      | cons b' bs' =>
        cases as with
        | nil => simp at hx
        | cons a' as' =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h4 : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := hcnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have ntail : (c::(a'::as')++(b'::bs')++cs).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := hcnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have hac : a≠c := by
              intro he
              subst a
              have h := hcnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hbc : b≠c := by
              intro he
              subst b
              have h := hcnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro he
              subst cin
              have h := hcnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hz := hclean c (by simp)
            let v := carryBit (s.basis a) (s.basis b) (s.basis cin)
            let seed : State := ⟨s.phase,writeBit s.basis c v⟩
            have hfirst (record : List Bool) : run (majority a b cin c) record s=seed := by
              rw [majority_correct _ _ _ _ h4]
              simp [hz,seed,v]
            have htailclean : ∀q∈cs,seed.basis q=false := by
              intro q hq
              have hqc : q≠c := by
                intro he
                subst q
                have h := hcnt c
                have hh := List.count_pos_iff.mpr hq
                simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                omega
              simpa only [seed,writeBit,Function.update_of_ne hqc] using hclean q (by simp [hq])
            have hcounts := retainedAdd_counts (a'::as') (b'::bs') cs c (by simpa using hx) (by simpa using hc)
            have hmaj : measurementCount (majority a b cin c)=0 := by rfl
            have hunsum : measurementCount [CX cin b,CX a b]=0 := by rfl
            simp only [retainedAddStart,retainedAddFinish,run_append,run_take,
              hmaj,hcounts.2.1,hunsum,List.drop_zero]
            rw [hfirst]
            generalize ht : run (retainedAddStart (a'::as') (b'::bs') cs c) r1 seed=middle
            have back := ih (a'::as') cs c ntail (by simpa using hx) (by simpa using hc)
              seed r1 r2 htailclean
            rw [ht] at back
            have hrecord : run (retainedAddStart (a'::as') (b'::bs') cs c) (r1.take 0) seed=
                run (retainedAddStart (a'::as') (b'::bs') cs c) r1 seed := by
              rw [← hcounts.2.1,run_take]
            rw [retained_sum_inverse a b cin hab hcb,hrecord,ht,back]
            have hk : seed.basis c=carryBit (seed.basis a) (seed.basis b) (seed.basis cin) := by
              simp [seed,writeBit,hac,hbc,hcc,v]
            rw [eraseCarry_correct _ _ _ _ hac hbc hcc seed hk]
            apply congrArg (State.mk s.phase)
            funext q
            by_cases hq : q=c
            · subst q
              simp [seed,writeBit,hz]
            · simp [seed,writeBit,hq]

private theorem retained_phase_pure (p : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : (run p m s).phase=s.phase := by
  induction p generalizing s m with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X q =>
      simp only [measurementCount] at hp
      exact ih hp _ m
    | CX a b =>
      simp only [measurementCount] at hp
      exact ih hp _ m
    | CCX a b c =>
      simp only [measurementCount] at hp
      exact ih hp _ m
    | measureX q c0 c1 => simp [measurementCount] at hp

/-- Image on precisely the capsule footprint. The incoming phase and every
outside bit are unrestricted; the reference input uses the incoming phase. -/
def RetainedAddImage (x y carry : List Wire) (cin : Wire) (base : BasisState) (current : State) : Prop :=
  ∀q∈(cin::x++y++carry).toFinset,
    current.basis q=(run (retainedAddStart x y carry cin) [] ⟨current.phase,base⟩).basis q

/-- A temporary compare may alter arbitrary outside bits and incoming phase.
If original operands and frozen carries return to the start image, finish
restores the full footprint and phase for every independent measurement list. -/
theorem retainedAdd_finish_image (x y carry : List Wire) (cin : Wire)
    (hn : (cin::x++y++carry).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (base : BasisState) (s : State) (record : List Bool)
    (hzero : ∀q∈carry,base q=false) (himage : RetainedAddImage x y carry cin base s) :
    (run (retainedAddFinish x y carry cin) record s).phase=s.phase ∧
    ∀q∈(cin::x++y++carry).toFinset,
      (run (retainedAddFinish x y carry cin) record s).basis q=base q := by
  let input : State := ⟨s.phase,base⟩
  obtain ⟨reference,heq⟩ : ∃t : State,run (retainedAddStart x y carry cin) [] input=t := ⟨_,rfl⟩
  have hs := retainedAdd_support x y carry cin
  have hcounts := retainedAdd_counts x y carry cin hx hc
  have hp : reference.phase=s.phase := by
    have h := retained_phase_pure (retainedAddStart x y carry cin) hcounts.2.1 input []
    rw [heq] at h
    exact h
  have hb : ∀q∈(cin::x++y++carry).toFinset,s.basis q=reference.basis q := by
    intro q hq
    have h := himage q hq
    change s.basis q=(run (retainedAddStart x y carry cin) [] input).basis q at h
    rw [heq] at h
    exact h
  have hlocal := pool_run_agrees (retainedAddFinish x y carry cin) (cin::x++y++carry).toFinset
    hs.2 record s reference hp.symm hb
  have hrestore := retainedAdd_roundtrip x y carry cin hn hx hc input [] record hzero
  rw [heq] at hrestore
  have hphase := congrArg State.phase hrestore
  refine ⟨hlocal.1.trans hphase,?_⟩
  intro q hq
  have h := hlocal.2 q hq
  rw [hrestore] at h
  exact h

/-- Exact modular sum with frozen low carries. Neither operand is truncated;
the carry into the top bit is kept, only the top overflow is omitted. -/
theorem retainedAddStart_correct (x y carry : List Wire) (cin : Wire)
    (hn : (cin::x++y++carry).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (record : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) :
    (run (retainedAddStart x y carry cin) record s).phase=s.phase ∧
    (∀q,q∉y++carry → (run (retainedAddStart x y carry cin) record s).basis q=s.basis q) ∧
    regValue y (run (retainedAddStart x y carry cin) record s).basis=
      (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^y.length := by
  induction y generalizing x carry cin s record with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a as =>
      have cnt := List.nodup_iff_count.mp hn
      have hab : a≠b := by
        intro he; subst a
        have h := cnt b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hcb : cin≠b := by
        intro he; subst cin
        have h := cnt b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      cases bs with
      | nil =>
        have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hx)
        have hk : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
        subst as carry
        simp only [retainedAddStart,run]
        refine ⟨trivial,?_,?_⟩
        · intro q hq
          have hqb : q≠b := by simpa using hq
          simp [writeBit,hqb]
        · simp only [regValue,List.foldr_cons,List.foldr_nil,List.length_cons,List.length_nil,
            writeBit,Function.update_self,Function.update_of_ne hcb]
          cases s.basis a <;> cases s.basis b <;> cases s.basis cin <;> simp
      | cons b' bs' =>
        cases as with
        | nil => simp at hx
        | cons a' as' =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h4 : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have ntail : (c::(a'::as')++(b'::bs')++cs).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have away (q : Wire) (hq : q=a ∨ q=b ∨ q=cin ∨ q=c) : q∉(b'::bs')++cs := by
              intro hm
              have h := cnt q
              have hm' := List.count_pos_iff.mpr hm
              simp only [List.count_append,List.count_cons] at hm'
              rcases hq with rfl|rfl|rfl|rfl <;>
                simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h <;> omega
            have hxyaway (q : Wire) (hq : q∈(a'::as')++(b'::bs')++cs) : q≠c := by
              intro he; subst q
              have h := cnt c
              have hq' := List.count_pos_iff.mpr hq
              simp only [List.count_cons,List.count_append] at h hq'
              simp only [beq_self_eq_true,if_true] at h
              omega
            have hac : a≠c := by
              intro he; subst a
              have h := cnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hbc : b≠c := by
              intro he; subst b
              have h := cnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro he; subst cin
              have h := cnt c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            let A := s.basis a
            let B := s.basis b
            let C := s.basis cin
            let seed : State := ⟨s.phase,writeBit s.basis c (carryBit A B C)⟩
            have hf (m : List Bool) : run (majority a b cin c) m s=seed := by
              rw [majority_correct _ _ _ _ h4]
              simp [seed,hclean c (by simp),A,B,C]
            have hs (q : Wire) (hq : q≠c) : seed.basis q=s.basis q := by simp [seed,writeBit,hq]
            have cleanTail : ∀q∈cs,seed.basis q=false := by
              intro q hq
              exact (hs q (hxyaway q (List.mem_append_right _ hq))).trans (hclean q (by simp [hq]))
            have htFull := ih (a'::as') cs c ntail (by simpa using hx) (by simpa using hc) seed record cleanTail
            generalize heq : run (retainedAddStart (a'::as') (b'::bs') cs c) record seed=tail at htFull
            obtain ⟨hp,keep,hy⟩ := htFull
            have haT : tail.basis a=A := (keep a (away a (Or.inl rfl))).trans (hs a hac)
            have hbT : tail.basis b=B := (keep b (away b (Or.inr (Or.inl rfl)))).trans (hs b hbc)
            have hcT : tail.basis cin=C := (keep cin (away cin (Or.inr (Or.inr (Or.inl rfl))))).trans (hs cin hcc)
            have head (m : List Bool) : run [CX a b,CX cin b] m tail=
                ⟨tail.phase,writeBit tail.basis b (sumBit A B C)⟩ := by
              simp only [run]
              apply congrArg (State.mk tail.phase)
              funext q
              by_cases hq : q=b
              · subst q
                simp [writeBit,Function.update,haT,hbT,hcT,hcb,sumBit]
                cases A <;> cases B <;> cases C <;> rfl
              · simp [writeBit,Function.update,hq]
            have hcounts := retainedAdd_counts (a'::as') (b'::bs') cs c (by simpa using hx) (by simpa using hc)
            have hm : measurementCount (majority a b cin c)=0 := rfl
            simp only [retainedAddStart,run_append,hm,hcounts.2.1,List.drop_zero]
            rw [hf]
            have hr : run (retainedAddStart (a'::as') (b'::bs') cs c) (record.take 0) seed=tail := by
              rw [←hcounts.2.1,run_take,heq]
            rw [hr,head]
            refine ⟨hp,?_,?_⟩
            · intro q hq
              have hqb : q≠b := by intro he; subst q; exact hq (by simp)
              have hqc : q≠c := by intro he; subst q; exact hq (by simp)
              have hqtail : q∉(b'::bs')++cs := by
                intro hh
                exact hq (by simp only [List.mem_append,List.mem_cons] at hh ⊢; tauto)
              have hheadKeep : (writeBit tail.basis b (sumBit A B C)) q=tail.basis q := by
                simp only [writeBit,Function.update_of_ne hqb]
              exact hheadKeep.trans ((keep q hqtail).trans (hs q hqc))
            · have hxseed : regValue (a'::as') seed.basis=regValue (a'::as') s.basis :=
                regValue_congr _ _ _ (fun q hq => hs q (hxyaway q (List.mem_append_left _ (List.mem_append_left _ hq))))
              have hyseed : regValue (b'::bs') seed.basis=regValue (b'::bs') s.basis :=
                regValue_congr _ _ _ (fun q hq => hs q (hxyaway q (List.mem_append_left _ (List.mem_append_right _ hq))))
              have hcout : seed.basis c=carryBit A B C := by simp [seed,writeBit]
              have hbrest : b∉b'::bs' := by
                intro hh
                have h := cnt b
                have hh' := List.count_pos_iff.mpr hh
                simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                simp only [List.count_cons] at hh'
                omega
              have htailreg : regValue (b'::bs') (writeBit tail.basis b (sumBit A B C))=regValue (b'::bs') tail.basis :=
                regValue_congr _ _ _ (fun q hq => by
                  have hqb : q≠b := by intro he; exact hbrest (he ▸ hq)
                  simp [writeBit,hqb])
              change (if (writeBit tail.basis b (sumBit A B C)) b then 1 else 0)+
                2*regValue (b'::bs') (writeBit tail.basis b (sumBit A B C))=_
              rw [htailreg,hy,hxseed,hyseed,hcout]
              simp only [writeBit,Function.update_self,List.length_cons]
              have hnum := sum_value_step A B C (regValue (a'::as') s.basis)
                (regValue (b'::bs') s.basis) (b'::bs').length
              simp only [List.length_cons] at hnum
              simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,A,B,C] using hnum

/-- Every clean-carry start establishes the footprint image used by finish. -/
theorem retainedAdd_start_image (x y carry : List Wire) (cin : Wire)
    (hn : (cin::x++y++carry).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (record : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) :
    RetainedAddImage x y carry cin s.basis (run (retainedAddStart x y carry cin) record s) := by
  generalize hr : run (retainedAddStart x y carry cin) record s=out
  have hs := retainedAddStart_correct x y carry cin hn hx hc s record hclean
  rw [hr] at hs
  have hm := (retainedAdd_counts x y carry cin hx hc).2.1
  have hrun : run (retainedAddStart x y carry cin) [] s=out := by
    have ht := run_take (retainedAddStart x y carry cin) record s
    rw [hm,List.take_zero] at ht
    exact ht.trans hr
  intro q hq
  rw [hs.1]
  change out.basis q=(run (retainedAddStart x y carry cin) [] s).basis q
  rw [hrun]

/-- Reloaded operands and frozen carries may be rebased over arbitrary
outside changes. Equal phase and footprint bits preserve the start image. -/
theorem retainedAdd_image_congr (x y carry : List Wire) (cin : Wire)
    (base : BasisState) (s t : State) (hphase : t.phase=s.phase)
    (hbits : ∀q∈(cin::x++y++carry).toFinset,t.basis q=s.basis q)
    (himage : RetainedAddImage x y carry cin base s) :
    RetainedAddImage x y carry cin base t := by
  intro q hq
  rw [hphase]
  exact (hbits q hq).trans (himage q hq)

end ECDSAAdd.Arithmetic
