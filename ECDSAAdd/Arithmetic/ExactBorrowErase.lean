import ECDSAAdd.Arithmetic.InPlaceAdder

namespace ECDSAAdd.Arithmetic

/-- Borrow-prefix carry without changing either data bit. -/
def borrowMajority (x y cin target : Wire) : Program :=
  [.X x]++majority x y cin target++[.X x]

/-- Immediate Clifford correction for a known borrow. The predicate prefix
is prepared before measuring the target, so no later arithmetic depends on a
saved measurement outcome. -/
def eraseBorrow (x y cin target : Wire) : Program :=
  [.X x]++eraseCarry x y cin target++[.X x]

theorem borrowMajority_correct (x y cin target : Wire)
    (hn : [x,y,cin,target].Nodup) (s : State) (m : List Bool) :
    run (borrowMajority x y cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (!s.basis x) (s.basis y) (s.basis cin))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxy,hxc,hxt⟩,⟨hyc,hyt⟩,hct⟩ := hn
  have hyx := Ne.symm hxy
  have hcx := Ne.symm hxc
  have hcy := Ne.symm hyc
  simp only [borrowMajority,majority,List.cons_append,List.nil_append,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwx : w=x <;> by_cases hwy : w=y <;>
    by_cases hwc : w=cin <;> by_cases hwt : w=target <;>
    simp_all [writeBit,Function.update,carryBit]
  all_goals cases s.basis x <;> cases s.basis y <;> cases s.basis cin <;>
    cases s.basis target <;> simp_all

theorem eraseBorrow_correct (x y cin target : Wire)
    (hx : x≠target) (hy : y≠target) (hc : cin≠target)
    (hxy : x≠y) (hxc : x≠cin)
    (s : State) (m : List Bool)
    (h : s.basis target=carryBit (!s.basis x) (s.basis y) (s.basis cin)) :
    run (eraseBorrow x y cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  let t : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
  have known : t.basis target=carryBit (t.basis x) (t.basis y) (t.basis cin) := by
    simpa [t,writeBit,Ne.symm hx,Ne.symm hxy,Ne.symm hxc] using h
  have clear := eraseCarry_correct x y cin target hx hy hc t known m
  simp only [eraseBorrow,List.cons_append,List.nil_append,run]
  change run (eraseCarry x y cin target++[.X x]) m t=_
  rw [run_append,run_take,clear]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwt : w=target <;> by_cases hwx : w=x <;>
    simp_all [t,writeBit,Function.update]

/-- Low-to-high borrow preparation, target measurement at the top, then
high-to-low independent measured cleanup. Carries never outlive this block. -/
def eraseLtChain : List Wire → List Wire → List Wire → Wire → Wire → Program
  | a::a'::as,b::b'::bs,c::cs,cin,target =>
      borrowMajority a b cin c++eraseLtChain (a'::as) (b'::bs) cs c target++
        eraseBorrow a b cin c
  | [a],[b],_,cin,target => eraseBorrow a b cin target
  | _,_,_,_,_ => []

theorem borrowMajority_counts (x y cin target : Wire) :
    toffoliCount (borrowMajority x y cin target)=1 ∧
    measurementCount (borrowMajority x y cin target)=0 := by constructor <;> rfl

theorem eraseBorrow_counts (x y cin target : Wire) :
    toffoliCount (eraseBorrow x y cin target)=0 ∧
    measurementCount (eraseBorrow x y cin target)=1 := by constructor <;> rfl

theorem eraseLtChain_counts (x y carry : List Wire) (cin target : Wire)
    (hxy : x.length=y.length) (hc : carry.length+1=y.length) :
    toffoliCount (eraseLtChain x y carry cin target)=y.length-1 ∧
    measurementCount (eraseLtChain x y carry cin target)=y.length := by
  induction y generalizing x carry cin with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hxy
    | cons a as =>
      cases bs with
      | nil =>
        have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hxy)
        subst ha
        simp [eraseLtChain,eraseBorrow_counts]
      | cons b' bs =>
        cases as with
        | nil => simp at hxy
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (a'::as) cs c (by simpa using hxy) (by simpa using hc)
            rw [eraseLtChain]
            constructor
            · simp only [toffoliCount_append,(borrowMajority_counts _ _ _ _).1,
                (eraseBorrow_counts _ _ _ _).1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,(borrowMajority_counts _ _ _ _).2,
                (eraseBorrow_counts _ _ _ _).2]
              rw [h.2]
              simp

/-- A borrow out of the low bit is the carry-in for the higher comparison. -/
theorem borrow_threshold (A B C : Bool) (X Y : Nat) :
    (A.toNat+2*X<B.toNat+2*Y+C.toNat) ↔
      X<Y+(carryBit (!A) B C).toNat := by
  cases A <;> cases B <;> cases C <;> simp [carryBit] <;> omega

/-- Exact full-register erasure of a known comparison predicate. The data,
incoming borrow and all other sites are restored; every measurement record
has the same final phase. Only n-1 Toffolis are needed. -/
theorem eraseLtChain_correct (x y carry : List Wire) (cin target : Wire)
    (hnd : (target::cin::(x++y++carry)).Nodup)
    (hxy : x.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (hpred : s.basis target=decide (regValue x s.basis<
      regValue y s.basis+(s.basis cin).toNat)) :
    run (eraseLtChain x y carry cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  induction y generalizing x carry cin s m with
  | nil => simp at hc
  | cons b bs ih =>
    cases x with
    | nil => simp at hxy
    | cons a as =>
      have cnt := List.nodup_iff_count.mp hnd
      have hta : target≠a := by
        intro bad; have h := cnt target; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have htb : target≠b := by
        intro bad; have h := cnt target; subst b
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have htcin : target≠cin := by
        intro bad; have h := cnt target; subst cin
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hab : a≠b := by
        intro bad; have h := cnt b; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have hacin : a≠cin := by
        intro bad; have h := cnt cin; subst a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      cases bs with
      | nil =>
        have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hxy)
        subst ha
        have known : s.basis target=carryBit (!s.basis a) (s.basis b) (s.basis cin) := by
          cases ha : s.basis a <;> cases hb : s.basis b <;> cases hi : s.basis cin <;>
            simpa [regValue,carryBit,ha,hb,hi] using hpred
        exact eraseBorrow_correct a b cin target hta.symm htb.symm htcin.symm
          hab hacin s m known
      | cons b' bs =>
        cases as with
        | nil => simp at hxy
        | cons a' as =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have htc : target≠c := by
              intro bad; have h := cnt target; subst c
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hac : a≠c := by
              intro bad; have h := cnt c; subst a
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hbc : b≠c := by
              intro bad; have h := cnt c; subst b
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro bad; have h := cnt c; subst cin
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hccs : c∉cs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcas : c∉a'::as := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hcbs : c∉b'::bs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have h4 : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have hnd' : (target::c::((a'::as)++(b'::bs)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            let K := carryBit (!s.basis a) (s.basis b) (s.basis cin)
            let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by
              simp [s1,writeBit,hq]
            have hzero := hclean c (by simp)
            have first (record : List Bool) : run (borrowMajority a b cin c) record s=s1 := by
              rw [borrowMajority_correct _ _ _ _ h4]
              simp [s1,K,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            have vx : regValue (a'::as) s1.basis=regValue (a'::as) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcas (bad ▸ hq)))
            have vy : regValue (b'::bs) s1.basis=regValue (b'::bs) s.basis :=
              regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcbs (bad ▸ hq)))
            have pred' : s1.basis target=decide (regValue (a'::as) s1.basis<
                regValue (b'::bs) s1.basis+(s1.basis c).toNat) := by
              rw [keep target htc,vx,vy]
              have hk : s1.basis c=K := by simp [s1,writeBit]
              rw [hk]
              have thr := borrow_threshold (s.basis a) (s.basis b) (s.basis cin)
                (regValue (a'::as) s.basis) (regValue (b'::bs) s.basis)
              have eq : decide (regValue (a::a'::as) s.basis<
                  regValue (b::b'::bs) s.basis+(s.basis cin).toNat)=
                  decide (regValue (a'::as) s.basis<regValue (b'::bs) s.basis+K.toNat) := by
                apply decide_eq_decide.mpr
                simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
              exact hpred.trans eq
            let t : State := ⟨s.phase,writeBit s1.basis target false⟩
            have tail (record : List Bool) :
                run (eraseLtChain (a'::as) (b'::bs) cs c target) record s1=t :=
              ih (a'::as) cs c hnd' (by simpa using hxy) (by simpa using hc)
                s1 record clean' pred'
            have kt (q : Wire) (hqt : q≠target) (hqc : q≠c) : t.basis q=s.basis q := by
              simp [t,writeBit,hqt,keep q hqc]
            have kvalue : t.basis c=K := by simp [t,s1,writeBit,htc.symm]
            have clear (record : List Bool) : run (eraseBorrow a b cin c) record t=
                ⟨s.phase,writeBit t.basis c false⟩ := by
              apply eraseBorrow_correct a b cin c hac hbc hcc hab hacin t record
              rw [kt a hta.symm hac,kt b htb.symm hbc,kt cin htcin.symm hcc,kvalue]
            rw [eraseLtChain]
            simp only [List.append_assoc,run_append,run_take,
              (borrowMajority_counts _ _ _ _).2,List.take_zero,List.drop_zero]
            rw [first,tail,clear]
            apply congrArg (State.mk s.phase)
            funext q
            by_cases hqc : q=c <;> by_cases hqt : q=target <;>
              simp_all [t,s1,writeBit,Function.update]

end ECDSAAdd.Arithmetic
