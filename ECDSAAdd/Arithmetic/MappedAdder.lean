import ECDSAAdd.Arithmetic.ExactBorrowErase

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- A literal or immutable source bit, optionally complemented. Source wires
may recur in several positions; no source register is materialized. -/
structure MappedBit where
  wire : Option Wire
  flip : Bool

def MappedBit.value (b : MappedBit) (s : BasisState) : Bool :=
  b.flip ^^ (b.wire.map s).getD false

def mappedValue : List MappedBit → BasisState → Nat
  | [],_ => 0
  | b::bs,s => (b.value s).toNat+2*mappedValue bs s

def mappedWires (bits : List MappedBit) : List Wire :=
  bits.flatMap (fun b => b.wire.toList)

/-- One exact carry; inputs return to their entry values before recursion. -/
def mappedMajority (b : MappedBit) (y cin target : Wire) : Program :=
  match b.wire with
  | none => if b.flip then [.CX y target,.CX cin target,.CCX y cin target]
      else [.CCX y cin target]
  | some a => if b.flip then borrowMajority a y cin target
      else majority a y cin target

def mappedEraseCarry (b : MappedBit) (y cin target : Wire) : Program :=
  match b.wire with
  | none => [.measureX target []
      (if b.flip then [.Z y,.Z cin,.CZ y cin] else [.CZ y cin])]
  | some a => if b.flip then eraseBorrow a y cin target
      else eraseCarry a y cin target

def mappedSum (b : MappedBit) (y cin : Wire) : Program :=
  (match b.wire with | none => [] | some a => [.CX a y])++
    (if b.flip then [.X y] else [])++[.CX cin y]

def mappedAdd : List MappedBit → List Wire → List Wire → Wire → Program
  | b::b'::bits,y::y'::ys,c::cs,cin =>
      mappedMajority b y cin c++mappedAdd (b'::bits) (y'::ys) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | [b],[y],_,cin => mappedSum b y cin
  | _,_,_,_ => []

private theorem mapped_four_nodup (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup)
    (ha : ∀q∈b.wire,q∉[y,cin,target]) (a : Wire) (hw : b.wire=some a) :
    [a,y,cin,target].Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨ha a (by simp [hw]),hn⟩

theorem mappedMajority_correct (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,target])
    (s : State) (m : List Bool) :
    run (mappedMajority b y cin target) m s=
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ carryBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  cases hw : b.wire with
  | some a =>
    have h4 := mapped_four_nodup b y cin target hn ha a hw
    cases hf : b.flip
    · simpa [mappedMajority,hw,hf,MappedBit.value] using majority_correct a y cin target h4 s m
    · simpa [mappedMajority,hw,hf,MappedBit.value] using borrowMajority_correct a y cin target h4 s m
  | none =>
    have hyt : y≠target := fun bad => (List.nodup_cons.mp hn).1 (by simp [bad])
    have hct : cin≠target := fun bad => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [bad])
    cases hf : b.flip <;>
      simp only [mappedMajority,hw,hf,Bool.false_eq_true,if_false,if_true,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;>
        simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hyt,hct,carryBit]

theorem mappedEraseCarry_correct (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀q∈b.wire,q∉[y,cin,target])
    (s : State) (m : List Bool)
    (hk : s.basis target=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
    run (mappedEraseCarry b y cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  have hyt : y≠target := fun bad => (List.nodup_cons.mp hn).1 (by simp [bad])
  have hct : cin≠target := fun bad => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [bad])
  cases hw : b.wire with
  | some a =>
    have h4 := mapped_four_nodup b y cin target hn ha a hw
    have hx : a≠target := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    have hxy : a≠y := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    have hxc : a≠cin := fun bad => (List.nodup_cons.mp h4).1 (by simp [bad])
    cases hf : b.flip
    · simpa [mappedEraseCarry,hw,hf] using eraseCarry_correct a y cin target hx hyt hct s
        (by simpa [MappedBit.value,hw,hf] using hk) m
    · simpa [mappedEraseCarry,hw,hf] using eraseBorrow_correct a y cin target hx hyt hct
        hxy hxc s m (by simpa [MappedBit.value,hw,hf] using hk)
  | none =>
    cases hf : b.flip <;> cases hm : m.head?.getD false <;>
      simp [mappedEraseCarry,hw,hf,run,measureAndCorrect,correct,writeBit,
        hyt,hct,hk,MappedBit.value,carryBit,hm]
    all_goals cases s.basis y <;> cases s.basis cin <;> simp

theorem mappedSum_correct (b : MappedBit) (y cin : Wire)
    (hc : cin≠y) (ha : ∀q∈b.wire,q≠y) (s : State) (m : List Bool) :
    run (mappedSum b y cin) m s=
      ⟨s.phase,writeBit s.basis y (sumBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;> simp only [mappedSum,hw,hf,Bool.false_eq_true,if_false,
      if_true,List.nil_append,List.cons_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=y <;> simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hc,sumBit]
  | some a =>
    have hay : a≠y := ha a (by simp [hw])
    cases hf : b.flip <;> simp only [mappedSum,hw,hf,Bool.false_eq_true,if_false,
      if_true,List.nil_append,List.cons_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=y <;> simp [MappedBit.value,hw,hf,writeBit,Function.update,hq,hc,hay,sumBit]
    all_goals cases s.basis a <;> cases s.basis y <;> cases s.basis cin <;> simp

theorem mappedValue_congr (bits : List MappedBit) (s t : BasisState)
    (h : ∀q∈mappedWires bits,s q=t q) : mappedValue bits s=mappedValue bits t := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.value s=b.value t := by
      cases hw : b.wire
      · simp [MappedBit.value,hw]
      · rename_i q
        simp [MappedBit.value,hw,h q (by simp [mappedWires,hw])]
    rw [mappedValue,mappedValue,hb,ih]
    intro q hq
    exact h q (by simp [mappedWires] at hq ⊢; tauto)

theorem mappedBit_counts (b : MappedBit) (y cin target : Wire) :
    toffoliCount (mappedMajority b y cin target)=1 ∧
    measurementCount (mappedMajority b y cin target)=0 ∧
    toffoliCount (mappedEraseCarry b y cin target)=0 ∧
    measurementCount (mappedEraseCarry b y cin target)=1 ∧
    toffoliCount (mappedSum b y cin)=0 ∧ measurementCount (mappedSum b y cin)=0 := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [mappedMajority,mappedEraseCarry,mappedSum,hw,hf,borrowMajority,eraseBorrow,
      majority,eraseCarry,toffoliCount,measurementCount]

theorem mappedBit_value_congr (b : MappedBit) (s t : BasisState)
    (h : ∀q∈b.wire,s q=t q) : b.value s=b.value t := by
  cases hw : b.wire
  · simp [MappedBit.value,hw]
  · rename_i q
    simp [MappedBit.value,hw,h q (by simp [hw])]

private theorem mapped_head_mem (b : MappedBit) (bits : List MappedBit)
    (q : Wire) (h : q∈b.wire) : q∈mappedWires (b::bits) := by
  cases hw : b.wire with
  | none => simp [hw] at h
  | some a =>
    have eq : a=q := by simpa [hw] using h
    subst a
    simp [mappedWires,hw]

private theorem mapped_tail_mem (b : MappedBit) (bits : List MappedBit)
    (q : Wire) (h : q∈mappedWires bits) : q∈mappedWires (b::bits) := by
  exact List.mem_append_right _ h

/-- Complete measured-adder semantics, allowing repeated immutable source
wires. The whole carry bank is cleaned and all measurement phases restored. -/
theorem mappedAdd_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedAdd bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedAdd bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedAdd bits ys carry cin) m s).basis=
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  induction ys generalizing bits carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      have cnt := List.nodup_iff_count.mp hn
      have hcy : cin≠y := by
        intro bad; have h := cnt y; subst cin
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have bitAway (q : Wire) (hq : q∈b.wire) : q∉cin::((y::ys)++carry) :=
        hs q (mapped_head_mem b bits q hq)
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        have ha : ∀q∈b.wire,q≠y := by
          intro q hq bad
          exact bitAway q hq (by simp [bad])
        rw [mappedAdd,mappedSum_correct b y cin hcy ha]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          simp [writeBit,hq]
        · simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,
            Function.update_self,List.length_cons,List.length_nil,mappedValue]
          cases b.value s.basis <;> cases s.basis y <;> cases s.basis cin <;>
            simp [sumBit,Bool.toNat]
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have hyc : y≠c := by
              intro bad; have h := cnt c; subst y
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro bad; have h := cnt c; subst cin
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcytail : c∉y'::ys := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hyytail : y∉y'::ys := by
              intro bad; have h := cnt y
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hcintail : cin∉y'::ys := by
              intro bad; have h := cnt cin
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hccs : c∉cs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have h3 : [y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have hbaway : ∀q∈b.wire,q∉[y,cin,c] := by
              intro q hq bad
              exact bitAway q hq (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have nd' : (c::((y'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have src' : ∀q∈mappedWires (b'::bits),q∉c::((y'::ys)++cs) := by
              intro q hq bad
              exact hs q (mapped_tail_mem b (b'::bits) q hq)
                (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have sourceAwayC (q : Wire) (hq : q∈mappedWires (b::b'::bits)) : q≠c := by
              intro bad
              exact hs q hq (by simp [bad])
            let A := b.value s.basis
            let B := s.basis y
            let C := s.basis cin
            let K := carryBit A B C
            let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by
              simp [s1,writeBit,hq]
            have hzero := hclean c (by simp)
            have first (record : List Bool) : run (mappedMajority b y cin c) record s=s1 := by
              rw [mappedMajority_correct b y cin c h3 hbaway]
              simp [s1,K,A,B,C,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            obtain ⟨hp,he,hv⟩ := ih (b'::bits) cs c nd' src'
              (by simpa using hl) (by simpa using hc) s1 m clean'
            let t := run (mappedAdd (b'::bits) (y'::ys) cs c) m s1
            have ht : t.phase=s.phase := hp
            have ty : t.basis y=B := (he y hyytail).trans (keep y hyc)
            have ti : t.basis cin=C := (he cin hcintail).trans (keep cin hcc)
            have tk : t.basis c=K := by rw [he c hcytail]; simp [s1,writeBit]
            have ta : b.value t.basis=A := by
              apply mappedBit_value_congr b t.basis s.basis
              intro q hq
              have away := bitAway q hq
              have yt : q∉y'::ys := fun bad => away
                (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem y bad)))
              exact (he q yt).trans (keep q (sourceAwayC q (mapped_head_mem b (b'::bits) q hq)))
            have clear (record : List Bool) : run (mappedEraseCarry b y cin c) record t=
                ⟨t.phase,writeBit t.basis c false⟩ := by
              apply mappedEraseCarry_correct b y cin c h3 hbaway t record
              rw [ta,ty,ti,tk]
            let u : State := ⟨t.phase,writeBit t.basis c false⟩
            have uy : u.basis y=B := by simp [u,writeBit,hyc,ty]
            have ui : u.basis cin=C := by simp [u,writeBit,hcc,ti]
            have ua : b.value u.basis=A := by
              apply Eq.trans (mappedBit_value_congr b u.basis t.basis ?_) ta
              intro q hq
              simp [u,writeBit,sourceAwayC q (mapped_head_mem b (b'::bits) q hq)]
            have finish (record : List Bool) : run (mappedSum b y cin) record u=
                ⟨t.phase,writeBit u.basis y (sumBit A B C)⟩ := by
              rw [mappedSum_correct b y cin hcy (by
                intro q hq bad; exact bitAway q hq (by simp [bad])),ua,uy,ui]
            have mh := mappedBit_counts b y cin c
            rw [mappedAdd]
            simp only [List.append_assoc,run_append,run_take,mh.2.1,List.take_zero,List.drop_zero]
            rw [first]
            change (run (mappedSum b y cin) _ (run (mappedEraseCarry b y cin c) _ t)).phase=_ ∧ _
            rw [clear,finish]
            refine ⟨ht,?_,?_⟩
            · intro q hq
              have hq' : q≠y ∧ q∉y'::ys := by simpa using hq
              by_cases hqc : q=c
              · subst q; simp [u,writeBit,hyc.symm,hzero]
              · simp only [u,writeBit,Function.update_of_ne hq'.1,Function.update_of_ne hqc]
                exact (he q hq'.2).trans (keep q hqc)
            · have tailValue : regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=
                  regValue (y'::ys) t.basis := by
                apply regValue_congr
                intro q hq
                have hqy : q≠y := fun bad => hyytail (bad ▸ hq)
                have hqc : q≠c := fun bad => hcytail (bad ▸ hq)
                simp [u,writeBit,hqy,hqc]
              have sourceValue : mappedValue (b'::bits) s1.basis=mappedValue (b'::bits) s.basis := by
                apply mappedValue_congr
                intro q hq
                exact keep q (sourceAwayC q (mapped_tail_mem b (b'::bits) q hq))
              have yValue : regValue (y'::ys) s1.basis=regValue (y'::ys) s.basis :=
                regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcytail (bad ▸ hq)))
              have kc : s1.basis c=K := by simp [s1,writeBit]
              change (if (writeBit u.basis y (sumBit A B C)) y then 1 else 0)+
                  2*regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=_
              rw [show (writeBit u.basis y (sumBit A B C)) y=sumBit A B C by simp [writeBit],
                tailValue,hv,sourceValue,yValue,kc]
              have num := sum_value_step A B C (mappedValue (b'::bits) s.basis)
                (regValue (y'::ys) s.basis) (y'::ys).length
              simpa only [regValue,List.foldr_cons,mappedValue,List.length_cons,
                Bool.toNat,Bool.cond_eq_ite,A,B,C,K] using num

theorem mappedAdd_counts (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (mappedAdd bits ys carry cin)=ys.length-1 ∧
    measurementCount (mappedAdd bits ys carry cin)=ys.length-1 := by
  induction ys generalizing bits carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        simpa [mappedAdd] using
          And.intro (mappedBit_counts b y cin cin).2.2.2.2.1
            (mappedBit_counts b y cin cin).2.2.2.2.2
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (b'::bits) cs c (by simpa using hl) (by simpa using hc)
            have head := mappedBit_counts b y cin c
            rw [mappedAdd]
            constructor
            · simp only [toffoliCount_append,head.1,head.2.2.1,head.2.2.2.2.1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,head.2.1,head.2.2.2.1,head.2.2.2.2.2]
              rw [h.2]
              simp

theorem mappedBit_wires (b : MappedBit) (y cin target : Wire) :
    wires (mappedMajority b y cin target)⊆(b.wire.toList++[y,cin,target]).toFinset ∧
    wires (mappedEraseCarry b y cin target)⊆(b.wire.toList++[y,cin,target]).toFinset ∧
    wires (mappedSum b y cin)⊆(b.wire.toList++[y,cin]).toFinset := by
  cases hw : b.wire <;> cases hf : b.flip
  all_goals
    constructor
    · intro q hq
      simp [mappedMajority,hw,hf,borrowMajority,majority,wires,Instr.wires] at hq ⊢
      tauto
    · constructor
      · intro q hq
        simp [mappedEraseCarry,hw,hf,eraseBorrow,eraseCarry,wires,Instr.wires,correctionWires] at hq ⊢
        tauto
      · intro q hq
        simp [mappedSum,hw,hf,wires,Instr.wires] at hq ⊢
        tauto

theorem mappedAdd_wires_subset (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (mappedAdd bits ys carry cin)⊆(mappedWires bits++ys++carry++[cin]).toFinset := by
  induction ys generalizing bits carry cin with
  | nil => cases bits <;> simp [mappedAdd,wires]
  | cons y ys ih =>
    cases bits with
    | nil => simp [mappedAdd,wires]
    | cons b bits =>
      cases ys with
      | nil =>
        cases bits with
        | nil =>
          rw [mappedAdd]
          apply Finset.Subset.trans (mappedBit_wires b y cin cin).2.2
          intro q hq
          simp [mappedWires] at hq ⊢
          tauto
        | cons b' bits => simp [mappedAdd,wires]
      | cons y' ys =>
        cases bits with
        | nil => simp [mappedAdd,wires]
        | cons b' bits =>
          cases carry with
          | nil => simp [mappedAdd,wires]
          | cons c cs =>
            let pool := (mappedWires (b::b'::bits)++(y::y'::ys)++(c::cs)++[cin]).toFinset
            have localPool : (b.wire.toList++[y,cin,c]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              tauto
            have tail : (mappedWires (b'::bits)++(y'::ys)++cs++[c]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              aesop
            have sum : (b.wire.toList++[y,cin]).toFinset⊆pool := by
              intro q hq
              simp [pool,mappedWires] at hq ⊢
              tauto
            have bit := mappedBit_wires b y cin c
            have headSupport := Finset.Subset.trans bit.1 localPool
            have tailSupport := Finset.Subset.trans (ih (b'::bits) cs c) tail
            have eraseSupport := Finset.Subset.trans bit.2.1 localPool
            have sumSupport := Finset.Subset.trans bit.2.2 sum
            rw [mappedAdd]
            intro q hq
            simp only [wires_append,Finset.mem_union] at hq
            exact by tauto

end ECDSAAdd.Arithmetic
