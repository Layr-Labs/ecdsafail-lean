import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.KnownOutputCarry

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.KnownOutputAdder

def boolValue : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*boolValue bs

def sumBits : List MappedBit → List Wire → Bool → BasisState → List Bool
  | b::bs,y::ys,c,s =>
      sumBit (b.value s) (s y) c :: sumBits bs ys (carryBit (b.value s) (s y) c) s
  | _,_,_,_ => []

theorem sumBits_length (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) :
    (sumBits bits ys c s).length=ys.length := by
  induction ys generalizing bits c with
  | nil => simp [sumBits]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs => simp [sumBits,ih bs _ (by simpa using hl)]

theorem sumBits_value (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) :
    boolValue (sumBits bits ys c s)=
      (mappedValue bits s+regValue ys s+c.toNat)%2^ys.length := by
  induction ys generalizing bits c with
  | nil =>
    have h : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h,sumBits,boolValue,mappedValue,regValue,Nat.mod_one]
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      rw [sumBits,boolValue,ih bs _ (by simpa using hl)]
      simpa only [mappedValue,regValue,List.length_cons,List.foldr_cons,
        Bool.toNat,Bool.cond_eq_ite] using
        sum_value_step (b.value s) (s y) c (mappedValue bs s) (regValue ys s) ys.length

theorem boolValue_injective (xs ys : List Bool) (hl : xs.length=ys.length)
    (hv : boolValue xs=boolValue ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    have h : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    simp [h]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [boolValue] at hv
      have bits : x=y := by
        cases x <;> cases y <;> simp only [Bool.toNat_false,Bool.toNat_true] at hv ⊢
        all_goals first | rfl | omega
      subst y
      have tails : boolValue xs=boolValue ys := by omega
      exact congrArg (List.cons x) (ih ys (by simpa using hl) tails)

theorem mapped_boolValue (bits : List MappedBit) (s : BasisState) :
    boolValue (bits.map (fun b => b.value s))=mappedValue bits s := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [boolValue,mappedValue,ih]

def Ready (bits sums : List MappedBit) (ys : List Wire) (c : Bool) (s : BasisState) : Prop :=
  sums.map (fun b => b.value s)=sumBits bits ys c s

theorem ready_of_value (bits sums : List MappedBit) (ys : List Wire) (c : Bool)
    (s : BasisState) (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hv : mappedValue sums s=(mappedValue bits s+regValue ys s+c.toNat)%2^ys.length) :
    Ready bits sums ys c s := by
  apply boolValue_injective
  · simp [hs,sumBits_length bits ys c s hl]
  · rw [mapped_boolValue,hv,sumBits_value bits ys c s hl]

def xorBit (b : MappedBit) (target : Wire) : Program :=
  (match b.wire with | none => [] | some a => [.CX a target])++
    (if b.flip then [.X target] else [])

def prepare (b desired : MappedBit) (nextTarget carry : Wire) : Program :=
  [.CX nextTarget carry]++xorBit b carry++xorBit desired carry

/-- Same full bank as the ordinary adder. Its carry producers are replaced
by affine reads of a disjoint, immutable complete sum witness. -/
def program : List MappedBit → List Wire → List MappedBit → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,d::d'::ds,c::cs,cin =>
      prepare b' d' y' c++program (b'::bs) (y'::ys) (d'::ds) cs c++
        mappedEraseCarry b y cin c++mappedSum b y cin
  | [b],[y],[_],_,cin => mappedSum b y cin
  | _,_,_,_,_ => []

theorem xorBit_counts (b : MappedBit) (target : Wire) :
    toffoliCount (xorBit b target)=0 ∧ measurementCount (xorBit b target)=0 := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [xorBit,hw,hf,toffoliCount,measurementCount]

theorem prepare_counts (b d : MappedBit) (y c : Wire) :
    toffoliCount (prepare b d y c)=0 ∧ measurementCount (prepare b d y c)=0 := by
  have h := xorBit_counts b c
  have k := xorBit_counts d c
  simp [prepare,toffoliCount_append,measurementCount_append,h.1,h.2,k.1,k.2,
    toffoliCount,measurementCount]

theorem program_counts (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (program bits ys sums carry cin)=0 ∧
    measurementCount (program bits ys sums carry cin)=ys.length-1 := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          have h := mappedBit_counts b y cin cin
          simpa [program] using And.intro h.2.2.2.2.1 h.2.2.2.2.2
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have h := prepare_counts b' d' y' c
                have t := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have k := mappedBit_counts b y cin c
                simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,
                  t.1,t.2,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,k.2.2.2.2.2]
                simp

theorem xorBit_correct (b : MappedBit) (target : Wire)
    (ha : ∀q∈b.wire,q≠target) (s : State) (m : List Bool) :
    run (xorBit b target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ b.value s.basis)⟩ := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;> simp only [xorBit,hw,hf,if_false,if_true,
      Bool.false_eq_true,List.nil_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target <;>
        simp [writeBit,MappedBit.value,hw,hf,hq]
  | some a =>
    have ne : a≠target := ha a (by simp [hw])
    cases hf : b.flip <;> simp only [xorBit,hw,hf,if_false,if_true,
      Bool.false_eq_true,List.cons_append,List.nil_append,run]
    all_goals
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hq : q=target
      · subst q
        cases hb : s.basis target <;> cases hx : s.basis a <;>
          simp [writeBit,MappedBit.value,hw,hf,ne,hb,hx]
      · simp [writeBit,hq]

private theorem write_twice (s : BasisState) (q : Wire) (a b : Bool) :
    writeBit (writeBit s q a) q b=writeBit s q b := by
  funext w
  by_cases h : w=q <;> simp [writeBit,h]

theorem prepare_correct (b d : MappedBit) (y c : Wire)
    (hy : y≠c) (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈d.wire,q≠c)
    (s : State) (m : List Bool) :
    run (prepare b d y c) m s=
      ⟨s.phase,writeBit s.basis c
        (((s.basis c ^^ s.basis y) ^^ b.value s.basis) ^^ d.value s.basis)⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let v : State := ⟨s.phase,writeBit u.basis c (u.basis c ^^ b.value u.basis)⟩
  have bu : b.value u.basis=b.value s.basis := by
    apply mappedBit_value_congr
    intro q hq
    simp [u,writeBit,hb q hq]
  have dv : d.value v.basis=d.value s.basis := by
    apply mappedBit_value_congr
    intro q hq
    simp [v,u,writeBit,hd q hq]
  have bc := xorBit_counts b c
  have dc := xorBit_counts d c
  rw [prepare]
  simp only [List.append_assoc,run_append,measurementCount,bc.2,
    dc.2,List.take_zero,List.drop_zero,run]
  change run (xorBit d c) m (run (xorBit b c) [] u)=_
  rw [xorBit_correct b c hb u []]
  change run (xorBit d c) m v=_
  rw [xorBit_correct d c hd v m,dv]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=c
  · subst q
    simp only [v,State.basis,writeBit,Function.update_self]
    rw [bu]
    simp [u,writeBit]
  · simp [v,u,writeBit,hq]

private theorem head_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈b.wire) : q∈mappedWires (b::bs) := by
  cases hw : b.wire with
  | none => simp [hw] at hq
  | some a =>
    have eq : a=q := by simpa [hw] using hq
    subst a
    simp [mappedWires,hw]

private theorem tail_source_mem (b : MappedBit) (bs : List MappedBit)
    (q : Wire) (hq : q∈mappedWires bs) : q∈mappedWires (b::bs) := by
  exact List.mem_append_right _ hq

theorem sumBits_congr (bits : List MappedBit) (ys : List Wire) (c : Bool)
    (s t : BasisState) (hs : ∀q∈mappedWires bits,s q=t q)
    (hy : ∀q∈ys,s q=t q) : sumBits bits ys c s=sumBits bits ys c t := by
  induction bits generalizing ys c with
  | nil => rfl
  | cons b bs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have bit : b.value s=b.value t := mappedBit_value_congr b s t
        (fun q hq => hs q (head_source_mem b bs q hq))
      simp only [sumBits,bit,hy y (by simp)]
      exact congrArg (List.cons _) (ih ys _
        (fun q hq => hs q (tail_source_mem b bs q hq))
        (fun q hq => hy q (by simp [hq])))

theorem ready_congr (bits sums : List MappedBit) (ys : List Wire) (c : Bool)
    (s t : BasisState) (hs : ∀q∈mappedWires bits,s q=t q)
    (hw : ∀q∈mappedWires sums,s q=t q) (hy : ∀q∈ys,s q=t q)
    (h : Ready bits sums ys c s) : Ready bits sums ys c t := by
  have vals : sums.map (fun b => b.value s)=sums.map (fun b => b.value t) := by
    apply List.map_congr_left
    intro b hb
    apply mappedBit_value_congr
    intro q hq
    apply hw q
    change q∈sums.flatMap (fun b => b.wire.toList)
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,by simpa using hq⟩
  unfold Ready at h ⊢
  rw [←vals,←sumBits_congr bits ys c s t hs hy]
  exact h

/-- Exact program transport on the known-sum subspace. The ordinary mapped
adder remains unrestricted; only this receiver carries the additional premise. -/
theorem program_eq_mappedAdd (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (ready : Ready bits sums ys (s.basis cin) s.basis) :
    run (program bits ys sums carry cin) m s=run (mappedAdd bits ys carry cin) m s := by
  induction ys generalizing bits sums carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        cases ys with
        | nil =>
          have hb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have hd : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          rfl
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have cnt := List.nodup_iff_count.mp hn
                have yc : y≠c := by
                  intro bad; have h := cnt c; subst y
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have yc' : y'≠c := by
                  intro bad; have h := cnt c; subst y'
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have cc : cin≠c := by
                  intro bad; have h := cnt c; subst cin
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
                  omega
                have ctail : c∉y'::ys := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have ccs : c∉cs := by
                  intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
                  simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
                  omega
                have three : [y,cin,c].Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
                  omega
                have nd : (c::((y'::ys)++cs)).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q; have h := cnt q
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have source : ∀q∈mappedWires (b'::bs),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact ha q (tail_source_mem b _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have witness : ∀q∈mappedWires (d'::ds),q∉c::((y'::ys)++cs) := by
                  intro q hq bad
                  exact hw q (tail_source_mem d _ q hq)
                    (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have sourceC (q : Wire) (hq : q∈mappedWires (b::b'::bs)) : q≠c := by
                  intro bad; exact ha q hq (by simp [bad])
                have witnessC (q : Wire) (hq : q∈mappedWires (d::d'::ds)) : q≠c := by
                  intro bad; exact hw q hq (by simp [bad])
                let K := carryBit (b.value s.basis) (s.basis y) (s.basis cin)
                let u : State := ⟨s.phase,writeBit s.basis c K⟩
                have clean0 : s.basis c=false := hclean c (by simp)
                have rt : Ready (b'::bs) (d'::ds) (y'::ys) K s.basis := by
                  exact (List.cons.inj ready).2
                have next : d'.value s.basis=sumBit (b'.value s.basis) (s.basis y') K := by
                  exact (List.cons.inj rt).1
                have affine : ((s.basis y' ^^ b'.value s.basis) ^^ d'.value s.basis)=K := by
                  rw [next]
                  cases b'.value s.basis <;> cases s.basis y' <;> cases K <;> decide
                have pre (mm : List Bool) : run (prepare b' d' y' c) mm s=u := by
                  rw [prepare_correct b' d' y' c yc'
                    (fun q hq => sourceC q (tail_source_mem b _ q (head_source_mem b' bs q hq)))
                    (fun q hq => witnessC q (tail_source_mem d _ q (head_source_mem d' ds q hq))) s mm]
                  simp [u,clean0,affine]
                have old (mm : List Bool) : run (mappedMajority b y cin c) mm s=u := by
                  rw [mappedMajority_correct b y cin c three]
                  · simp [u,K,clean0]
                  · intro q hq bad
                    exact ha q (head_source_mem b _ q hq)
                      (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
                have keep (q : Wire) (hne : q≠c) : u.basis q=s.basis q := by
                  simp [u,writeBit,hne]
                have uc : u.basis c=K := by simp [u,writeBit]
                have tailReady : Ready (b'::bs) (d'::ds) (y'::ys) (u.basis c) u.basis := by
                  rw [uc]
                  apply ready_congr _ _ _ _ s.basis u.basis _ _ _ rt
                  · intro q hq
                    exact (keep q (sourceC q (tail_source_mem b _ q hq))).symm
                  · intro q hq
                    exact (keep q (witnessC q (tail_source_mem d _ q hq))).symm
                  · intro q hq
                    exact (keep q (fun bad => ctail (bad ▸ hq))).symm
                have clean : ∀q∈cs,u.basis q=false := by
                  intro q hq
                  rw [keep q (fun bad => ccs (bad ▸ hq))]
                  exact hclean q (by simp [hq])
                have tail (mm : List Bool) := ih (b'::bs) (d'::ds) cs c nd source witness
                  (by simpa using hl) (by simpa using hs) (by simpa using hc) u mm clean tailReady
                have pc := prepare_counts b' d' y' c
                have oc := mappedBit_counts b y cin c
                have nc := program_counts (b'::bs) (d'::ds) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                have mc := mappedAdd_counts (b'::bs) (y'::ys) cs c
                  (by simpa using hl) (by simpa using hc)
                rw [program,mappedAdd]
                simp only [List.append_assoc,run_append,run_take,pc.2,oc.2.1,
                  nc.2,mc.2,List.take_zero,List.drop_zero]
                rw [pre,old,tail]

theorem program_correct (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (sumKnown : mappedValue sums s.basis=
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length) :
    (run (program bits ys sums carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (program bits ys sums carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (program bits ys sums carry cin) m s).basis=mappedValue sums s.basis := by
  have ready := ready_of_value bits sums ys (s.basis cin) s.basis hl hs sumKnown
  rw [program_eq_mappedAdd bits sums ys carry cin hn ha hw hl hs hc s m hclean ready]
  have old := mappedAdd_correct bits ys carry cin hn ha hl hc s m hclean
  exact ⟨old.1,old.2.1,old.2.2.trans sumKnown.symm⟩

theorem xorBit_support (b : MappedBit) (target : Wire) :
    wires (xorBit b target)⊆(b.wire.toList++[target]).toFinset := by
  intro q hq
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [xorBit,hw,hf,wires,Instr.wires] at hq ⊢
  all_goals tauto

theorem prepare_support (b d : MappedBit) (y c : Wire) :
    wires (prepare b d y c)⊆(b.wire.toList++d.wire.toList++[y,c]).toFinset := by
  intro q hq
  simp only [prepare,wires_append,Finset.mem_union] at hq
  rcases hq with (hq|hq)|hq
  · have h : q=y ∨ q=c := by simpa [wires,Instr.wires] using hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have h := xorBit_support b c hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · have h := xorBit_support d c hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem program_support (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (program bits ys sums carry cin)⊆
      (mappedWires bits++mappedWires sums++ys++carry++[cin]).toFinset := by
  induction ys generalizing bits sums carry cin with
  | nil => cases bits <;> cases sums <;> simp [program,wires]
  | cons y ys ih =>
    cases bits with
    | nil => simp [program,wires]
    | cons b bs =>
      cases sums with
      | nil => simp [program,wires]
      | cons d ds =>
        cases ys with
        | nil =>
          cases bs with
          | nil =>
            cases ds with
            | nil =>
              apply Finset.Subset.trans (mappedBit_wires b y cin cin).2.2
              intro q hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                or_false,mappedWires,List.flatMap_cons,List.flatMap_nil] at hq ⊢
              tauto
            | cons d' ds => simp [program,wires]
          | cons b' bs => simp [program,wires]
        | cons y' ys =>
          cases bs with
          | nil => simp [program,wires]
          | cons b' bs =>
            cases ds with
            | nil => simp [program,wires]
            | cons d' ds =>
              cases carry with
              | nil => simp [program,wires]
              | cons c cs =>
                intro q hq
                simp only [program,wires_append,Finset.mem_union] at hq
                have p := prepare_support b' d' y' c
                have r := ih (b'::bs) (d'::ds) cs c
                have e := (mappedBit_wires b y cin c).2.1
                have z := (mappedBit_wires b y cin c).2.2
                rcases hq with ((hq|hq)|hq)|hq
                · have h := p hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := r hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := e hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto
                · have h := z hq
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
                    or_false,mappedWires,List.flatMap_cons] at h ⊢
                  tauto

end ECDSAAdd.Arithmetic.KnownOutputAdder

#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.sumBits_value
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.ready_of_value
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.program_counts
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.prepare_correct
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.program_eq_mappedAdd
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.program_correct
#print axioms ECDSAAdd.Arithmetic.KnownOutputAdder.program_support
