import ECDSAAdd.Submission.Entrant.FrontierEntrySignMath
import ECDSAAdd.Arithmetic.MappedAdder

/-! Affine source bits are read through local Clifford views. The views
return before the carry recursion uses another source bit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5.Affine
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run

def parity : List Wire → BasisState → Bool
  | [],_ => false
  | q::qs,s => s q ^^ parity qs s

def fan (qs : List Wire) (a : Wire) : Program := qs.map (fun q => Instr.CX q a)

theorem parity_congr (qs : List Wire) (s t : BasisState)
    (h : ∀q∈qs,s q=t q) : parity qs s=parity qs t := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [parity,h q (by simp),ih (fun q hq => h q (by simp [hq]))]

theorem fan_counts (qs : List Wire) (a : Wire) :
    toffoliCount (fan qs a)=0 ∧ measurementCount (fan qs a)=0 := by
  induction qs with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs ih => simpa only [fan,List.map_cons,toffoliCount,measurementCount] using ih

theorem fan_proper (qs : List Wire) (a : Wire) (ha : a∉qs) : ProperProgram (fan qs a) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun e => ha (e ▸ hq)

theorem fan_correct (qs : List Wire) (a : Wire) (ha : a∉qs) (s : State) (m : List Bool) :
    run (fan qs a) m s=⟨s.phase,writeBit s.basis a (s.basis a ^^ parity qs s.basis)⟩ := by
  induction qs generalizing s with
  | nil => simp [fan,run,parity,writeBit]
  | cons q qs ih =>
    have qa : q≠a := fun e => ha (by simp [e])
    have tail : a∉qs := fun h => ha (by simp [h])
    let t : State := ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩
    have same : parity qs t.basis=parity qs s.basis := by
      apply parity_congr
      intro b hb
      simp [t,writeBit,show b≠a from fun e => tail (e ▸ hb)]
    simp only [fan,List.map_cons,run]
    change run (fan qs a) m t=_
    rw [ih tail,same]
    apply State.extensionality
    · rfl
    · funext b
      by_cases ba : b=a
      · subst b
        simp [t,writeBit,parity,Bool.xor_assoc]
      · simp [t,writeBit,ba]

structure Bit where
  wire : Wire
  terms : List Wire

def Bit.wires (b : Bit) : List Wire := b.wire::b.terms
def Bit.value (b : Bit) (s : BasisState) : Bool := s b.wire ^^ parity b.terms s
def Bit.Valid (b : Bit) : Prop := b.wire∉b.terms

def value : List Bit → BasisState → Nat
  | [],_ => 0
  | b::bs,s => (b.value s).toNat+2*value bs s

def sites (bs : List Bit) : List Wire := bs.flatMap Bit.wires

def view (b : Bit) : Program := fan b.terms b.wire

def majority (b : Bit) (y cin co : Wire) : Program :=
  view b++Arithmetic.majority b.wire y cin co++(view b).reverse

def erase (b : Bit) (y cin co : Wire) : Program :=
  view b++eraseCarry b.wire y cin co++(view b).reverse

def sum (b : Bit) (y cin : Wire) : Program := fan b.wires y++[.CX cin y]

def add : List Bit → List Wire → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,c::cs,cin => majority b y cin c++add (b'::bs) (y'::ys) cs c++erase b y cin c++sum b y cin
  | [b],[y],_,cin => sum b y cin
  | _,_,_,_ => []

/-- A local view can be undone after a disjoint target update, including
an independently measured update. -/
theorem unview_write (b : Bit) (hb : b.Valid) (q : Wire)
    (hq : q∉wires (view b)) (s : State) (v : Bool) (m : List Bool) :
    run (view b).reverse m ⟨(run (view b) [] s).phase,writeBit (run (view b) [] s).basis q v⟩=
      ⟨s.phase,writeBit s.basis q v⟩ := by
  let t : State := ⟨(run (view b) [] s).phase,writeBit (run (view b) [] s).basis q v⟩
  have p : ProperProgram (view b) := fan_proper _ _ hb
  have e : BalancedCleanup.Except q t (run (view b) [] s) := by
    refine ⟨rfl,?_⟩
    intro a ha
    simp [t,writeBit,ha]
  have h := BalancedCleanup.inverse_except (view b) p q hq s t [] m e
  apply State.extensionality
  · exact h.1
  · funext a
    by_cases aq : a=q
    · subst a
      have keep := run_preserves_outside (view b).reverse m t q (by rwa [wires_reverse])
      simpa only [t,writeBit,Function.update_self] using keep
    · simpa only [writeBit,Function.update_of_ne aq] using h.2 a aq

theorem fan_support (qs : List Wire) (a : Wire) : wires (fan qs a)⊆(a::qs).toFinset := by
  induction qs with
  | nil => simp [fan,wires]
  | cons q qs ih =>
    intro x hx
    simp only [fan,List.map_cons,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with (rfl|rfl)|hx
    · simp
    · simp
    · have h := ih hx
      simp only [List.mem_toFinset,List.mem_cons] at h ⊢
      tauto

theorem Bit.value_congr (b : Bit) (s t : BasisState)
    (h : ∀q∈b.wires,s q=t q) : b.value s=b.value t := by
  rw [Bit.value,Bit.value,h _ (by simp [Bit.wires]),parity_congr _ _ _ (fun q hq => h q (by simp [Bit.wires,hq]))]

theorem value_congr (bs : List Bit) (s t : BasisState)
    (h : ∀q∈sites bs,s q=t q) : value bs s=value bs t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [value,value,Bit.value_congr b s t (fun q hq => h q (by simp [sites,hq])),ih (fun q hq => h q (by simp [sites] at hq ⊢;tauto))]

theorem view_value (b : Bit) (hb : b.Valid) (s : State) :
    (run (view b) [] s).basis b.wire=b.value s.basis := by
  rw [view,fan_correct _ _ hb]
  simp [writeBit,Bit.value]

theorem view_other (b : Bit) (hb : b.Valid) (s : State) (q : Wire) (hq : q≠b.wire) :
    (run (view b) [] s).basis q=s.basis q := by
  rw [view,fan_correct _ _ hb]
  simp [writeBit,hq]

theorem view_away (b : Bit) (q : Wire) (hq : q∉b.wires) : q∉wires (view b) :=
  fun h => hq (List.mem_toFinset.mp (fan_support _ _ h))

theorem majority_correct (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool) :
    run (majority b y cin co) m s=⟨s.phase,writeBit s.basis co
      (s.basis co ^^ carryBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  have nd : [b.wire,y,cin,co].Nodup := List.nodup_cons.mpr ⟨ha _ (by simp [Bit.wires]),hn⟩
  have away (q : Wire) (hq : q∈[y,cin,co]) : q≠b.wire := fun e => ha _ (by simp [Bit.wires]) (e ▸ hq)
  have h := Arithmetic.majority_correct b.wire y cin co nd (run (view b) [] s) m
  rw [view_value b hb s,view_other b hb s y (away _ (by simp)),
    view_other b hb s cin (away _ (by simp)),view_other b hb s co (away _ (by simp))] at h
  have z : measurementCount (view b)=0 := (fan_counts _ _).2
  rw [majority,List.append_assoc,run_append,z,List.take_zero,List.drop_zero,run_append,run_take,h]
  exact unview_write b hb co (view_away b co (fun h => ha co h (by simp))) s _ _

theorem erase_correct (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool)
    (hc : s.basis co=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
    run (erase b y cin co) m s=⟨s.phase,writeBit s.basis co false⟩ := by
  have a := ha b.wire (by simp [Bit.wires])
  have ay : b.wire≠y := fun e => a (by simp [e])
  have ai : b.wire≠cin := fun e => a (by simp [e])
  have ac : b.wire≠co := fun e => a (by simp [e])
  have yc : y≠co := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
  have ic : cin≠co := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [e])
  have h := eraseCarry_correct b.wire y cin co ac yc ic (run (view b) [] s)
    (by rw [view_value b hb s,view_other b hb s y ay.symm,view_other b hb s cin ai.symm,
      view_other b hb s co ac.symm];exact hc) m
  have z : measurementCount (view b)=0 := (fan_counts _ _).2
  rw [erase,List.append_assoc,run_append,z,List.take_zero,List.drop_zero,run_append,run_take,h]
  exact unview_write b hb co (view_away b co (fun h => ha co h (by simp))) s false _

theorem sum_correct (b : Bit) (y cin : Wire) (hc : cin≠y)
    (ha : ∀q∈b.wires,q≠y) (s : State) (m : List Bool) :
    run (sum b y cin) m s=⟨s.phase,writeBit s.basis y
      (sumBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  have yb : y∉b.wires := fun h => ha y h rfl
  have first := fan_correct b.wires y yb s []
  have ci : (run (fan b.wires y) [] s).basis cin=s.basis cin := by
    rw [first];simp [writeBit,hc]
  rw [sum,run_append,(fan_counts _ _).2,List.take_zero,List.drop_zero,first]
  apply State.extensionality
  · simp only [run]
  · funext q
    by_cases qy : q=y
    · subst q
      simp [run,writeBit,hc,parity,Bit.wires,Bit.value,sumBit,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
    · simp [run,writeBit,qy]

theorem head_mem (b : Bit) (bs : List Bit) (q : Wire) (hq : q∈b.wires) : q∈sites (b::bs) := by
  simp only [sites,List.flatMap_cons,List.mem_append]
  exact Or.inl hq

theorem tail_mem (b : Bit) (bs : List Bit) (q : Wire) (hq : q∈sites bs) : q∈sites (b::bs) := by
  simp only [sites,List.flatMap_cons,List.mem_append] at hq ⊢
  exact Or.inr hq

theorem bit_counts (b : Bit) (y cin co : Wire) :
    toffoliCount (majority b y cin co)=1 ∧ measurementCount (majority b y cin co)=0 ∧
    toffoliCount (erase b y cin co)=0 ∧ measurementCount (erase b y cin co)=1 ∧
    toffoliCount (sum b y cin)=0 ∧ measurementCount (sum b y cin)=0 := by
  have v := fan_counts b.terms b.wire
  have u := fan_counts b.wires y
  simp only [majority,erase,sum,view,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,v.1,v.2,u.1,u.2,Arithmetic.majority,eraseCarry,toffoliCount,measurementCount]
  decide

theorem add_correct (bits : List Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    (run (add bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (add bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (add bits ys carry cin) m s).basis=
      (value bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
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
      have bitAway (q : Wire) (hq : q∈b.wires) : q∉cin::((y::ys)++carry) :=
        hs q (head_mem b bits q hq)
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        have ha : ∀q∈b.wires,q≠y := by
          intro q hq bad
          exact bitAway q hq (by simp [bad])
        rw [add,sum_correct b y cin hcy ha]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          simp [writeBit,hq]
        · simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,
            Function.update_self,List.length_cons,List.length_nil,value]
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
            have hbaway : ∀q∈b.wires,q∉[y,cin,c] := by
              intro q hq bad
              exact bitAway q hq (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have nd' : (c::((y'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have src' : ∀q∈sites (b'::bits),q∉c::((y'::ys)++cs) := by
              intro q hq bad
              exact hs q (tail_mem b (b'::bits) q hq)
                (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have sourceAwayC (q : Wire) (hq : q∈sites (b::b'::bits)) : q≠c := by
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
            have first (record : List Bool) : run (majority b y cin c) record s=s1 := by
              rw [majority_correct b (hvalid b (by simp)) y cin c h3 hbaway]
              simp [s1,K,A,B,C,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            obtain ⟨hp,he,hv⟩ := ih (b'::bits) cs c nd' src'
              (by simpa using hl) (by simpa using hc) s1 m clean'
              (fun b hb => hvalid b (by simp [hb]))
            let t := run (add (b'::bits) (y'::ys) cs c) m s1
            have ht : t.phase=s.phase := hp
            have ty : t.basis y=B := (he y hyytail).trans (keep y hyc)
            have ti : t.basis cin=C := (he cin hcintail).trans (keep cin hcc)
            have tk : t.basis c=K := by rw [he c hcytail]; simp [s1,writeBit]
            have ta : b.value t.basis=A := by
              apply Bit.value_congr b t.basis s.basis
              intro q hq
              have away := bitAway q hq
              have yt : q∉y'::ys := fun bad => away
                (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem y bad)))
              exact (he q yt).trans (keep q (sourceAwayC q (head_mem b (b'::bits) q hq)))
            have clear (record : List Bool) : run (erase b y cin c) record t=
                ⟨t.phase,writeBit t.basis c false⟩ := by
              apply erase_correct b (hvalid b (by simp)) y cin c h3 hbaway t record
              rw [ta,ty,ti,tk]
            let u : State := ⟨t.phase,writeBit t.basis c false⟩
            have uy : u.basis y=B := by simp [u,writeBit,hyc,ty]
            have ui : u.basis cin=C := by simp [u,writeBit,hcc,ti]
            have ua : b.value u.basis=A := by
              apply Eq.trans (Bit.value_congr b u.basis t.basis ?_) ta
              intro q hq
              simp [u,writeBit,sourceAwayC q (head_mem b (b'::bits) q hq)]
            have finish (record : List Bool) : run (sum b y cin) record u=
                ⟨t.phase,writeBit u.basis y (sumBit A B C)⟩ := by
              rw [sum_correct b y cin hcy (by
                intro q hq bad; exact bitAway q hq (by simp [bad])),ua,uy,ui]
            have mh := bit_counts b y cin c
            rw [add]
            simp only [List.append_assoc,run_append,run_take,mh.2.1,List.take_zero,List.drop_zero]
            rw [first]
            change (run (sum b y cin) _ (run (erase b y cin c) _ t)).phase=_ ∧ _
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
              have sourceValue : value (b'::bits) s1.basis=value (b'::bits) s.basis := by
                apply value_congr
                intro q hq
                exact keep q (sourceAwayC q (tail_mem b (b'::bits) q hq))
              have yValue : regValue (y'::ys) s1.basis=regValue (y'::ys) s.basis :=
                regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcytail (bad ▸ hq)))
              have kc : s1.basis c=K := by simp [s1,writeBit]
              change (if (writeBit u.basis y (sumBit A B C)) y then 1 else 0)+
                  2*regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=_
              rw [show (writeBit u.basis y (sumBit A B C)) y=sumBit A B C by simp [writeBit],
                tailValue,hv,sourceValue,yValue,kc]
              have num := sum_value_step A B C (value (b'::bits) s.basis)
                (regValue (y'::ys) s.basis) (y'::ys).length
              simpa only [regValue,List.foldr_cons,value,List.length_cons,
                Bool.toNat,Bool.cond_eq_ite,A,B,C,K] using num

theorem add_counts (bits : List Bit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (add bits ys carry cin)=ys.length-1 ∧
    measurementCount (add bits ys carry cin)=ys.length-1 := by
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
        simpa [add] using
          And.intro (bit_counts b y cin cin).2.2.2.2.1
            (bit_counts b y cin cin).2.2.2.2.2
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (b'::bits) cs c (by simpa using hl) (by simpa using hc)
            have head := bit_counts b y cin c
            rw [add]
            constructor
            · simp only [toffoliCount_append,head.1,head.2.2.1,head.2.2.2.2.1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,head.2.1,head.2.2.2.1,head.2.2.2.2.2]
              rw [h.2]
              simp

end ECDSAAdd.Entrant.EntryRetained5.Affine
