import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Baselines.SlotAlgebra

namespace ECDSAAdd.Entrant.KnownLastCarry
open Arithmetic

def topBit : MappedBit := ⟨none,true⟩

def two (b b' : MappedBit) (y y' c cin : Wire) : Program :=
  KnownOutputAdder.prepare b' topBit y' c ++ mappedSum b' y' c ++
    mappedEraseCarry b y cin c ++ mappedSum b y cin

theorem two_eq (b b' : MappedBit) (y y' c cin : Wire)
    (hn : [cin,y,y',c].Nodup)
    (ha : ∀q∈mappedWires [b,b'],q∉[cin,y,y',c])
    (s : State) (m : List Bool) (clean : s.basis c=false)
    (top : sumBit (b'.value s.basis) (s.basis y')
      (carryBit (b.value s.basis) (s.basis y) (s.basis cin))=true) :
    run (two b b' y y' c cin) m s=run (mappedAdd [b,b'] [y,y'] [c] cin) m s := by
  let low : MappedBit := ⟨none,sumBit (b.value s.basis) (s.basis y) (s.basis cin)⟩
  have ready : KnownOutputAdder.Ready [b,b'] [low,topBit] [y,y'] (s.basis cin) s.basis := by
    simp only [KnownOutputAdder.Ready,KnownOutputAdder.sumBits,List.map_cons,List.map_nil,
      List.cons.injEq,low,topBit,MappedBit.value,Option.map_none,Option.getD_none,Bool.xor_false]
    exact ⟨trivial,top.symm,trivial⟩
  have eq := KnownOutputAdder.program_eq_mappedAdd [b,b'] [low,topBit] [y,y'] [c] cin
    hn ha (by simp [low,topBit,mappedWires]) rfl rfl rfl s m
    (by simpa using clean) ready
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using eq

theorem two_counts (b b' : MappedBit) (y y' c cin : Wire) :
    toffoliCount (two b b' y y' c cin)=0 ∧ measurementCount (two b b' y y' c cin)=1 := by
  have cnt := KnownOutputAdder.program_counts [b,b'] [topBit,topBit] [y,y'] [c] cin rfl rfl rfl
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using cnt

theorem two_physical (b b' : MappedBit) (y y' c cin : Wire)
    (hn : [cin,y,y',c].Nodup)
    (ha : ∀q∈mappedWires [b,b'],q∉[cin,y,y',c]) :
    GatePhysical (two b b' y y' c cin) := by
  have p := KnownOutputAdder.program_physical [b,b'] [topBit,topBit] [y,y'] [c] cin
    rfl rfl rfl hn (by
      intro bit hbit q hq
      apply ha q
      exact List.mem_flatMap.mpr ⟨bit,hbit,by simpa using hq⟩) (by simp [topBit])
  simpa only [KnownOutputAdder.program,two,List.append_assoc] using p

/-- Ordinary adder until its two-bit tail, where the top output is known. -/
def program : List Wire → List Wire → List Wire → Wire → Program
  | [a,a'],[b,b'],[c],cin => two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin
  | a::a'::as,b::b'::bs,c::cs,cin =>
      majority a b cin c ++ program (a'::as) (b'::bs) cs c ++
        eraseCarry a b cin c ++ [.CX a b,.CX cin b]
  | [a],[b],[],cin => [.CX a b,.CX cin b]
  | _,_,_,_ => []

theorem program_counts (xs ys carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (program xs ys carry cin)=ys.length-2 ∧
    measurementCount (program xs ys carry cin)=ys.length-1 := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      simp [program,toffoliCount,measurementCount]
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        simpa only [program,List.length_cons,List.length_nil] using two_counts ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin
      | cons a'' as =>
        have hi := ih (b'::bs) cs c (by simpa using hl) (by simpa using hc)
        have cap : 2≤(b'::bs).length := by simp only [List.length_cons] at hl ⊢;omega
        simp only [program,toffoliCount_append,measurementCount_append,
          hi.1,hi.2]
        simp only [majority,eraseCarry,toffoliCount,measurementCount,List.length_cons]
        simp only [List.length_cons] at hl hc cap
        constructor <;> omega

theorem sumBits_congr (xs ys : List Wire) (cin : Bool) (s t : BasisState)
    (hx : ∀q∈xs,s q=t q) (hy : ∀q∈ys,s q=t q) :
    KnownOutputAdder.sumBits (mappedRead xs false) ys cin s=
      KnownOutputAdder.sumBits (mappedRead xs false) ys cin t := by
  induction xs generalizing ys cin with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      have aeq := hx a (by simp)
      have beq := hy b (by simp)
      simp only [mappedRead,List.map_cons,KnownOutputAdder.sumBits,MappedBit.value,
        Option.map_some,Option.getD_some,Bool.false_xor]
      rw [aeq,beq]
      congr 1
      exact ih ys _ (fun q hq => hx q (by simp [hq])) (fun q hq => hy q (by simp [hq]))

theorem read_add (xs ys carry : List Wire) (cin : Wire) :
    mappedAdd (mappedRead xs false) ys carry cin=addInPlace xs ys carry cin := by
  induction xs generalizing ys carry cin with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons a' xs =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons b' ys =>
          cases carry with
          | nil => rfl
          | cons c cs =>
            simp only [mappedRead,List.map_cons,mappedAdd,mappedMajority,
              mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false,addInPlace]
            rw [←ih (b'::ys) cs c]
            rfl

theorem program_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (top : (KnownOutputAdder.sumBits (mappedRead xs false) ys (s.basis cin) s.basis).getLastD false=true) :
    run (program xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  induction xs generalizing ys carry cin s m with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      rfl
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      have cnt (q : Wire) := List.nodup_iff_count.mp hn q
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        have nd : [cin,b,b',c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have away : ∀q∈mappedWires [⟨some a,false⟩,⟨some a',false⟩],q∉[cin,b,b',c] := by
          intro q hq bad
          have l : q∈[a,a'] := by simpa [mappedWires] using hq
          have h := cnt q
          have lp := List.count_pos_iff.mpr l
          have rp := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h lp rp
          omega
        have tp : sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=true := by
          simpa [mappedRead,KnownOutputAdder.sumBits,MappedBit.value] using top
        have leaf := two_eq ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin nd away s m
          (clean c (by simp)) (by simpa [MappedBit.value] using tp)
        change run (two _ _ _ _ _ _) _ _=_
        rw [←read_add]
        exact leaf
      | cons a'' as =>
        have nd : (c::(a'::a''::as)++(b'::bs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have nd4 : [a,b,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have fresh (q : Wire) (hq : q∈(a'::a''::as)++(b'::bs)++cs) : q≠c := by
          intro eq
          have p := List.count_pos_iff.mpr hq
          have h := cnt q
          subst q
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h p
          omega
        let K := carryBit (s.basis a) (s.basis b) (s.basis cin)
        let u : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q∈(a'::a''::as)++(b'::bs)++cs) : u.basis q=s.basis q := by
          simp [u,writeBit,fresh q hq]
        have cu : u.basis c=K := by simp [u,writeBit]
        have preRun (r : List Bool) : run (majority a b cin c) r s=u := by
          rw [majority_correct _ _ _ _ nd4]
          simp [u,K,clean c (by simp)]
        have tailTop : (KnownOutputAdder.sumBits (mappedRead (a'::a''::as) false)
            (b'::bs) (u.basis c) u.basis).getLastD false=true := by
          rw [cu,sumBits_congr _ _ _ u.basis s.basis
            (fun q hq => keep q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto))
            (fun q hq => keep q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto))]
          simpa only [mappedRead,List.map_cons,KnownOutputAdder.sumBits,MappedBit.value,
            Option.map_some,Option.getD_some,Bool.false_xor,List.getLastD_cons,K] using top
        have tc : ∀q∈cs,u.basis q=false := by
          intro q hq
          rw [keep q (by simp [hq])]
          exact clean q (by simp [hq])
        have tail (r : List Bool) := ih (b'::bs) cs c nd (by simpa using hl) (by simpa using hc) u r tc tailTop
        have nm := (program_counts (a'::a''::as) (b'::bs) cs c (by simpa using hl) (by simpa using hc)).2
        have om := (addInPlace_counts (a'::a''::as) (b'::bs) cs c (by simpa using hl) (by simpa using hc)).2
        have zero : measurementCount (majority a b cin c)=0 := rfl
        rw [program,addInPlace]
        simp only [List.append_assoc,run_append,run_take,zero,nm,om,List.take_zero,List.drop_zero]
        simp only [preRun,tail]
        all_goals simp

theorem two_resources (a a' b b' c cin : Wire) :
    wires (two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin) ⊆
      wires (addInPlace [a,a'] [b,b'] [c] cin) ∧
    Challenge.gateSlots (two ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin) ≤
      Challenge.gateSlots (addInPlace [a,a'] [b,b'] [c] cin) := by
  constructor
  · intro q hq
    simp only [two,topBit,KnownOutputAdder.prepare,KnownOutputAdder.xorBit,
      mappedSum,mappedEraseCarry,Bool.false_eq_true,if_false,if_true,
      addInPlace,majority,eraseCarry,wires_append,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at hq ⊢
    tauto
  · simp [two,topBit,KnownOutputAdder.prepare,KnownOutputAdder.xorBit,
      mappedSum,mappedEraseCarry,addInPlace,majority,eraseCarry,
      Challenge.gateSlots,Challenge.instructionSlots]

theorem program_resources (xs ys carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    wires (program xs ys carry cin) ⊆ wires (addInPlace xs ys carry cin) ∧
    Challenge.gateSlots (program xs ys carry cin) ≤ Challenge.gateSlots (addInPlace xs ys carry cin) := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      simp [program,addInPlace]
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        exact two_resources a a' b b' c cin
      | cons a'' as =>
        have side := ih (b'::bs) cs c (by simpa using hl) (by simpa using hc)
        rw [program,addInPlace]
        constructor
        · simp only [wires_append]
          exact Finset.union_subset_union (Finset.union_subset_union
            (Finset.union_subset_union (Finset.Subset.refl _) side.1) (Finset.Subset.refl _)) (Finset.Subset.refl _)
        · simp only [Challenge.gateSlots_append]
          have le := side.2
          omega
        all_goals simp

theorem program_physical (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    GatePhysical (program xs ys carry cin) := by
  induction xs generalizing ys carry cin with
  | nil => simp at hl hc;omega
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨b,rfl⟩ : ∃b,ys=[b] := by
        cases ys with
        | nil => simp at hl
        | cons b ys => have e : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm);subst ys;exact ⟨b,rfl⟩
      have e : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst carry
      exact addInPlace_physical [a] [b] [] cin hn
    | cons a' as =>
      obtain ⟨b,b',bs,rfl⟩ : ∃b b' bs,ys=b::b'::bs := by
        match ys,hl with
        | b::b'::bs,_ => exact ⟨b,b',bs,rfl⟩
        | [],h => simp at h
        | [_],h => simp at h
      obtain ⟨c,cs,rfl⟩ : ∃c cs,carry=c::cs := by
        match carry,hc with
        | c::cs,_ => exact ⟨c,cs,rfl⟩
        | [],h => simp at h
      have cnt (q : Wire) := List.nodup_iff_count.mp hn q
      cases as with
      | nil =>
        have eb : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons,List.length_nil] at hc hl;omega)
        subst bs;subst cs
        have nd : [cin,b,b',c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have away : ∀q∈mappedWires [⟨some a,false⟩,⟨some a',false⟩],q∉[cin,b,b',c] := by
          intro q hq bad
          have l : q∈[a,a'] := by simpa [mappedWires] using hq
          have h := cnt q
          have lp := List.count_pos_iff.mpr l
          have rp := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,List.count_nil] at h lp rp
          omega
        exact two_physical ⟨some a,false⟩ ⟨some a',false⟩ b b' c cin nd away
      | cons a'' as =>
        have nd : (c::(a'::a''::as)++(b'::bs)++cs).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have tail := ih (b'::bs) cs c nd (by simpa using hl) (by simpa using hc)
        have old := addInPlace_physical (a::a'::a''::as) (b::b'::bs) (c::cs) cin hn
        rw [program]
        · simp only [addInPlace,gatePhysical_append] at old ⊢
          tauto
        · simp

theorem boolValue_read (xs : List Wire) (s : BasisState) :
    KnownOutputAdder.boolValue (xs.map s)=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : s a <;> simp [KnownOutputAdder.boolValue,regValue,ih,h]

theorem sumBits_output (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (clean : ∀q∈carry,s.basis q=false) :
    KnownOutputAdder.sumBits (mappedRead xs false) ys (s.basis cin) s.basis=
      ys.map (run (addInPlace xs ys carry cin) [] s).basis := by
  have old := addInPlace_correct xs ys carry cin hn hl hc s [] clean
  apply KnownOutputAdder.boolValue_injective
  · simp only [List.length_map]
    exact KnownOutputAdder.sumBits_length (mappedRead xs false) ys (s.basis cin) s.basis (by simpa [mappedRead] using hl)
  · rw [KnownOutputAdder.sumBits_value (mappedRead xs false) ys (s.basis cin) s.basis (by simpa [mappedRead] using hl),boolValue_read,mappedRead_value,old.2.2]

theorem program_eq_of_top_output (xs low carry : List Wire) (top cin : Wire)
    (hn : (cin::xs++(low++[top])++carry).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (ht : (run (addInPlace xs (low++[top]) carry cin) [] s).basis top=true) :
    run (program xs (low++[top]) carry cin) m s=run (addInPlace xs (low++[top]) carry cin) m s := by
  apply program_eq xs (low++[top]) carry cin hn hl hc s m clean
  rw [sumBits_output xs (low++[top]) carry cin hn hl hc s clean]
  simpa using ht

end ECDSAAdd.Entrant.KnownLastCarry
#print axioms ECDSAAdd.Entrant.KnownLastCarry.two_eq

#print axioms ECDSAAdd.Entrant.KnownLastCarry.program_eq

#print axioms ECDSAAdd.Entrant.KnownLastCarry.program_physical
