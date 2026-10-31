import ECDSAAdd.Submission.Entrant.MainA
import ECDSAAdd.Submission.Entrant.LowZero
import ECDSAAdd.Submission.Entrant.TrimRow
import ECDSAAdd.Submission.Entrant.TrimSq3

-- ===== ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Primitive =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.DiagSquare
-- consolidated import: import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical

/-! Known-output sum cleanup from accepted b53aedf5, commit8764679c.
Donor: DiagSquare.lean, SHA256da5a012d90b45a5b4f0d993c07b286918dc436a7818b12608e1c6aca89bfb968.
Only the675T sum-cleanup change is ported. The old leaf programs and register
layout are retained. KRegs has new, distinct helper names; no old declaration changes.
-/
-- Known-output sum cleanup.
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Primitive
open Arithmetic

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

def sub (xs ys expected carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++KnownOutputAdder.program (mappedRead xs false) ys
    (mappedRead expected true) carry cin++notRegister ys

theorem sub_eq (xs ys expected carry : List Wire) (cin : Wire)
    (hn : (cin::ys++carry).Nodup)
    (hx : ∀q∈xs,q∉cin::ys++carry) (he : ∀q∈expected,q∉cin::ys++carry)
    (hl : xs.length=ys.length) (hel : expected.length=ys.length)
    (hcl : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hc0 : ∀q∈carry,s.basis q=false) (hi0 : s.basis cin=false)
    (hval : regValue ys s.basis=regValue xs s.basis+regValue expected s.basis) :
    run (sub xs ys expected carry cin) m s=run (subInPlace xs ys carry cin) m s := by
  let u := run (notRegister ys) [] s
  have nd : ys.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  have yc : cin∉ys := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : ys.Disjoint carry := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
  have out (q : Wire) (hq : q∉ys) : u.basis q=s.basis q := by
    dsimp only [u]
    rw [notRegister_correct ys nd]
    simp [hq]
  have ux : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => out q (fun h => hx q hq (by simp [h])))
  have ue : regValue expected u.basis=regValue expected s.basis :=
    regValue_congr _ _ _ (fun q hq => out q (fun h => he q hq (by simp [h])))
  have uy : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    dsimp only [u]
    rw [notRegister_correct ys nd]
    have e : regValue ys (fun w => if w∈ys then !s.basis w else s.basis w)=regValue ys (fun w => !s.basis w) :=
      regValue_congr _ _ _ (fun q hq => by simp [hq])
    rw [e,regValue_complement]
  have ui : u.basis cin=false := (out cin yc).trans hi0
  have uc : ∀q∈carry,u.basis q=false := by
    intro q hq
    exact (out q (fun h => List.disjoint_left.mp dis h hq)).trans (hc0 q hq)
  have known : KnownOutputAdder.Ready (mappedRead xs false) (mappedRead expected true) ys
      (u.basis cin) u.basis := by
    apply KnownOutputAdder.ready_of_value
    · exact (mappedRead_length xs false).trans hl
    · exact (mappedRead_length expected true).trans hel
    rw [mappedRead_complement,mappedRead_value,hel,ux,ue,uy,ui]
    simp only [Bool.toNat_false,Nat.add_zero]
    have hy := regValue_lt ys s.basis
    have hp := Nat.two_pow_pos ys.length
    have small : regValue xs s.basis+(2^ys.length-1-regValue ys s.basis)<2^ys.length := by omega
    rw [Nat.mod_eq_of_lt small]
    omega
  have eq (record : List Bool) := KnownOutputAdder.program_eq_mappedAdd (mappedRead xs false)
    (mappedRead expected true) ys carry cin hn (by simpa only [mappedRead_wires] using hx)
    (by simpa only [mappedRead_wires] using he) ((mappedRead_length xs false).trans hl) ((mappedRead_length expected true).trans hel) hcl u record uc known
  simp only [read_add] at eq
  have mz := (notRegister_counts ys).2
  have counts := KnownOutputAdder.program_counts (mappedRead xs false) (mappedRead expected true)
    ys carry cin ((mappedRead_length xs false).trans hl) ((mappedRead_length expected true).trans hel) hcl
  have old := addInPlace_counts xs ys carry cin hl hcl
  have pre : run (notRegister ys) m s=u := by
    rw [←run_take (notRegister ys) m s,mz,List.take_zero]
  simp only [sub,subInPlace,List.append_assoc,run_append,run_take,mz,List.drop_zero,counts.2,old.2,pre]
  simp only [List.take_zero]
  exact congrArg (fun t => run (notRegister ys) (m.drop (ys.length-1)) t) (eq (m.take (ys.length-1)))

end ECDSAAdd.Entrant.FrontierSumCleanup1591Primitive


namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Primitive
open Arithmetic Challenge

theorem sub_counts (xs ys expected carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (he : expected.length=ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (sub xs ys expected carry cin)=0 ∧
    measurementCount (sub xs ys expected carry cin)=ys.length-1 := by
  have a:=KnownOutputAdder.program_counts (mappedRead xs false) (mappedRead expected true) ys carry cin
    ((mappedRead_length _ _).trans hl) ((mappedRead_length _ _).trans he) hc
  have b:=notRegister_counts ys
  simp only [sub,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  simp

theorem sub_support (xs ys expected carry : List Wire) (cin : Wire) :
    wires (sub xs ys expected carry cin)⊆(cin::xs++ys++expected++carry).toFinset := by
  have h:=KnownOutputAdder.program_support (mappedRead xs false) (mappedRead expected true) ys carry cin
  simp only [mappedRead_wires] at h
  intro q hq
  simp only [sub,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with (hq|hq)|hq
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  · have hq:=h hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢; tauto
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto

theorem sub_physical (xs ys expected carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (he : expected.length=ys.length)
    (hc : carry.length+1=ys.length) (hn : (cin::ys++carry).Nodup)
    (hx : ∀q∈xs,q∉cin::ys++carry) (hex : ∀q∈expected,q∉cin::ys++carry) :
    GatePhysical (sub xs ys expected carry cin) := by
  have h:=KnownOutputAdder.program_physical (mappedRead xs false) (mappedRead expected true) ys carry cin
    ((mappedRead_length _ _).trans hl) ((mappedRead_length _ _).trans he) hc hn
  have bx : ∀b∈mappedRead xs false,∀q∈b.wire,q∉cin::ys++carry := by
    intro b hb q hq
    apply hx q
    rw [←mappedRead_wires xs false]
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  have be : ∀b∈mappedRead expected true,∀q∈b.wire,q∉cin::ys++carry := by
    intro b hb q hq
    apply hex q
    rw [←mappedRead_wires expected true]
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  simpa only [sub,gatePhysical_append] using And.intro (And.intro (notRegister_physical ys) (h bx be)) (notRegister_physical ys)

theorem xorBit_slots (b : MappedBit) (t : Wire) : gateSlots (KnownOutputAdder.xorBit b t)≤2 := by
  cases hw:b.wire <;> cases hf:b.flip <;>
    simp [KnownOutputAdder.xorBit,hw,hf,gateSlots,instructionSlots]

theorem prepare_slots (a d : MappedBit) (y c : Wire) : gateSlots (KnownOutputAdder.prepare a d y c)≤5 := by
  have a:=xorBit_slots a c
  have b:=xorBit_slots d c
  simp only [KnownOutputAdder.prepare,gateSlots_append]
  have h: gateSlots ([Instr.CX y c] : Program)=1 := rfl
  omega

theorem program_slots (xs ys : List Wire) (sums : List MappedBit) (carry : List Wire) (cin : Wire) :
    gateSlots (KnownOutputAdder.program (mappedRead xs false) ys sums carry cin)≤
      gateSlots (addInPlace xs ys carry cin) := by
  induction xs generalizing ys sums carry cin with
  | nil => cases ys <;> cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
      | cons b ys =>
        cases ys with
        | nil =>
          cases sums with
          | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
          | cons d ds => cases ds <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,mappedSum,gateSlots,instructionSlots]
        | cons b' ys => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
    | cons a' xs =>
      cases ys with
      | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
      | cons b ys =>
        cases ys with
        | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
        | cons b' ys =>
          cases sums with
          | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
          | cons d ds =>
            cases ds with
            | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
            | cons d' ds =>
              cases carry with
              | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
              | cons c cs =>
                have ht:=ih (b'::ys) (d'::ds) cs c
                have hp:=prepare_slots ({wire:=some a',flip:=false} : MappedBit) d' b' c
                simp only [mappedRead,List.map_cons,KnownOutputAdder.program,addInPlace,
                  gateSlots_append,mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false] at ht hp ⊢
                have hm : gateSlots (majority a b cin c)=6 := rfl
                simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,instructionSlots] at ht hp ⊢
                omega

theorem sub_slots (xs ys expected carry : List Wire) (cin : Wire) :
    gateSlots (sub xs ys expected carry cin)≤gateSlots (subInPlace xs ys carry cin) := by
  have h:=program_slots xs ys (mappedRead expected true) carry cin
  simp only [sub,subInPlace,gateSlots_append]
  omega
end ECDSAAdd.Entrant.FrontierSumCleanup1591Primitive


namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)

def sumExpected1591 : List Wire := R.lo++R.z.take (R.S.length-R.lo.length)
def scl1591 : Program := FrontierSumCleanup1591Primitive.sub (R.hi++R.zS) R.S R.sumExpected1591
  (R.carry.take (R.S.length-1)) R.cin++R.m3

theorem sumExpected1591_length (w : R.W) : R.sumExpected1591.length=R.S.length := by
  have h4:=w.h4; have hh:=w.hh; have h5:=w.h5; have hS:=w.S; have hz:=w.z
  have lens:=R.lens w
  simp only [sumExpected1591,List.length_append,List.length_take,lens.1]
  omega

theorem sumExpected1591_value (w : R.W) (s : BasisState) (hz : regValue R.z s=0) :
    regValue R.sumExpected1591 s=regValue R.lo s := by
  have z : regValue (R.z.take (R.S.length-R.lo.length)) s=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (List.mem_of_mem_take hq))
  simp [sumExpected1591,regValue_append,z]

theorem scl1591_fresh (hn : R.all.Nodup) :
    (∀q∈R.hi++R.zS,q∉R.cin::R.S++R.carry.take (R.S.length-1)) ∧
    (∀q∈R.sumExpected1591,q∉R.cin::R.S++R.carry.take (R.S.length-1)) := by
  have aux (q : Wire) (hq : q∈R.bank ∨ q∈R.z) : q∉R.cin::R.S++R.carry.take (R.S.length-1) := by
    intro bad
    have cnt:=List.nodup_iff_count.mp hn q
    have ck:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    have cb:=List.count_pos_iff.mpr bad
    simp only [all,List.count_cons,List.count_append] at cnt cb
    rcases hq with hq|hq <;> have pos:=List.count_pos_iff.mpr hq <;> omega
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact aux q (Or.inl (List.mem_of_mem_drop (show q∈R.bank.drop R.h from hq)))
    · exact aux q (Or.inr (List.mem_of_mem_take (show q∈R.z.take 1 from hq)))
  · intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact aux q (Or.inl (List.mem_of_mem_take (show q∈R.bank.take R.h from hq)))
    · exact aux q (Or.inr (List.mem_of_mem_take hq))

theorem scl1591_eq (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hS : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) : run R.scl1591 m s=run R.scl m s := by
  have h4:=w.h4; have hh:=w.hh; have h5:=w.h5; have hSlen:=w.S; have hcl:=w.carry
  have ln:=R.lens w
  have nd : (R.cin::R.S++R.carry.take (R.S.length-1)).Nodup := by
    apply knd hn
    intro q
    have ct:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    simp only [all,List.count_cons,List.count_append]
    omega
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by
    simp only [List.length_take]; omega
  have zero : regValue R.zS s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz0 q (List.mem_of_mem_take (show q∈R.z.take 1 from hq)))
  have value : regValue R.S s.basis=regValue (R.hi++R.zS) s.basis+regValue R.sumExpected1591 s.basis := by
    rw [regValue_append,zero,R.sumExpected1591_value w s.basis hz0,hS]; omega
  have eq (record : List Bool) := FrontierSumCleanup1591Primitive.sub_eq (R.hi++R.zS) R.S R.sumExpected1591
    (R.carry.take (R.S.length-1)) R.cin nd (R.scl1591_fresh hn).1 (R.scl1591_fresh hn).2
    lens (R.sumExpected1591_length w) car s record
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) hi0 value
  have count:=FrontierSumCleanup1591Primitive.sub_counts (R.hi++R.zS) R.S R.sumExpected1591
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected1591_length w) car
  have old:=subInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin lens car
  simp only [scl1591,scl,c4,run_append,count.2,old.2]
  rw [eq]

theorem scl1591_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hS : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) :
    (run R.scl1591 m s).phase=s.phase ∧ regValue R.S (run R.scl1591 m s).basis=0 ∧
    ∀q,q∉R.S → (run R.scl1591 m s).basis q=s.basis q := by
  rw [R.scl1591_eq w hn s m hS hz0 hc0 hi0]
  exact R.scl_correct w hn s m hS hz0 hc0 hi0

theorem scl1591_counts (w : R.W) : toffoliCount R.scl1591=0 ∧
    measurementCount R.scl1591=R.bank.length-R.h := by
  have ln:=R.lens w
  have h4:=w.h4;have hh:=w.hh;have h5:=w.h5;have hS:=w.S;have hcl:=w.carry
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by simp only [List.length_take]; omega
  have a:=FrontierSumCleanup1591Primitive.sub_counts (R.hi++R.zS) R.S R.sumExpected1591
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected1591_length w) car
  have b:=copyRegister_counts none R.lo (R.S.take R.h) (by rw [ln.1,ln.2.2.2.2.2.2.2.2.2.1])
  simp only [scl1591,m3,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    Option.isSome_none,Bool.false_eq_true,if_false]
  constructor
  · trivial
  · rw [hS]; omega

theorem scl1591_slots : Challenge.gateSlots R.scl1591≤Challenge.gateSlots R.scl := by
  have h:=FrontierSumCleanup1591Primitive.sub_slots (R.hi++R.zS) R.S R.sumExpected1591 (R.carry.take (R.S.length-1)) R.cin
  simp only [scl1591,scl,c4,Challenge.gateSlots_append]
  omega

theorem scl1591_support (w : R.W) : wires R.scl1591⊆R.all.toFinset := by
  have a:=FrontierSumCleanup1591Primitive.sub_support (R.hi++R.zS) R.S R.sumExpected1591 (R.carry.take (R.S.length-1)) R.cin
  have p:=copyRegister_wires_subset none R.lo (R.S.take R.h)
  intro q hq
  simp only [scl1591,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have hq:=a hq
    simp only [sumExpected1591,lo,hi,zS,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq|hq|hq
    · simp [all,hq.symm]
    · have h:=List.mem_of_mem_drop hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · simp [all,hq]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]

  · have hq:=p hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h:=List.mem_of_mem_take (show q∈R.bank.take R.h from hq);simp [all,h]
    · have h:=List.mem_of_mem_take hq;simp [all,h]

theorem scl1591_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.scl1591 := by
  have h4:=w.h4;have hh:=w.hh;have h5:=w.h5;have hS:=w.S;have hcl:=w.carry
  have ln:=R.lens w
  have nd : (R.cin::R.S++R.carry.take (R.S.length-1)).Nodup := by
    apply knd hn;intro q
    have ct:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    simp only [all,List.count_cons,List.count_append];omega
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by simp only [List.length_take];omega
  have a:=FrontierSumCleanup1591Primitive.sub_physical (R.hi++R.zS) R.S R.sumExpected1591
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected1591_length w) car nd
    (R.scl1591_fresh hn).1 (R.scl1591_fresh hn).2
  have ndcp : (R.lo++R.S.take R.h).Nodup := by
    apply knd hn;intro q
    have cb:=(List.take_sublist R.h R.bank).count_le q
    have cs:=(List.take_sublist R.h R.S).count_le q
    simp only [all,lo,List.count_cons,List.count_append];omega
  have cp:=copyRegister_physical none R.lo (R.S.take R.h) ndcp (by simp)
  simpa only [scl1591,m3,gatePhysical_append] using And.intro a cp
/-! Low-bit carry trims (LowZero): each `*z` program drops the dead bit-0 carry of the
corresponding Karatsuba combination adder. -/
theorem m8z_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
theorem t_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem lo_lens (w : R.W) : (R.dlo++R.zA).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dlo++R.zA).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem T_ne (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dhi_ne (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dlo_ne (w : R.W) : R.dlo≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
def m8z : Program := LowZero.addLow0G (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem m8z_counts (w : R.W) : toffoliCount R.m8z+1=toffoliCount R.m8 ∧
    measurementCount R.m8z=measurementCount R.m8 := by
  have l := R.m8z_lens w
  unfold m8z; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2
theorem m8z_wires : wires R.m8z⊆wires R.m8 := LowZero.addLow0G_wires_sub _ _ _ _
theorem m8z_slots : Challenge.gateSlots R.m8z≤Challenge.gateSlots R.m8 := LowZero.addLow0G_slots _ _ _ _
theorem m8z_physical (hn : R.all.Nodup) : GatePhysical R.m8z :=
  LowZero.addLow0G_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8z m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.m8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8z m s).basis=(regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  unfold m8z; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT (R.T_ne w)) hi

def m7z : Program := LowZero.subLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7z_counts (w : R.W) : toffoliCount R.m7z+1=toffoliCount R.m7 ∧
    measurementCount R.m7z=measurementCount R.m7 := by
  have l := R.t_lens w
  unfold m7z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m7z_wires : wires R.m7z⊆wires R.m7 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m7z_slots : Challenge.gateSlots R.m7z≤Challenge.gateSlots R.m7 := LowZero.subLowNCG_slots _ _ _ _
theorem m7z_physical (hn : R.all.Nodup) : GatePhysical R.m7z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7z m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  unfold m7z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c8z : Program := LowZero.subLowNCG (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem c8z_counts (w : R.W) : toffoliCount R.c8z+1=toffoliCount R.c8 ∧
    measurementCount R.c8z=measurementCount R.c8 := by
  have l := R.m8z_lens w
  unfold c8z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2
theorem c8z_wires : wires R.c8z⊆wires R.c8 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem c8z_slots : Challenge.gateSlots R.c8z≤Challenge.gateSlots R.c8 := LowZero.subLowNCG_slots _ _ _ _
theorem c8z_physical (hn : R.all.Nodup) : GatePhysical R.c8z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8z m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8z m s).basis=(regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  unfold c8z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi

def c7z : Program := LowZero.addLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7z_counts (w : R.W) : toffoliCount R.c7z+1=toffoliCount R.c7 ∧
    measurementCount R.c7z=measurementCount R.c7 := by
  have l := R.t_lens w
  unfold c7z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_wires : wires R.c7z⊆wires R.c7 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c7z_slots : Challenge.gateSlots R.c7z≤Challenge.gateSlots R.c7 := LowZero.addLowNCG_slots _ _ _ _
theorem c7z_physical (hn : R.all.Nodup) : GatePhysical R.c7z :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7z m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  unfold c7z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def m6z : Program := LowZero.subLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6z_counts (w : R.W) : toffoliCount R.m6z+1=toffoliCount R.m6 ∧
    measurementCount R.m6z=measurementCount R.m6 := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m6z_wires : wires R.m6z⊆wires R.m6 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m6z_slots : Challenge.gateSlots R.m6z≤Challenge.gateSlots R.m6 := LowZero.subLowNCG_slots _ _ _ _
theorem m6z_physical (hn : R.all.Nodup) : GatePhysical R.m6z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6z m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c6z : Program := LowZero.addLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6z_counts (w : R.W) : toffoliCount R.c6z+1=toffoliCount R.c6 ∧
    measurementCount R.c6z=measurementCount R.c6 := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c6z_wires : wires R.c6z⊆wires R.c6 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c6z_slots : Challenge.gateSlots R.c6z≤Challenge.gateSlots R.c6 := LowZero.addLowNCG_slots _ _ _ _
theorem c6z_physical (hn : R.all.Nodup) : GatePhysical R.c6z :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6z m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs


end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Core =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Primitive

/-!675T port: the old diagonal leaves and the old KG register descriptors remain.
The generic known-sum KG proofs are from acceptedb53 DiagSquare1886..2401.
The diagonal transitions reuse our accepted old DiagSq public Shape lemmas.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- `rawMake` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawMakeT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.mk xs dst pad carry

/-- `rawClear` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawClearT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.cl xs dst pad carry

theorem rawMakeT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeT xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.mk_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawMakeT,hR]
  exact rawMake_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawClearT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearT xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.cl_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawClearT,hR]
  exact rawClear_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (rawMakeT xs dst pad carry)+1=toffoliCount (rawMake xs dst pad carry) ∧
      measurementCount (rawMakeT xs dst pad carry)+1=measurementCount (rawMake xs dst pad carry)) ∧
    (toffoliCount (rawClearT xs dst pad carry)+1=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1=measurementCount (rawClear xs dst pad carry)) :=
  ECDSAAdd.Entrant.TrimRow.counts xs dst pad carry hx hd hp hc

theorem rawT_slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawMakeT xs dst pad carry)≤Challenge.gateSlots (rawMake xs dst pad carry) ∧
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry

theorem rawT_wires (xs dst pad carry : List Wire) (X : Finset Wire)
    (h1 : wires (signedSquareRows xs dst pad carry)⊆X) (h2 : wires (signedSquareTop xs dst)⊆X)
    (h3 : wires (signedSquareRowsClear xs dst pad carry)⊆X) :
    wires (rawMakeT xs dst pad carry)⊆X ∧ wires (rawClearT xs dst pad carry)⊆X := by
  have w := ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry
  simp only [wires_append] at w
  exact ⟨w.1.trans (Finset.union_subset h1 h2),w.2.trans (Finset.union_subset h2 h3)⟩

theorem rawT_physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry)) (h2 : GatePhysical (signedSquareTop xs dst))
    (h3 : GatePhysical (signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (rawMakeT xs dst pad carry) ∧ GatePhysical (rawClearT xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,h3⟩)


def seedsT (R : KRegs) : Program :=
  rawMakeT R.lo R.dlo R.pad R.carry ++ rawMakeT R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMakeT R.S R.T R.pad R.carry

theorem seedsT_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seedsT R) m s)
      (vec (rawValue R.h (regValue R.lo s.basis)) (rawValue R.h (regValue R.hi s.basis))
        (regValue R.lo s.basis+regValue R.hi s.basis)
        (rawValue (R.h+1) (regValue R.lo s.basis+regValue R.hi s.basis))) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hpl := w.pad
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have init : Shape R s s (vec 0 0 0 0) := by
    refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro i; fin_cases i
    · change (regValue R.dlo s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dlo) hd0 (fun q h => List.mem_of_mem_take h)]; rfl
    · change (regValue R.dhi s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dhi) hd0 (fun q h => List.mem_of_mem_drop h)]; rfl
    · change (regValue R.S s.basis : Int) ≡ 0 [ZMOD _]
      rw [hS0]; rfl
    · change (regValue R.T s.basis : Int) ≡ 0 [ZMOD _]
      rw [hT0]; rfl
  have loStep : Transition R s (vec 0 0 0 0) (vec (rawValue R.h a) 0 0 0)
      (rawMakeT R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMakeT_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMakeT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMakeT R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMakeT_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMakeT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h b : Nat) [ZMOD (2^(reg R 1).length : Nat)] := by
      change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,ht0,hhi]; rfl
    simpa only [vec1] using ht.step hn 1 (rawValue R.h b) r.1 r.2.2 v
  have sumStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0) R.smk := by
    intro t rec ht
    have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := R.smk_correct w hn t rec (ht.exact 2 0 rfl (by norm_num))
      ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
    have v : (regValue (reg R 2) (run R.smk rec t).basis : Int) ≡ (a+b : Nat) [ZMOD (2^(reg R 2).length : Nat)] := by
      change (regValue R.S _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,al,bl]
    simpa only [vec2] using ht.step hn 2 (a+b : Nat) r.1 r.2.2 v
  have sqStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) (rawValue (R.h+1) (a+b)))
      (rawMakeT R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMakeT_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMakeT R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init



theorem rawClearT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawClearT xs dst pad carry)⊆wires (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear; exact (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).2
theorem rawClearT_slots_le (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear; exact (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).2
theorem rawClearT_physical_of (xs dst pad carry : List Wire) (hm : GatePhysical (rawMake xs dst pad carry))
    (hc : GatePhysical (rawClear xs dst pad carry)) : GatePhysical (rawClearT xs dst pad carry) := by
  unfold rawClearT; exact (ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry hm hc).2
theorem rawClearT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rawClearT xs dst pad carry)+1=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1=measurementCount (rawClear xs dst pad carry) :=
  (rawT_counts xs dst pad carry hx hd hp hc).2

theorem rawclearlo_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClearT R.lo R.dlo R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.lo.length=R.h := by omega
  have hdlen : R.dlo.length=2*R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have rb := rawValue_bound R.lo base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 0 (rawValue R.h (regValue R.lo base.basis)) rfl
    (by change _<2^R.dlo.length; rw [hdlen]; exact rb)
  change regValue R.dlo t.basis=_ at dv
  have r := rawClearT_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClearT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClearT R.hi R.dhi R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.hi.length=R.h := by omega
  have hdlen : R.dhi.length=2*R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have rb := rawValue_bound R.hi base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 1 (rawValue R.h (regValue R.hi base.basis)) rfl
    (by change _<2^R.dhi.length; rw [hdlen]; exact rb)
  change regValue R.dhi t.basis=_ at dv
  have r := rawClearT_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClearT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transitionT (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClearT R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClearT_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClearT R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

end ECDSAAdd.Entrant.DiagSq

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- A register whose value is congruent to an even integer modulo `2^len` (`len ≥ 1`) has
its lowest wire clear. -/
theorem head_false_of_modEq (r : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T) :
    st (r.headD 0)=false := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have hd : (2:Int)∣(regValue r st : Int) := by
    have m := (Int.ModEq.dvd hv.symm)
    have := dvd_trans h2 m
    have e : (regValue r st : Int)=T+((regValue r st : Int)-T) := by ring
    rw [e]; exact dvd_add hT this
  obtain ⟨k,hk⟩ := hd
  have hk' : regValue r st=2*k.toNat := by omega
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have := LowZero.head_false_of_even r [] st k.toNat hk' ne
  simpa using this

theorem addhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hTe : (2:Int)∣T) :
    Transition R base (vec A B S T) (vec A B S (T+B)) R.c7z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have t0 : t.basis (R.T.headD 0)=false :=
    head_false_of_modEq R.T t.basis T (by omega) (ht.value 3) hTe
  have c := R.c7z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [t0]; exact Bool.and_false _) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dhi++R.zB) t.basis : Int) t (run R.c7z rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem rawValue_even (n x : Nat) (hn : 1≤n) : 2∣rawValue n x := by
  unfold rawValue signedDiagValue
  rw [if_neg (by omega)]
  have h1 : 2∣x^2+x := by
    rw [show x^2+x=x*(x+1) by ring]; exact (Nat.even_mul_succ_self x).two_dvd
  have h2 : 2∣(2^(n-1)-1-x%2^(n-1))*2^n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  rw [show x^2+(x+(2^(n-1)-1-x%2^(n-1))*2^n)=(x^2+x)+(2^(n-1)-1-x%2^(n-1))*2^n by ring]
  exact dvd_add h1 h2

theorem subloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T-A)) R.m6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have l := R.lo_lens w
  have c := R.m6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6z rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hBe : 2∣B) :
    Transition R base (vec A B S T) (vec A B S (T-B)) R.m7z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dhi++R.zB).headD 0)=false := by
    obtain ⟨k,hk⟩ := hBe
    exact LowZero.head_false_of_even R.dhi R.zB t.basis k (by rw [xv,hk]) (R.dhi_ne w)
  have l := R.t_lens w
  have c := R.m7z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dhi++R.zB) t.basis : Int)) t (run R.m7z rec t) := by
    have vl := regValue_lt (R.dhi++R.zB) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dhi++R.zB) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have c := R.c6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6z rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act


def headBlockZ (R : KRegs) : Program := seedsT R ++ (R.m6z++R.m7z++corr R++
  mappedDiagSub R.lo R.dlo R.carry R.cin++mappedDiagSub R.hi R.dhi R.carry R.cin)

/-- `make` with the dead lowest carries of `m6`, `m7`, `m8` dropped. -/
def makeZ (R : KRegs) : Program := headBlockZ R++R.m8z

theorem makeZ_counts_rel (R : KRegs) (w : R.W) :
    toffoliCount (makeZ R)+6=toffoliCount (make R) ∧ measurementCount (makeZ R)+3=measurementCount (make R) := by
  have a := R.m6z_counts w; have b := R.m7z_counts w; have c := R.m8z_counts w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have t1 := rawT_counts R.lo R.dlo R.pad R.carry (by simp only [KRegs.lo,List.length_take]; omega)
    (by simp only [KRegs.lo,KRegs.dlo,List.length_take]; omega) hpl
    (by simp only [KRegs.lo,List.length_take]; omega)
  have t2 := rawT_counts R.hi R.dhi R.pad R.carry (by simp only [KRegs.hi,List.length_drop]; omega)
    (by simp only [KRegs.hi,KRegs.dhi,List.length_drop]; omega) hpl
    (by simp only [KRegs.hi,List.length_drop]; omega)
  have t5 := rawT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem makeZ_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (makeZ R)+6=cost R ∧ measurementCount (makeZ R)+3=cost R := by
  have a := makeZ_counts_rel R w
  have b := make_counts R w he
  constructor <;> omega

theorem rawMakeT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawMakeT xs dst pad carry)⊆wires (rawMake xs dst pad carry) := by
  unfold rawMakeT rawMake; exact (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).1

theorem seedsT_wires (R : KRegs) : wires (seedsT R)⊆wires (seeds R) := by
  simp only [seedsT,seeds,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
    (rawMakeT_wires_sub _ _ _ _) (rawMakeT_wires_sub _ _ _ _)) (subset_refl _)) (rawMakeT_wires_sub _ _ _ _)

theorem makeZ_support (R : KRegs) (w : R.W) : wires (makeZ R)⊆R.all.toFinset := by
  have old := (steps_support R w).1
  have a := R.m6z_wires; have b := R.m7z_wires; have c := R.m8z_wires
  have d := seedsT_wires R
  simp only [make,headBlock,wires_append,Finset.union_subset_iff] at old
  simp only [makeZ,headBlockZ,wires_append,Finset.union_subset_iff]
  obtain ⟨⟨o1,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  exact ⟨⟨d.trans o1,⟨⟨⟨⟨a.trans o2,b.trans o3⟩,o4⟩,o5⟩,o6⟩⟩,c.trans o7⟩

theorem makeZ_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeZ R) := by
  have old := (steps_physical R w hn).1
  have oldc := (steps_physical R w hn).2
  simp only [make,headBlock,seeds,rawMake,gatePhysical_append] at old
  simp only [clear,rawClear,gatePhysical_append] at oldc
  simp only [makeZ,headBlockZ,seedsT,gatePhysical_append]
  obtain ⟨⟨⟨⟨⟨⟨l1,l2⟩,⟨h1,h2⟩⟩,sm⟩,⟨s1,s2⟩⟩,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  have pl := ECDSAAdd.Entrant.TrimRow.physical R.lo R.dlo R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨l1,l2⟩) (by rw [gatePhysical_append]; exact ⟨l2,by tauto⟩)
  have ph := ECDSAAdd.Entrant.TrimRow.physical R.hi R.dhi R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,by tauto⟩)
  have ps := ECDSAAdd.Entrant.TrimRow.physical R.S R.T R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨s1,s2⟩) (by rw [gatePhysical_append]; exact ⟨s2,by tauto⟩)
  exact ⟨⟨⟨⟨⟨pl.1,ph.1⟩,sm⟩,ps.1⟩,⟨⟨⟨⟨R.m6z_physical hn,R.m7z_physical hn⟩,o4⟩,o5⟩,o6⟩⟩,R.m8z_physical hn⟩

theorem makeZ_slots (R : KRegs) : Challenge.gateSlots (makeZ R)≤Challenge.gateSlots (make R) := by
  have a := R.m6z_slots; have b := R.m7z_slots; have c := R.m8z_slots
  have t1 := (ECDSAAdd.Entrant.TrimRow.slots R.lo R.dlo R.pad R.carry).1
  have t2 := (ECDSAAdd.Entrant.TrimRow.slots R.hi R.dhi R.pad R.carry).1
  have t5 := (ECDSAAdd.Entrant.TrimRow.slots R.S R.T R.pad R.carry).1
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,rawMakeT,rawMake,Challenge.gateSlots_append] at t1 t2 t5 ⊢
  omega

theorem prefixZ_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlockZ R) m s)
      (vec ((regValue R.lo s.basis)^2) ((regValue R.hi s.basis)^2)
        (regValue R.lo s.basis+regValue R.hi s.basis) (2*regValue R.lo s.basis*regValue R.hi s.basis)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hhi : R.hi.length=R.h := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have st1 := subloZ_transition R w hn s hz0 hc0 hi0 A B S Z hA (rawValue_even _ _ (by omega))
  have st2 := subhiZ_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB (rawValue_even _ _ (by omega))
  have st3 := corr_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B)
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  rw [norm] at st3
  have st4 := diagsublo_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat)
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (mappedDiagSub R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := diagsubhi_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat)
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (mappedDiagSub R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seedsT_shape R w he hn s (m.take (measurementCount (seedsT R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seedsT R))) initial
  simpa only [headBlockZ,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem makeZ_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (makeZ R) m s).phase=s.phase ∧
    regValue R.dst (run (makeZ R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (makeZ R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (makeZ R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (makeZ R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlockZ R))
  let g := m.drop (measurementCount (headBlockZ R))
  let u := run (headBlockZ R) f s
  have h := prefixZ_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have sq := square_bound (a+b) R.S.length slt
  have tvlt : 2*a*b<2^R.T.length := by rw [hTl]; omega
  have av : regValue R.dlo u.basis=a^2 := h.exact 0 (a^2) (by simp [vec,a,b])
    (by change a^2<2^R.dlo.length; rw [L2]; exact square_bound _ _ al)
  have bv : regValue R.dhi u.basis=b^2 := h.exact 1 (b^2) (by simp [vec,a,b])
    (by change b^2<2^R.dhi.length; rw [L3,show R.bank.length-R.h=R.h by omega]; exact square_bound _ _ bl)
  have sv : regValue R.S u.basis=a+b := h.exact 2 (a+b) (by simp [vec,a,b]) slt
  have tv : regValue R.T u.basis=2*a*b := h.exact 3 (2*a*b) (by simp [vec,a,b]) tvlt
  have dv : regValue R.dst u.basis=a^2+2^(2*R.h)*b^2 := by rw [R.dst_value w,av,bv]
  have cv := (h.keep hn R.carry (by intro q hq; simp [hq])).trans hc0
  have zv := (h.keep hn R.zM (fun q hq => Or.inr (Or.inl (List.mem_of_mem_take hq)))).trans
    (KRegs.xz (r:=R.zM) hz0 (fun q hq => List.mem_of_mem_take hq))
  have r := R.m8z_correct w hn u g (a*b) (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
    (by rw [tv]; ring) ((h.cin hn).trans hi0)
  have rv : regValue R.dmid (run R.m8z g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8z g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8z g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8z g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8z g u).phase=s.phase ∧ regValue R.dst (run R.m8z g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8z g u).basis=a+b ∧ regValue R.T (run R.m8z g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8z g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  simpa only [makeZ,run_append,u,f,g,a,b] using result

theorem clearZ_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run R.c8z m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hdl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^(R.bank.length-R.h) := by simpa only [L1] using regValue_lt R.hi s.basis
  have av : a^2<2^(2*R.h) := square_bound _ _ al
  have hd : regValue R.dst s.basis=(a+2^R.h*b)^2 := by
    simpa only [R.bank_value w s.basis] using hd0
  have XLt : (a+2^R.h*b)^2<2^(2*R.bank.length) := by
    rw [←R.bank_value w s.basis]
    exact square_bound _ _ (regValue_lt R.bank s.basis)
  have hX : (a+2^R.h*b)^2=(a^2+2^(2*R.h)*b^2)+2^R.h*(2*a*b) := by ring
  have hdiv : (a+2^R.h*b)^2/2^R.h=(a^2+2^(2*R.h)*b^2)/2^R.h+2*a*b := by
    rw [hX,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hmod : (a+2^R.h*b)^2%2^R.h=(a^2+2^(2*R.h)*b^2)%2^R.h := by
    rw [hX,Nat.add_mul_mod_self_left]
  have hq : (a+2^R.h*b)^2/2^R.h<2^(2*R.bank.length-R.h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),←pow_add,
      show 2*R.bank.length-R.h+R.h=2*R.bank.length by omega]
    exact XLt
  have r := R.c8z_correct w hn s m (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
    (by rw [LowZero.head_false_of_even R.T R.zM s.basis (a*b) (by rw [hT0]; ring) (R.T_ne w)]; rfl) hi0
  have frame : ∀q,q∉R.dmid → (run R.c8z m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8z m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8z m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8z m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8z m s).basis=regValue R.dst (run R.c8z m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8z m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8z m s).basis=regValue R.dst (run R.c8z m s).basis/2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt av,Nat.zero_add]
  have sv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hS0
  have tv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hT0
  refine ⟨r.1,?_,fun q hd _ _ => frame q (fun bad => hd (List.mem_of_mem_drop bad))⟩
  intro i; fin_cases i
  · change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
    rw [dlo]; exact Int.ModEq.rfl
  · change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
    rw [dhi]; exact Int.ModEq.rfl
  · change (regValue R.S _ : Int) ≡ _ [ZMOD _]
    rw [sv]; exact Int.ModEq.rfl
  · change (regValue R.T _ : Int) ≡ _ [ZMOD _]
    rw [tv]; exact Int.ModEq.rfl


end ECDSAAdd.Entrant.DiagSq

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Diagonal
open Arithmetic DiagSq KRegs

def clear (R : KRegs) : Program := R.c8z++(mappedDiagAdd R.lo R.dlo R.carry R.cin++
  mappedDiagAdd R.hi R.dhi R.carry R.cin++corrBack R++R.c7z++R.c6z++
  rawClearT R.S R.T R.pad R.carry++R.scl1591++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)

def makeC (R : KRegs) : Program := DiagSq.makeZ R++R.scl1591
def clearC (R : KRegs) : Program := R.smk++clear R

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl1591 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hs := w.S
  have hl : R.hi.length=R.h := by omega
  have av := regValue_lt R.lo base.basis; have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hl] at bv
  have hS : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [show R.S.length=R.h+1 by omega,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) hS
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have r := R.scl1591_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl1591 rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  let d : Int := ((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)-(2^(2*R.h-1) : Nat)
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have slt : S<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [S]; omega
  have st1 := diagaddlo_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat)
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (mappedDiagAdd R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := diagaddhi_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat)
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (mappedDiagAdd R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBack_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhiZ_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB (by
    apply dvd_add
    · push_cast; exact ⟨(a:Int)*b, by ring⟩
    · dsimp only [d]
      apply dvd_sub
      · apply Dvd.dvd.mul_right
        push_cast; exact dvd_pow_self 2 (by omega)
      · push_cast; exact dvd_pow_self 2 (by omega))
  have st5 := addloZ_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) hA (rawValue_even _ _ (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  rw [norm'] at st5
  have st6 := rawclearSum_transitionT R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transitionT R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transitionT R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBack R) := by
    (convert st3 using 1; try rfl)
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clearZ_start_shape R w he hn s (m.take (measurementCount R.c8z)) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount R.c8z)) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeZ R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.makeZ_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.makeZ R))
  let b := m.drop (measurementCount (DiagSq.makeZ R))
  have r := DiagSq.makeZ_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.makeZ R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

theorem diag_sq_cl_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clearC R) R.invC := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  let a := m.take (measurementCount R.smk)
  let b := m.drop (measurementCount R.smk)
  have r := R.smk_correct w hn s a hI.1 (xz hz0 hz) hc0 hi0
  generalize hu : run R.smk a s=u at r
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin ∨ q∈R.dst ∨ q∈R.T) : q∉R.S := by
    rcases h with h|h|h|h|h|h|h
    · exact (R.outside hn q (Or.inl h)).2.1
    · exact (R.outside hn q (Or.inr (Or.inl h))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.2 q (hl q hq))
  have bk := keep R.bank (fun q h => o q (Or.inl h))
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (clearC R) m s=run (clear R) b u := by
    rw [clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


theorem clear_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clear R)+(R.bank.length-R.h)+6=toffoliCount (DiagSq.clear R) ∧
    measurementCount (clear R)+3=measurementCount (DiagSq.clear R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z8 := R.c8z_counts w; have z7 := R.c7z_counts w; have z6 := R.c6z_counts w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have r1 := DiagSq.rawClearT_counts R.lo R.dlo R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r2 := DiagSq.rawClearT_counts R.hi R.dhi R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r5 := DiagSq.rawClearT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  simp only [clear,DiagSq.clear,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem makeC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (makeC R)+(R.bank.length-R.h)+6=toffoliCount (DiagSq.makeC R) ∧
    measurementCount (makeC R)+3=measurementCount (DiagSq.makeC R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z := DiagSq.makeZ_counts_rel R w
  simp only [makeC,DiagSq.makeC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clearC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clearC R)+(R.bank.length-R.h)+6=toffoliCount (DiagSq.clearC R) ∧
    measurementCount (clearC R)+3=measurementCount (DiagSq.clearC R) := by
  have h := clear_counts_diff R w
  simp only [clearC,DiagSq.clearC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clear_support (R : KRegs) (w : R.W) : wires (clear R)⊆R.all.toFinset := by
  have old := (DiagSq.steps_support R w).2
  have new := R.scl1591_support w
  have pcs := R.piece_support w
  have q2 := pcs.2.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at q2
  have c8w : wires R.c8z⊆R.all.toFinset := R.c8z_wires.trans q2.1.1
  have c7w : wires R.c7z⊆R.all.toFinset := R.c7z_wires.trans q2.1.2
  have c6w : wires R.c6z⊆R.all.toFinset := R.c6z_wires.trans q2.2
  clear q2 pcs
  simp only [clear,DiagSq.clear,wires_append,Finset.union_subset_iff] at old ⊢
  have rS : wires (rawClearT R.S R.T R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rH : wires (rawClearT R.hi R.dhi R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rL : wires (rawClearT R.lo R.dlo R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  tauto

theorem makeC_support (R : KRegs) (w : R.W) : wires (makeC R)⊆R.all.toFinset := by
  simpa only [makeC,wires_append,Finset.union_subset_iff] using
    And.intro (DiagSq.makeZ_support R w) (R.scl1591_support w)

theorem clearC_support (R : KRegs) (w : R.W) : wires (clearC R)⊆R.all.toFinset := by
  simpa only [clearC,wires_append,Finset.union_subset_iff] using
    And.intro (R.piece_support w).1 (clear_support R w)

theorem clear_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clear R) := by
  have old := (DiagSq.steps_physical R w hn).2
  have new := R.scl1591_physical w hn
  have z8 := R.c8z_physical hn; have z7 := R.c7z_physical hn; have z6 := R.c6z_physical hn
  have oldm := (DiagSq.steps_physical R w hn).1
  simp only [DiagSq.make,DiagSq.headBlock,DiagSq.seeds,gatePhysical_append] at oldm
  simp only [clear,DiagSq.clear,gatePhysical_append] at old ⊢
  have rS := DiagSq.rawClearT_physical_of R.S R.T R.pad R.carry (by tauto) (by tauto)
  have rH := DiagSq.rawClearT_physical_of R.hi R.dhi R.pad R.carry (by tauto) (by tauto)
  have rL := DiagSq.rawClearT_physical_of R.lo R.dlo R.pad R.carry (by tauto) (by tauto)
  tauto

theorem makeC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) := by
  simpa only [makeC,gatePhysical_append] using
    And.intro (DiagSq.makeZ_physical R w hn) (R.scl1591_physical w hn)

theorem clearC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clearC R) := by
  simpa only [clearC,gatePhysical_append] using
    And.intro (R.piece_physical hn).1 (clear_physical R w hn)

theorem clear_slots_le (R : KRegs) : Challenge.gateSlots (clear R)≤Challenge.gateSlots (DiagSq.clear R) := by
  have h := R.scl1591_slots
  have z8 := R.c8z_slots; have z7 := R.c7z_slots; have z6 := R.c6z_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  simp only [clear,DiagSq.clear,Challenge.gateSlots_append] at *
  omega

theorem makeC_slots_le (R : KRegs) : Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) := by
  have h := R.scl1591_slots
  have z := DiagSq.makeZ_slots R
  simp only [makeC,DiagSq.makeC,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_le (R : KRegs) : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (DiagSq.clearC R) := by
  have h := clear_slots_le R
  simp only [clearC,DiagSq.clearC,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.FrontierSumCleanup1591Diagonal

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591KG
open Arithmetic KG
variable (K : KG)
def make : Program := K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7z++K.R.m8z++K.R.scl1591
def clear : Program := K.R.smk++K.R.c8z++K.R.c7z++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c
theorem make_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=0) (hX0 : regValue K.X s.basis=0)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (make K) m s).phase=s.phase ∧
    regValue K.R.dst (run (make K) m s).basis=(regValue K.R.bank s.basis)^2 ∧
    regValue K.R.S (run (make K) m s).basis=0 ∧
    regValue K.R.T (run (make K) m s).basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis ∧
    K.I1 (regValue K.R.lo s.basis) (run (make K) m s).basis ∧
    K.I2 (regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (make K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have bv := K.R.bank_value w s.basis
  rw [bv]
  generalize ha : regValue K.R.lo s.basis=a
  generalize hb : regValue K.R.hi s.basis=b
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7z++K.R.m8z) K.R.scl1591 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7z) K.R.m8z a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6) K.R.m7z a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) K.R.m6 a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7z++K.R.m8z++K.R.scl1591 from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- Q1: a^2 into dlo
  have st1 := sp.mk1 s r1 (zero _ _ hd0 (fun q h => mt h)) (zero _ _ hX0 (fun q h => x1 h)) hp0 hc0 hz0 hi0
  rw [ha] at st1
  generalize run K.Q1 r1 s=s1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s1.basis q=s.basis q :=
    fun q h _ _ x => st1.2.2.2 q (fun y => h (mt y)) (fun y => x (x1 y))
  -- Q2: b^2 into dhi
  have dhi1 : regValue K.R.dhi s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hd0 (fun q h => md h))
  have X21 : regValue K.X2 s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x2 h))
  have hi1 : regValue K.R.hi s1.basis=b := (outV s1 G1 _ (fun q h => Or.inl (md h))).trans hb
  have st2 := sp.mk2 s1 r2 dhi1 X21 ((outV s1 G1 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s1 G1 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s1 G1 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [hi1] at st2
  generalize run K.Q2 r2 s1=s2 at st2 ⊢
  have F2 : ∀q,q∉K.R.dhi → q∉K.X2 → s2.basis q=s1.basis q := st2.2.2.2
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s2.basis q=s.basis q :=
    fun q h hS hT x => (F2 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo s2.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have I12 : K.I1 a s2.basis := sp.lc1 a s1.basis s2.basis (fun q hq => (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st1.2.2.1
  -- sum register
  have S2 : regValue K.R.S s2.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)))).trans hS0
  have st3 := K.R.smk_correct w hR s2 r3 S2 ((outV s2 G2 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  have lo2 : regValue K.R.lo s2.basis=a := (outV s2 G2 K.R.lo (fun q h => Or.inl (mt h))).trans ha
  have hi2 : regValue K.R.hi s2.basis=b := (outV s2 G2 K.R.hi (fun q h => Or.inl (md h))).trans hb
  rw [lo2,hi2] at st3
  generalize run K.R.smk r3 s2=s3 at st3 ⊢
  have F3 := st3.2.2
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s3.basis q=s.basis q :=
    fun q h hS hT x => (F3 q hS).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo s3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi s3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st2.2.1
  have I13 : K.I1 a s3.basis := sp.lc1 a s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I12
  have I23 : K.I2 b s3.basis := sp.lc2 b s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st2.2.2.1
  -- Q5: T = (a+b)^2
  have back3 (q : Wire) (h1 : q∉K.R.dlo) (h2 : q∉K.X1) (h3 : q∉K.R.dhi) (h4 : q∉K.X2) (h5 : q∉K.R.S) :
      s3.basis q=s.basis q :=
    (F3 q h5).trans ((F2 q h3 h4).trans (st1.2.2.2 q h1 h2))
  have T3 : regValue K.R.T s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have X53 : regValue K.X5 s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x5 h))
  have st5 := sp.mk5 s3 r4 T3 X53 ((outV s3 G3 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s3 G3 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [st3.2.1] at st5
  generalize run K.Q5 r4 s3=s5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → s5.basis q=s3.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G3 q h hS hT x)
  have dlo5 : regValue K.R.dlo s5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi5 : regValue K.R.dhi s5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S5 : regValue K.R.S s5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st3.2.1
  have I15 : K.I1 a s5.basis := sp.lc1 a s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I13
  have I25 : K.I2 b s5.basis := sp.lc2 b s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I23
  have sumLt : a+b<2^K.R.S.length := by
    have hp : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
    omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  -- T -= a^2
  have st6 : (run K.R.m6 r5 s5).phase=s5.phase ∧ regValue K.R.T (run K.R.m6 r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.m6 r5 s5).basis q=s5.basis q := by
    unfold KRegs.m6
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dlo++K.R.zA) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo5,outV s5 G5 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st5.2.1,G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt,ex]; omega
  generalize run K.R.m6 r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have st7 : (run K.R.m7z r6 s6).phase=s6.phase ∧ regValue K.R.T (run K.R.m7z r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run K.R.m7z r6 s6).basis q=s6.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m7z_correct w hR s6 r6
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_bit K.R.T [] s6.basis (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [LowZero.head_bit K.R.dhi K.R.zB s6.basis (K.R.dhi_ne w),hT,dhi6,st6.2.1,
          show 2*a*b+b^2=b^2+2*(a*b) by ring,Nat.add_mul_mod_self_left]
        cases decide (b^2%2=1) <;> rfl)
      ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run K.R.m7z r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run K.R.m8z r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run K.R.m8z r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run K.R.m8z r7 s7).basis q=s7.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m8z_correct w hR s7 r7 (a*b)
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [st7.2.1]; ring) ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run K.R.m8z r7 s7=s8 at st8 ⊢
  have G8 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s8.basis q=s.basis q :=
    fun q h hS hT x => (st8.2.2 q (fun y => h (md y))).trans (G7 q h hS hT x)
  have D8 : regValue K.R.dst s8.basis=(a+2^K.R.h*b)^2 := by
    rw [K.R.dst_value_mid w,st8.2.1,kkeep st8.2.2 (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),D7]
    exact KRegs.kfinal a b K.R.h K.R.bank.length aLt bLt (by omega)
  -- facts between s5 and s8: only T and dmid changed
  have back8 (q : Wire) (hT : q∉K.R.T) (hd : q∉K.R.dst) : s8.basis q=s5.basis q :=
    (st8.2.2 q (fun y => hd (md y))).trans ((st7.2.2 q hT).trans (st6.2.2 q hT))
  have S8 : regValue K.R.S s8.basis=a+b := (regValue_congr _ _ _ (fun q hq => back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S5
  have T8 : regValue K.R.T s8.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st8.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1
  have I18 : K.I1 a s8.basis := sp.lc1 a s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I15
  have I28 : K.I2 b s8.basis := sp.lc2 b s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I25
  have I58 : K.I5 (a+b) s8.basis := sp.lc5 (a+b) s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st5.2.2.1
  -- clean the sum register
  have st9 := K.R.scl1591_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r8 s8=s9 at st9 ⊢
  refine ⟨st9.1.trans (st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,st9.2.1,?_,?_,?_,?_,?_⟩
  · rw [←D8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · rw [←T8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · exact sp.lc1 a s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I18
  · exact sp.lc2 b s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I28
  · exact sp.lc5 (a+b) s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I58
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · exact ((regValue_zero _ _).mp st9.2.1 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (st9.2.2 q hS).trans (G8 q hd hS hT hx)

theorem clear_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=(regValue K.R.bank s.basis)^2) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis)
    (hI1 : K.I1 (regValue K.R.lo s.basis) s.basis) (hI2 : K.I2 (regValue K.R.hi s.basis) s.basis)
    (hI5 : K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) s.basis)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (clear K) m s).phase=s.phase ∧
    regValue K.R.dst (run (clear K) m s).basis=0 ∧
    regValue K.R.S (run (clear K) m s).basis=0 ∧
    regValue K.R.T (run (clear K) m s).basis=0 ∧
    regValue K.X (run (clear K) m s).basis=0 ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (clear K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  rw [K.R.bank_value w s.basis] at hd0
  generalize ha : regValue K.R.lo s.basis=a at hd0 hT0 hI1 hI5
  generalize hb : regValue K.R.hi s.basis=b at hd0 hT0 hI2 hI5
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  have hp2 : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
  have sumLt : a+b<2^K.R.S.length := by omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have hX : (a+2^K.R.h*b)^2=(a^2+2^(2*K.R.h)*b^2)+2^K.R.h*(2*a*b) := by ring
  have hpos : 0<2^K.R.h := Nat.two_pow_pos _
  have XLt : (a+2^K.R.h*b)^2<2^(2*K.R.bank.length) := by
    have hsplit : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
    have hm := Nat.mul_le_mul_left (2^K.R.h) (show b+1≤2^(K.R.bank.length-K.R.h) by omega)
    rw [Nat.mul_add,Nat.mul_one,←hsplit] at hm
    exact square_bound _ _ (by omega)
  have aSq : a^2<2^(2*K.R.h) := square_bound _ _ aLt
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7z++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7z++K.R.c6++K.Q5c++K.R.scl1591) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7z++K.R.c6++K.Q5c) K.R.scl1591 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7z++K.R.c6) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7z) K.R.c6 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++K.R.c8z) K.R.c7z a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk K.R.c8z a2 s
  rw [show (clear K)=K.R.smk++K.R.c8z++K.R.c7z++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run K.R.c8z r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run K.R.c8z r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run K.R.c8z r2 t1).basis q=t1.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c8z_correct w hR t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [LowZero.head_false_of_even K.R.T K.R.zM t1.basis (a*b) (by rw [T1]; ring) (K.R.T_ne w)]; rfl)
      ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [K.R.dst_value_mid w,v,kkeep f (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),regValue_append,T1,outV t1 G1 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),
      show regValue K.R.dmid t1.basis=regValue K.R.dst t1.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) t1.basis,D1,L4]
    have hdiv : (a+2^K.R.h*b)^2/2^K.R.h=(a^2+2^(2*K.R.h)*b^2)/2^K.R.h+2*a*b := by
      rw [hX,Nat.add_mul_div_left _ _ hpos]
    have hmod : (a+2^K.R.h*b)^2%2^K.R.h=(a^2+2^(2*K.R.h)*b^2)%2^K.R.h := by
      rw [hX,Nat.add_mul_mod_self_left]
    have hq : (a+2^K.R.h*b)^2/2^K.R.h<2^(2*K.R.bank.length-K.R.h) := by
      rw [Nat.div_lt_iff_lt_mul hpos,←pow_add,show 2*K.R.bank.length-K.R.h+K.R.h=2*K.R.bank.length by omega]
      exact XLt
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod ((a+2^K.R.h*b)^2/2^K.R.h) (2*a*b) _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  generalize run K.R.c8z r2 t1=t2 at st2 ⊢
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t2.basis q=s.basis q :=
    fun q h hS hT x => (st2.2.2 q (fun y => h (md y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo t2.basis=a^2 := by
    rw [show regValue K.R.dlo t2.basis=regValue K.R.dst t2.basis%2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt aSq]
  have dhi2 : regValue K.R.dhi t2.basis=b^2 := by
    rw [show regValue K.R.dhi t2.basis=regValue K.R.dst t2.basis/2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt aSq,Nat.zero_add]
  have S2 : regValue K.R.S t2.basis=a+b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have T2 : regValue K.R.T t2.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans T1
  -- T += b^2
  have st3 : (run K.R.c7z r3 t2).phase=t2.phase ∧ regValue K.R.T (run K.R.c7z r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.c7z r3 t2).basis q=t2.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c7z_correct w hR t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_false_of_even K.R.T [] t2.basis (a*b) (by rw [T2]; ring) (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [hT]; exact Bool.and_false _)
      ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run K.R.c7z r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run K.R.c6 r4 t3).phase=t3.phase ∧ regValue K.R.T (run K.R.c6 r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run K.R.c6 r4 t3).basis q=t3.basis q := by
    unfold KRegs.c6
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dlo++K.R.zA) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t3 r4
      (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo3,outV t3 G3 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st3.2.1,G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega),ex]; ring
  generalize run K.R.c6 r4 t3=t4 at st4 ⊢
  have G4 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t4.basis q=s.basis q :=
    fun q h hS hT x => (st4.2.2 q hT).trans (G3 q h hS hT x)
  have dlo4 : regValue K.R.dlo t4.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi4 : regValue K.R.dhi t4.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S4 : regValue K.R.S t4.basis=a+b := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S3
  have back4 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) : t4.basis q=s.basis q :=
    (st4.2.2 q h3).trans ((st3.2.2 q h3).trans ((st2.2.2 q (fun y => h2 (md y))).trans (st1.2.2 q h1)))
  -- clear T with the S-square cleanup
  have st5 := sp.cl5 t4 r5 (by rw [st4.2.1,S4])
    (by rw [S4]; exact sp.lc5 (a+b) s.basis t4.basis (fun q hq => (back4 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI5)
    ((outV t4 G4 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t4 G4 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t4 G4 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G4 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q5c r5 t4=t5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → t5.basis q=t4.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G4 q h hS hT x)
  have dlo5 : regValue K.R.dlo t5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo4
  have dhi5 : regValue K.R.dhi t5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi4
  have S5 : regValue K.R.S t5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S4
  -- clean S
  have st6 := K.R.scl1591_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r6 t5=t6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hS).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo t6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi t6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  have T6 : regValue K.R.T t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.1
  have X56 : regValue K.X5 t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.2.1
  have back6 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) (h4 : q∉K.X5) : t6.basis q=s.basis q :=
    (st6.2.2 q h1).trans ((F5 q h3 h4).trans (back4 q h1 h2 h3))
  -- clear b^2
  have st7 := sp.cl2 t6 r7
    (by rw [dhi6,(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    (by rw [(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb]
        exact sp.lc2 b s.basis t6.basis (fun q hq => (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI2)
    ((outV t6 G6 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t6 G6 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q2c r7 t6=t7 at st7 ⊢
  have F7 : ∀q,q∉K.R.dhi → q∉K.X2 → t7.basis q=t6.basis q := st7.2.2.2
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t7.basis q=s.basis q :=
    fun q h hS hT x => (F7 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo t7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  -- clear a^2
  have st8 := sp.cl1 t7 r8
    (by rw [dlo7,(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha])
    (by rw [(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha]
        exact sp.lc1 a s.basis t7.basis (fun q hq => ((F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).symm) hI1)
    ((outV t7 G7 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t7 G7 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t7 G7 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q1c r8 t7=t8 at st8 ⊢
  have F8 : ∀q,q∉K.R.dlo → q∉K.X1 → t8.basis q=t7.basis q := st8.2.2.2
  have k78 (r : List Wire) (h : ∀q∈r,q∉K.R.dlo ∧ q∉K.X1 ∧ q∉K.R.dhi ∧ q∉K.X2) :
      regValue r t8.basis=regValue r t6.basis :=
    regValue_congr _ _ _ (fun q hq => (F8 q (h q hq).1 (h q hq).2.1).trans (F7 q (h q hq).2.2.1 (h q hq).2.2.2))
  refine ⟨st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st4.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,?_,?_,?_,?_⟩
  · rw [K.R.dst_value w,st8.2.1,(regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1]; simp
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact st6.2.1
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact T6
  · rw [X,regValue_append,regValue_append,st8.2.2.1,
      (regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.2.1,
      k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩),X56]; simp
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · have a1 := (regValue_zero _ _).mp st6.2.1 q hS
      have a2 := (regValue_zero _ _).mp hS0 q hS
      rw [F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),a1,a2]
    · exact (F8 q (fun y => hd (mt y)) (fun y => hx (x1 y))).trans (G7 q hd hS hT hx)


theorem make_counts (w : K.R.W) :
    toffoliCount (make K)+2=toffoliCount K.Q1+toffoliCount K.Q2+toffoliCount K.Q5+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (make K)=measurementCount K.Q1+measurementCount K.Q2+measurementCount K.Q5+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mz := K.R.m8z_counts w
  have mz7 := K.R.m7z_counts w
  have e : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7z++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have q1 := p.2.2.2.2.1
  have q2 := p.2.2.2.2.2.1
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem clear_counts (w : K.R.W) :
    toffoliCount (clear K)+2=toffoliCount K.Q1c+toffoliCount K.Q2c+toffoliCount K.Q5c+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (clear K)=measurementCount K.Q1c+measurementCount K.Q2c+measurementCount K.Q5c+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mc8 := K.R.c8z_counts w
  have mc7 := K.R.c7z_counts w
  have e : (clear K)=K.R.smk++(K.R.c8z++K.R.c7z++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have q1 := p.2.2.2.2.2.2.1
  have q2 := p.2.2.2.2.2.2.2
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem r_sub (q : Wire) (h : q∈K.R.all.toFinset) : q∈K.all.toFinset := by
  simp only [List.mem_toFinset,all,List.mem_append] at h ⊢; exact Or.inl h

theorem steps_support (w : K.R.W)
    (s1 : ECDSAAdd.wires K.Q1⊆K.all.toFinset) (s1c : ECDSAAdd.wires K.Q1c⊆K.all.toFinset)
    (s2 : ECDSAAdd.wires K.Q2⊆K.all.toFinset) (s2c : ECDSAAdd.wires K.Q2c⊆K.all.toFinset)
    (s5 : ECDSAAdd.wires K.Q5⊆K.all.toFinset) (s5c : ECDSAAdd.wires K.Q5c⊆K.all.toFinset) :
    ECDSAAdd.wires (make K)⊆K.all.toFinset ∧ ECDSAAdd.wires (clear K)⊆K.all.toFinset := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7z++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7z++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have lift {P : Program} (h : ECDSAAdd.wires P⊆K.R.all.toFinset) : ECDSAAdd.wires P⊆K.all.toFinset :=
    fun q hq => K.r_sub q (h hq)
  have ap {P Q : Program} (h1 : ECDSAAdd.wires P⊆K.all.toFinset) (h2 : ECDSAAdd.wires Q⊆K.all.toFinset) :
      ECDSAAdd.wires (P++Q)⊆K.all.toFinset := by rw [wires_append]; exact Finset.union_subset h1 h2
  have pz : ECDSAAdd.wires (K.R.m6++K.R.m7z++K.R.m8z)⊆K.R.all.toFinset := by
    have h := p.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨h.1.1,K.R.m7z_wires.trans h.1.2⟩,K.R.m8z_wires.trans h.2⟩
  have cz : ECDSAAdd.wires (K.R.c8z++K.R.c7z++K.R.c6)⊆K.R.all.toFinset := by
    have h := p.2.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨K.R.c8z_wires.trans h.1.1,K.R.c7z_wires.trans h.1.2⟩,h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap s1 s2) (lift p.1)) s5) (lift pz)) (lift sc),
    ap (ap (ap (ap (ap (lift p.1) (lift cz)) s5c) (lift sc)) s2c) s1c⟩

theorem steps_physical (w : K.R.W) (hn : K.all.Nodup)
    (p1 : GatePhysical K.Q1) (p1c : GatePhysical K.Q1c) (p2 : GatePhysical K.Q2) (p2c : GatePhysical K.Q2c)
    (p5 : GatePhysical K.Q5) (p5c : GatePhysical K.Q5c) :
    GatePhysical (make K) ∧ GatePhysical (clear K) := by
  have p := K.R.piece_physical (K.rnd hn)
  have sc := K.R.scl1591_physical w (K.rnd hn)
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7z++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7z++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have pz : GatePhysical (K.R.m6++K.R.m7z++K.R.m8z) := by
    have h := p.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1,K.R.m7z_physical (K.rnd hn)⟩,K.R.m8z_physical (K.rnd hn)⟩
  have cz : GatePhysical (K.R.c8z++K.R.c7z++K.R.c6) := by
    have h := p.2.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.c8z_physical (K.rnd hn),K.R.c7z_physical (K.rnd hn)⟩,h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap p1 p2) p.1) p5) pz) sc,ap (ap (ap (ap (ap p.1 cz) p5c) sc) p2c) p1c⟩

theorem steps_slots :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+2*(Challenge.gateSlots K.R.make+Challenge.gateSlots K.R.clear) := by
  have sc := K.R.scl1591_slots
  have z1 := K.R.m7z_slots; have z2 := K.R.m8z_slots; have z3 := K.R.c8z_slots; have z4 := K.R.c7z_slots
  simp only [make,clear,KRegs.smk,KRegs.scl,KRegs.make,KRegs.clear,Challenge.gateSlots_append] at sc ⊢
  omega

end ECDSAAdd.Entrant.FrontierSumCleanup1591KG

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591KG
open Arithmetic KG
variable (K : KG)
theorem steps_slots2 :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+
      (2*(Challenge.gateSlots K.R.smk+Challenge.gateSlots K.R.scl)+Challenge.gateSlots (K.R.m6++K.R.m7++K.R.m8)+
      Challenge.gateSlots (K.R.c8++K.R.c7++K.R.c6)) := by
  have sc := K.R.scl1591_slots
  have z1 := K.R.m7z_slots; have z2 := K.R.m8z_slots; have z3 := K.R.c8z_slots; have z4 := K.R.c7z_slots
  simp only [make,clear,Challenge.gateSlots_append] at sc ⊢; omega
end ECDSAAdd.Entrant.FrontierSumCleanup1591KG

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591LowK =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Core

/-! Same old KG leaf/register layout, with only known-output sum cleanup changed.
No TrimRow or TrimSquare3 program is used. Published b53 count/proof passages are
adapted to the old6693/6811 measurement prices and the unchanged old leaves.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Diagonal
open Arithmetic

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=DiagSq.cost R-R.h-6 ∧ measurementCount (clear R)+3=DiagSq.cost R := by
  have a := clear_counts_diff R w
  have b := DiagSq.clear_counts R w he
  constructor <;> omega

theorem steps_support (R : KRegs) (w : R.W) :
    wires (DiagSq.makeZ R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨DiagSq.makeZ_support R w,clear_support R w⟩

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (DiagSq.makeZ R) ∧ GatePhysical (clear R) :=
  ⟨DiagSq.makeZ_physical R w hn,clear_physical R w hn⟩

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (DiagSq.makeZ R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(DiagSq.makeZ_slots R).trans (DiagSq.tiny_slots R w he hh).1,(clear_slots_le R).trans (DiagSq.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.FrontierSumCleanup1591Diagonal

-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.TrimSquare3
open Arithmetic
theorem tsq3_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨le_refl _,le_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append]
    constructor <;> omega
end ECDSAAdd.Entrant.TrimSquare3

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic
theorem sq_plain3_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsq3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsq3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩
theorem sq_plain3_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsqc3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsqc3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩
end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

/-- Fold-pad tail: untouched by the leaf producer and cleanup, used only for clean-at-rest scratch. -/
def ktmp (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.drop 131

def oregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=64,bank:=L.inputBank.take src.length,dst:=dst,
   S:=((ktmp L).take 66).take (src.length-63),
   T:=(ext.take 132).take (2*(src.length-63)),
   z:=(L.leafCarry.drop 193).take 62,
   pad:=L.leafPad,carry:=L.leafCarry.take 193,cin:=L.core.cin}

def iregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).lo,dst:=(oregs L ext src dst).dlo,
   S:=((ktmp L).drop 66).take 33,T:=(ext.drop 132).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).hi,dst:=(oregs L ext src dst).dhi,
   S:=((ext.drop 198).take 34).take 33,T:=(ext.drop 232).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=33,bank:=(oregs L ext src dst).S,dst:=(oregs L ext src dst).T,
   S:=(ext.drop 198).take 34,T:=(ext.drop 232).take 68,
   z:=(oregs L ext src dst).z.take 31,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

/-- 128-bit leaves: nested split of the low and high halves, cleaned low inner sum. -/
def kgH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=(jregsH L ext src dst).S++(jregsH L ext src dst).T,X5:=[],
   Q1:=FrontierSumCleanup1591Diagonal.makeC (iregs L ext src dst),Q1c:=FrontierSumCleanup1591Diagonal.clearC (iregs L ext src dst),
   Q2:=DiagSq.makeZ (jregsH L ext src dst),Q2c:=FrontierSumCleanup1591Diagonal.clear (jregsH L ext src dst),
   Q5:=TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q5c:=TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=FrontierSumCleanup1591Diagonal.makeC (iregs L ext src dst),Q1c:=FrontierSumCleanup1591Diagonal.clearC (iregs L ext src dst),
   Q2:=TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q2c:=TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   Q5:=DiagSq.makeZ (jregsS L ext src dst),Q5c:=FrontierSumCleanup1591Diagonal.clear (jregsS L ext src dst),
   I1:=(iregs L ext src dst).invC,I2:=fun _ _ => True,I5:=(jregsS L ext src dst).invF}

def kg (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  if src.length=128 then kgH L ext src dst else kgS L ext src dst

theorem ktmp_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (ktmp L).length=123 := by
  simp [ktmp,L.foldPad_length hw]

theorem oregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (oregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem iregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (iregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [iregs,oregs,KRegs.lo,KRegs.dlo,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem jregsH_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : src.length=128) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsH L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsH,oregs,KRegs.hi,KRegs.dhi,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h128] <;> omega

theorem jregsS_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h129 : src.length=129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsS L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsS,oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h129] <;> omega

theorem tmp_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry++ktmp L).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailSplit := congrArg (List.count q) (List.take_append_drop 130 (L.foldPad.drop 1))
  have hdd : (L.foldPad.drop 1).drop 130=L.foldPad.drop 131 := by simp [List.drop_drop]
  rw [hdd] at tailSplit
  simp only [inputBank,leafPad,leafCarry,ktmp,List.count_append] at inputBound workSplit padSplit tailSplit ⊢
  omega

def kbig2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L)++ext

theorem lst_le2 (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (q : Wire) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L).count q ≤
      (control::L.wires).count q := by
  have a := hs q
  have b := hd q
  have banks := tmp_count L src.length q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at a banks ⊢
  omega

theorem kbig2_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (ext : List Wire) (hx : ext.Nodup)
    (hdx : ∀q∈ext,q∉control::L.wires) : (kbig2 L ext control src dst).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have b := List.nodup_iff_count_le_one.mp hx q
  have c := lst_le2 L control src dst hs hd q
  have d := List.nodup_iff_count_le_one.mp hn q
  simp only [kbig2,List.count_append] at c ⊢
  by_cases hq : q∈ext
  · have z : (control::L.wires).count q=0 := List.count_eq_zero.mpr (hdx q hq)
    omega
  · have z : ext.count q=0 := List.count_eq_zero.mpr hq
    omega

theorem ktmp_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈ktmp L) : q∈L.wires := by
  have h' : q∈L.foldPad := List.mem_of_mem_drop h
  simp only [foldPad,List.mem_append] at h'
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,List.mem_cons]
  tauto

theorem ext_split4 (ext : List Wire) (a b c : Nat) (q : Wire) :
    ((ext.take 132).take a).count q+((ext.drop 132).take 66).count q+
      (((ext.drop 198).take 34).take b).count q+((ext.drop 232).take c).count q≤ext.count q := by
  have x1 := kcnt_take (ext.take 132) a q
  have x2 := kcnt_take ((ext.drop 198).take 34) b q
  have x3 := kcnt_take (ext.drop 232) c q
  have e1 := kcnt_split ext 132 q
  have e2 := kcnt_split (ext.drop 132) 66 q
  have e3 := kcnt_split (ext.drop 198) 34 q
  have e4 := kcnt_take (ext.drop 132) 66 q
  simp only [List.drop_drop] at e2 e3
  norm_num at e2 e3
  omega

theorem tmp_split2 (L : CuccaroStreamedSquareWideLayout) (a : Nat) (q : Wire) :
    (((ktmp L).take 66).take a).count q+(((ktmp L).drop 66).take 33).count q≤(ktmp L).count q := by
  have x1 := kcnt_take ((ktmp L).take 66) a q
  have x2 := kcnt_take ((ktmp L).drop 66) 33 q
  have e := kcnt_split (ktmp L) 66 q
  omega

theorem carry_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.leafCarry.take 193).count q+((L.leafCarry.drop 193).take 62).count q≤L.leafCarry.count q := by
  have x := kcnt_take (L.leafCarry.drop 193) 62 q
  have e := kcnt_split L.leafCarry 193 q
  omega

end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs




theorem sub_of_count {l l' : List Wire} (h : ∀q,l.count q≤l'.count q) : l.toFinset⊆l'.toFinset := by
  intro q hq
  have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := h q; omega))

section Inst
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem kgH_nodup : (kgH L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c ⊢
    omega)

include hn hs hd hx hdx in
theorem kgS_nodup : (kgS L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c e ⊢
    omega)

theorem kgH_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgH_jall (q : Wire) :
    (jregsH L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,jregsH,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgS,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_jall (q : Wire) :
    (jregsS L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 31 q
  simp only [KG.all,KG.X,kgS,KRegs.all,jregsS,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega

include hw h128 hsmax hlen he in
theorem kgH_spec (h : src.length=128) (hall : (kgH L ext src dst).all.Nodup) : (kgH L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgH_iall L ext src dst)
  have nj : (jregsH L ext src dst).all.Nodup := knd hall (kgH_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have n5 : ((oregs L ext src dst).cin::(oregs L ext src dst).S++(oregs L ext src dst).T++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,FrontierSumCleanup1591Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    FrontierSumCleanup1591Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    FrontierSumCleanup1591Diagonal.diag_sq_full_make (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    FrontierSumCleanup1591Diagonal.diag_sq_full_clear (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    sq_plain3_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain3_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_local⟩

include hw h128 hsmax hlen he in
theorem kgS_spec (h : src.length=129) (hall : (kgS L ext src dst).all.Nodup) : (kgS L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgS_iall L ext src dst)
  have nj : (jregsS L ext src dst).all.Nodup := knd hall (kgS_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have hdl := w.dst
  have n2 : ((oregs L ext src dst).cin::(oregs L ext src dst).hi++(oregs L ext src dst).dhi++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,FrontierSumCleanup1591Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    FrontierSumCleanup1591Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    sq_plain3_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain3_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    FrontierSumCleanup1591Diagonal.diag_sq_full_make (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    FrontierSumCleanup1591Diagonal.diag_sq_full_clear (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (FrontierSumCleanup1591KG.make (kgH L ext src dst))=6582 ∧ measurementCount (FrontierSumCleanup1591KG.make (kgH L ext src dst))=6686 ∧
    toffoliCount (FrontierSumCleanup1591KG.clear (kgH L ext src dst))=6550 ∧ measurementCount (FrontierSumCleanup1591KG.clear (kgH L ext src dst))=6686 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := FrontierSumCleanup1591KG.make_counts (kgH L ext src dst) w
  have cl := FrontierSumCleanup1591KG.clear_counts (kgH L ext src dst) w
  have i1 := DiagSq.makeZ_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := FrontierSumCleanup1591Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := DiagSq.makeZ_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := FrontierSumCleanup1591Diagonal.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-6 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-3+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=(raw_kcost 64 32-30)-6 ∧ measurementCount (kgH L ext src dst).Q1c=32+((raw_kcost 64 32-30)-3) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.makeZ (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((DiagSq.makeZ (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(FrontierSumCleanup1591Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(FrontierSumCleanup1591Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-6 ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-3 ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-32-6 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-3 :=
    ⟨Nat.eq_sub_of_add_eq j1.1,Nat.eq_sub_of_add_eq j1.2,j2.1,Nat.eq_sub_of_add_eq j2.2⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65-1 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65-1 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65-1 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65-1 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.2,e,f]; rfl
    · show toffoliCount (TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.2,e,f]; rfl
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (FrontierSumCleanup1591KG.make (kgS L ext src dst))=6699 ∧ measurementCount (FrontierSumCleanup1591KG.make (kgS L ext src dst))=6804 ∧
    toffoliCount (FrontierSumCleanup1591KG.clear (kgS L ext src dst))=6666 ∧ measurementCount (FrontierSumCleanup1591KG.clear (kgS L ext src dst))=6804 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := FrontierSumCleanup1591KG.make_counts (kgS L ext src dst) w
  have cl := FrontierSumCleanup1591KG.clear_counts (kgS L ext src dst) w
  have i1 := DiagSq.makeZ_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := FrontierSumCleanup1591Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := DiagSq.makeZ_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := FrontierSumCleanup1591Diagonal.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-6 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-3+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=(raw_kcost 64 32-30)-6 ∧ measurementCount (kgS L ext src dst).Q1c=32+((raw_kcost 64 32-30)-3) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.makeZ (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((DiagSq.makeZ (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(FrontierSumCleanup1591Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(FrontierSumCleanup1591Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65-1 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65-1 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65-1 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65-1 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.2,e,f]; rfl
    · show toffoliCount (TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.2,e,f]; rfl
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-6 ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-3 ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-33-6 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-3 :=
    ⟨Nat.eq_sub_of_add_eq j1.1,Nat.eq_sub_of_add_eq j1.2,j2.1,Nat.eq_sub_of_add_eq j2.2⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Inst3
end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6686 else 6804
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6582 else 6699
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6550 else 6666
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (FrontierSumCleanup1591KG.make (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (FrontierSumCleanup1591KG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (FrontierSumCleanup1591KG.clear (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (FrontierSumCleanup1591KG.clear (kg L ext src dst))=lowkcost2 src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (FrontierSumCleanup1591KG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (FrontierSumCleanup1591KG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := FrontierSumCleanup1591Diagonal.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl1591_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := FrontierSumCleanup1591Diagonal.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact FrontierSumCleanup1591KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1) rK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2.trans rp.2.2.2.2.2.2.2) rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := FrontierSumCleanup1591Diagonal.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact FrontierSumCleanup1591KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.1) rK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2.trans rp.2.2.2.2.2.1) rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (FrontierSumCleanup1591KG.make (kg L ext src dst)) ∧ GatePhysical (FrontierSumCleanup1591KG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := FrontierSumCleanup1591Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := FrontierSumCleanup1591Diagonal.steps_physical (jregsH L ext src dst) wj nj
    exact FrontierSumCleanup1591KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) js.1 js.2 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).1 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).2
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := FrontierSumCleanup1591Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := FrontierSumCleanup1591Diagonal.steps_physical (jregsS L ext src dst) wj nj
    exact FrontierSumCleanup1591KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) (TrimSquare3.tsq3_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).1 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).2 js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (FrontierSumCleanup1591KG.make (kg L ext src dst))+Challenge.gateSlots (FrontierSumCleanup1591KG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := FrontierSumCleanup1591Diagonal.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl1591_slots
  have g2 := TrimSquare3.tsq3_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimSquare3.tsq3_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := FrontierSumCleanup1591Diagonal.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := FrontierSumCleanup1591KG.steps_slots2 (kgH L ext src dst)
    simp only [kgH,FrontierSumCleanup1591Diagonal.makeC,FrontierSumCleanup1591Diagonal.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := FrontierSumCleanup1591Diagonal.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := FrontierSumCleanup1591KG.steps_slots2 (kgS L ext src dst)
    simp only [kgS,FrontierSumCleanup1591Diagonal.makeC,FrontierSumCleanup1591Diagonal.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.clear (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)

private theorem diag3_k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := kg_R L ext src dst
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(oregs L ext src dst).S,q∈ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(kg L ext src dst).X,q∈ext ∨ q∈ktmp L := fun q h =>
    (kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈ktmp L,q∉L.core.out := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈ktmp L,q∉dst := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈ktmp L,q∉src := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈ktmp L,q∉ext := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉ktmp L) :
      q∉(oregs L ext src dst).dst ∧ q∉(oregs L ext src dst).T ∧ q∉(kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.clear (kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)) (FrontierSumCleanup1591KG.clear (kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) body a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (FrontierSumCleanup1591KG.make (kg L ext src dst)) a2 s
  rw [show withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.make (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++body++copyRegister (some control) src (L.inputBank.take src.length)++(FrontierSumCleanup1591KG.clear (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := FrontierSumCleanup1591KG.make_correct (kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have i1 := mk.2.2.2.2.1
  rw [kg_I1] at i1
  rw [hKR] at mk
  generalize run (FrontierSumCleanup1591KG.make (kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(oregs L ext src dst).dst → q∉(oregs L ext src dst).T → q∉(kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈ktmp L
    · by_cases hX : q∈(kg L ext src dst).X
      · have hI : q∈((ktmp L).drop 66).take 33 := (kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc ⊢
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply diag3_k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  -- second copy
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (oregs L ext src dst).lo w0.basis=regValue (oregs L ext src dst).lo u0.basis ∧
      regValue (oregs L ext src dst).hi w0.basis=regValue (oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := FrontierSumCleanup1591KG.clear_correct (kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (oregs L ext src dst).dst w0.basis=regValue (oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  rw [hKR] at cl
  generalize run (FrontierSumCleanup1591KG.clear (kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

theorem kg_cnt (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (q : Wire) : (kg L ext src dst).all.count q≤(kbig2 L ext control src dst).count q := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d ⊢
    omega
  · rw [kg,if_neg c]
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d e ⊢
    omega

theorem withLowK2_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)=
      2*src.length+lowkcostTPair src.length+toffoliCount body ∧
    measurementCount (withLowK2 L ext control src dst body)=
      2*src.length+2*lowkcost2 src.length+measurementCount body := by
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have copy := copyRegister_counts (some control) src (L.inputBank.take src.length) inputLen.symm
  have erase := eraseMask_counts control src (L.inputBank.take src.length) inputLen.symm
  have k := kg_counts L hw ext src dst h128 hsmax hd he
  simp only [withLowK2,toffoliCount_append,measurementCount_append,copy.1,copy.2,erase.1,erase.2,
    k.1,k.2.1,k.2.2.1,k.2.2.2,inputLen,Option.isSome_some,if_true,lowkcostTPair]
  constructor <;> omega

theorem withLowK2_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) (hb : ECDSAAdd.wires body⊆(control::L.wires).toFinset) :
    ECDSAAdd.wires (withLowK2 L ext control src dst body)⊆(control::L.wires++ext).toFinset := by
  have st := kg_support L hw ext src dst h128 hsmax hlen he
  have kin : (kg L ext src dst).all.toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
    have b := kg_cnt L ext control src dst q
    have c := lst_le2 L control src dst hs hd q
    simp only [kbig2,List.count_append] at b c
    apply List.mem_toFinset.mpr
    simp only [List.mem_append]
    by_cases hx : q∈ext
    · exact Or.inr hx
    · have z : ext.count q=0 := List.count_eq_zero.mpr hx
      exact Or.inl (List.count_pos_iff.mp (by omega))
  have cin : ∀q∈control::src++L.inputBank.take src.length,q∈control::L.wires := by
    intro q h
    have a := List.count_pos_iff.mpr h
    have c := lst_le L control src dst hs hd q
    simp only [List.count_cons,List.count_append] at a c
    exact List.count_pos_iff.mp (by simp only [List.count_cons] at *; omega)
  have cp : ECDSAAdd.wires (copyRegister (some control) src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := copyRegister_wires_subset (some control) src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset,Option.toList_some,List.singleton_append] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have er : ECDSAAdd.wires (eraseMask control src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := eraseMask_wires_subset control src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have bd : ECDSAAdd.wires body⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (hb hq)
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl h
  simp only [withLowK2,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1.trans kin⟩,er⟩,bd⟩,cp⟩,st.2.trans kin⟩,er⟩

theorem withLowK2_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hb : GatePhysical body) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have st := kg_physical L hw ext src dst h128 hsmax hlen he hall
  have ndCopy : (src++L.inputBank.take src.length).Nodup :=
    knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉L.inputBank.take src.length := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e
    exact kdis hbig (r:=[c]) (fun q => by
      simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) c (by simp)
  have cp := copyRegister_physical (some control) src (L.inputBank.take src.length) ndCopy hcB
  have er := eraseMask_physical control src (L.inputBank.take src.length)
  simp only [withLowK2,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1⟩,er⟩,hb⟩,cp⟩,st.2⟩,er⟩

theorem withLowK2_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤1620000+Challenge.gateSlots body := by
  have sizes := L.measured_bank_widths hw
  have st := kg_slots L hw ext src dst h128 hsmax hlen he
  have hcopy := Nat.min_le_right src.length (L.inputBank.take src.length).length
  have hl : (L.inputBank.take src.length).length ≤ 129 := by simp [sizes.1]
  simp only [withLowK2,Challenge.gateSlots_append,Baselines.copyRegister_gateSlots,Baselines.eraseMask_gateSlots]
  omega

end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK

end




namespace ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
open Arithmetic
attribute [local irreducible] Challenge.gateSlots

private theorem kgH_slots_le (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    Challenge.gateSlots (FrontierSumCleanup1591KG.make (kgH L ext src dst))+
      Challenge.gateSlots (FrontierSumCleanup1591KG.clear (kgH L ext src dst))≤
    Challenge.gateSlots (OwnDiagLowK.kgH L ext src dst).make+
      Challenge.gateSlots (OwnDiagLowK.kgH L ext src dst).clear := by
  have im := FrontierSumCleanup1591Diagonal.makeC_slots_le (iregs L ext src dst)
  have ic := FrontierSumCleanup1591Diagonal.clearC_slots_le (iregs L ext src dst)
  have jc := FrontierSumCleanup1591Diagonal.clear_slots_le (jregsH L ext src dst)
  have jm := DiagSq.makeZ_slots (jregsH L ext src dst)
  have outer := (oregs L ext src dst).scl1591_slots
  have z1 := (oregs L ext src dst).m7z_slots
  have z2 := (oregs L ext src dst).m8z_slots
  have z3 := (oregs L ext src dst).c8z_slots
  have z4 := (oregs L ext src dst).c7z_slots
  have q5 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  simp only [oregs,iregs,jregsH,ktmp] at im ic jc jm outer z1 z2 z3 z4 q5
  simp only [FrontierSumCleanup1591KG.make,FrontierSumCleanup1591KG.clear,
    KG.make,KG.clear,kgH,OwnDiagLowK.kgH,oregs,iregs,jregsH,
    OwnDiagLowK.oregs,OwnDiagLowK.iregs,OwnDiagLowK.jregsH,
    ktmp,OwnDiagLowK.ktmp,KRegs.m5,KRegs.c5,Challenge.gateSlots_append]
  omega

private theorem kgS_slots_le (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    Challenge.gateSlots (FrontierSumCleanup1591KG.make (kgS L ext src dst))+
      Challenge.gateSlots (FrontierSumCleanup1591KG.clear (kgS L ext src dst))≤
    Challenge.gateSlots (OwnDiagLowK.kgS L ext src dst).make+
      Challenge.gateSlots (OwnDiagLowK.kgS L ext src dst).clear := by
  have im := FrontierSumCleanup1591Diagonal.makeC_slots_le (iregs L ext src dst)
  have ic := FrontierSumCleanup1591Diagonal.clearC_slots_le (iregs L ext src dst)
  have jc := FrontierSumCleanup1591Diagonal.clear_slots_le (jregsS L ext src dst)
  have jm := DiagSq.makeZ_slots (jregsS L ext src dst)
  have outer := (oregs L ext src dst).scl1591_slots
  have z1 := (oregs L ext src dst).m7z_slots
  have z2 := (oregs L ext src dst).m8z_slots
  have z3 := (oregs L ext src dst).c8z_slots
  have z4 := (oregs L ext src dst).c7z_slots
  have q5 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  simp only [oregs,iregs,jregsS,ktmp] at im ic jc jm outer z1 z2 z3 z4 q5
  simp only [FrontierSumCleanup1591KG.make,FrontierSumCleanup1591KG.clear,
    KG.make,KG.clear,kgS,OwnDiagLowK.kgS,oregs,iregs,jregsS,
    OwnDiagLowK.oregs,OwnDiagLowK.iregs,OwnDiagLowK.jregsS,
    ktmp,OwnDiagLowK.ktmp,KRegs.m2,KRegs.c2,Challenge.gateSlots_append]
  omega

theorem withLowK2_slots_le (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (control : Wire) (body : Program) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (OwnDiagLowK.withLowK2 L ext control src dst body) := by
  have pair : Challenge.gateSlots (FrontierSumCleanup1591KG.make (kg L ext src dst))+
      Challenge.gateSlots (FrontierSumCleanup1591KG.clear (kg L ext src dst))≤
      Challenge.gateSlots (OwnDiagLowK.kg L ext src dst).make+
      Challenge.gateSlots (OwnDiagLowK.kg L ext src dst).clear := by
    by_cases h : src.length=128
    · simpa only [kg,OwnDiagLowK.kg,if_pos h] using kgH_slots_le L ext src dst
    · simpa only [kg,OwnDiagLowK.kg,if_neg h] using kgS_slots_le L ext src dst
  simp only [withLowK2,OwnDiagLowK.withLowK2,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.FrontierSumCleanup1591LowK
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591LowK
-- consolidated import: import ECDSAAdd.Submission.Entrant.PrefixFrontierSquare1591

/-!675T sum-cleanup square on our old leaves and old register allocation.
Published b53aedf5 supplies only the known-output sum eraser and generic KG
cleanup proofs. The arithmetic fold, placement and hosting proof bodies are
reused from our fixed accepted682/783 square. No TrimRow change is included.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Raw
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout OwnDiagAll12Square
abbrev cFlipK := OwnDiagAll12Square.cFlipK
abbrev kext := OwnDiagAll12Square.kext
abbrev kext_index := OwnDiagAll12Square.kext_index

theorem withMixedK_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) (hst : ∀i∈items,MixStatic L i) :
    (run (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (mixFoldsQ L orientation items) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (mixFoldsQ_support L hw nd control orientation items hst hw'))
  apply FrontierSumCleanup1591LowK.withLowK2_correct L hw control hn src dst hs hd hs2 hsmax hlen ext he.nodup he.away he.len
    (mixFoldsQ L orientation items) hbody s records hc hzero hz V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := mixFoldsQ_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩


def accBranchAK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591LowK.withLowK2 L ext control L.core.low (L.core.product.take 256) (mixFoldsQ L true (accAMixQ L))
def accBranchBK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591LowK.withLowK2 L ext control L.core.high (L.core.product.take 256) (mixFoldsQ L false (accBMixQ L))
def accMiddleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591LowK.withLowK2 L ext control L.core.sum L.core.product (bodyC L control)
def accBranchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  gPrep L++accMiddleCK L ext control++gClear L
def accPrefixK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  accBranchCK L ext control++accBranchBK L ext control++accBranchAK L ext control

theorem accBranchAK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchAK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchAK L ext control) records s).basis=
      resAQ ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchAK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) true (accAMixQ L) s records hc dstZero
    O (M^2) (resAQ (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accA_views L hw t M mb hp i (accAMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accAMixQ_sum L t).trans ((accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).1
  exact result

theorem accBranchBK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchBK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchBK L ext control) records s).basis=
      resBQ ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchBK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) false (accBMixQ L) s records hc dstZero
    O (M^2) (resBQ (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accB_views L hw t M mb hp i (accBMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accBMixQ_sum L t).trans ((accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).2.1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).2
  exact result

theorem accMiddleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accMiddleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bodyC L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bodyC_support L hw nd control hw'))
  apply FrontierSumCleanup1591LowK.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (bodyC L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := accMiddleCF_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem accBranchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := accMiddleCK L ext control
  let mp := measurementCount (gPrep L)
  let rest := records.drop mp
  let u := run (gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (gClear L) (rest.drop (measurementCount middle)) v
  have prep := gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (sum_in L control q bad)))).trans hz
  have used := accMiddleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [accBranchCK,middle,u,v,out,rest,mp,run_append] using final

theorem cbaF_complete_exact (enabled : Bool) (A B O : Nat) :
    resAQ ((if enabled then A else 0)^2)
      (resBQ ((if enabled then B else 0)^2) (resCF enabled ((if enabled then A+B else 0)^2) O))=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OB+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p<
      SquareReduction.p := Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have cast : (OA : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p : Nat) :
        ZMod SquareReduction.p) := by
    rw [ZMod.natCast_mod,Nat.cast_add,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt oaBound,ZMod.val_natCast_of_lt targetBound] using value

theorem accPrefixK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accPrefixK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefixK L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then cFlipK else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefixK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  let restC := records.drop (measurementCount (accBranchCK L ext control))
  let restB := restC.drop (measurementCount (accBranchBK L ext control))
  let u := run (accBranchCK L ext control) (records.take (measurementCount (accBranchCK L ext control))) s
  let v := run (accBranchBK L ext control) (restC.take (measurementCount (accBranchBK L ext control))) u
  let w := run (accBranchAK L ext control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ec := accBranchCK_correct L hw ext control hn A B O hO s
    (records.take (measurementCount (accBranchCK L ext control))) rfl sumB sumBound ho hp0 hc he hz
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OC ⟨ec.2.1,ec.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ec.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B := regValue_congr _ _ _ (fun q hq => ec.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ec.2.2 control ctrlAway
  have eb := accBranchBK_correct L hw ext control hn B OC (ofCast_lt _ _) u
    (restC.take (measurementCount (accBranchBK L ext control))) highU ec.2.1 productU cleanU he
    ((regValue_congr _ _ _ (fun q hq => ec.2.2 q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ec.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A :=
    regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ea := accBranchAK_correct L hw ext control hn A OB (ofCast_lt _ _) v restB lowV eb.2.1 productV cleanV he
    ((regValue_congr _ _ _ (fun q hq => sameV q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlV] at ea
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ea.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p := by
    have exactResult := cbaF_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    rw [ea.2.1]
    exact exactResult
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ea.1.trans (eb.1.trans ec.1),fullValue,sameW⟩
  simpa [accPrefixK,u,v,w,restB,restC,enabled,run_append,Nat.add_assoc] using final


theorem accPrefixK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (accPrefixK L ext control)=2*FrontierSumCleanup1591LowK.lowkcostTPair 128+FrontierSumCleanup1591LowK.lowkcostTPair 129+13554 ∧ measurementCount (accPrefixK L ext control)=4*FrontierSumCleanup1591LowK.lowkcost2 128+2*FrontierSumCleanup1591LowK.lowkcost2 129+13566 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := mixFoldsQ_counts L hw true (accAMixQ L) stQ.1
  have fb := mixFoldsQ_counts L hw false (accBMixQ L) stQ.2
  have fc := bodyC_counts L hw control
  have prices := accQ_item_prices L hw
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  have sum := gSum_counts L hw
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2]
  constructor <;> omega

theorem accPrefixK_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (accPrefixK L ext control)⊆(control::L.wires++ext).toFinset := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have a := mixFoldsQ_support L hw hn control true (accAMixQ L) stQ.1
  have b := mixFoldsQ_support L hw hn control false (accBMixQ L) stQ.2
  have c := bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) hl hp (by omega) (by omega) (by omega) he a
  have sb := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) hb hp (by omega) (by omega) (by omega) he b
  have sc := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.sum L.core.product
    (bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (gSum_support L hw control).1.trans embed
  have unprep := (gSum_support L hw control).2.trans embed
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩

theorem accPrefixK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : ExtOK L control ext) :
    GatePhysical (accPrefixK L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd true (accAMixQ L) stQ.1)
  have b := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd false (accBMixQ L) stQ.2)
  have c := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _
    (bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (gSum_physical L hw nd).1
  have clear := (gSum_physical L hw nd).2
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩

theorem accPrefixK_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (accPrefixK L ext control) ≤ 8000000 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have bd (items : List MixItem) (h : items=accAMixQ L ∨ items=accBMixQ L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMixQ,accBMixQ,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,earlyHTerms,Acc.earlyTerm,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFoldsQ_gateSlots L hw true (accAMixQ L) stQ.1 20 (bd _ (Or.inl rfl))
  have hb := mixFoldsQ_gateSlots L hw false (accBMixQ L) stQ.2 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := bodyC_gateSlots L hw control
  have la : (accAMixQ L).length = 3 := rfl
  have lb : (accBMixQ L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := gSum_gateSlots L hw
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,Challenge.gateSlots_append]
  omega


end ECDSAAdd.Entrant.FrontierSumCleanup1591Raw

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Raw
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare OwnDiagAll12Square

def fastCandidate (L : ControlledPointLayout) : Program :=
  accPrefixK L.dialogStreamedSquareWide (kext L) L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=2*FrontierSumCleanup1591LowK.lowkcostTPair 128+FrontierSumCleanup1591LowK.lowkcostTPair 129+13554 ∧ measurementCount (fastCandidate L)=4*FrontierSumCleanup1591LowK.lowkcost2 128+2*FrontierSumCleanup1591LowK.lowkcost2 129+13566 :=
  accPrefixK_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
    L.core.generic (by simp [kext,OwnDiagAll12Square.kext,wireBlock_length])

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
  have support := accPrefixK_support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) (kext L)
    L.core.generic (by simp [kext,OwnDiagAll12Square.kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := accPrefixK_correct K hwK (kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply accPrefixK_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
  · have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢; omega
  · exact kext_ok L hw hn

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem diag4_pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem diag4_pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (diag4_pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply diag4_pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end StateEq

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 8000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using accPrefixK_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
      L.core.generic (by simp [kext,OwnDiagAll12Square.kext,wireBlock_length])


end ECDSAAdd.Entrant.FrontierSumCleanup1591Raw

-- DIAGONAL COMPONENT SquareTriple.lean

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Raw
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog OwnDiagAll12Square
private theorem diag5_sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section SquareStep
attribute [local irreducible] run fastSquare fastCandidate
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

theorem fast_step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (fastSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (cFlipK : Fp) else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  have hK : ((cFlipK : Nat) : Fp).val=cFlipK := ZMod.val_natCast_of_lt (by norm_num [cFlipK,OwnDiagAll12Square.cFlipK,p])
  rw [ZMod.val_add,diag5_sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul,hK] using hx

end SquareStep
end ECDSAAdd.Entrant.FrontierSumCleanup1591Raw



-- DIAGONAL COMPONENT Placement.lean

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def SquareCorrect (L : ControlledPointLayout) (P : Program) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState),
    Triple (PointDialogValues L X Y G origin) P
      (PointDialogValues L (X-(if G then Y*Y else 0)+
        (if G then (FrontierSumCleanup1591Raw.cFlipK : Fp) else 0)) Y G origin)

theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool)
    (hf : ∀q,q∉L.dialogPool → e q=q) (P : Program) (correct : SquareCorrect L P) :
    SquareCorrect L (renameProgram e P) := by
  intro X Y G origin s m v
  have old:=correct X Y G origin s m v
  have eq:=Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean old.2.clean
  simpa only [eq] using old

def initial (L : ControlledPointLayout) : Program :=
  renameProgram (Square5Placement.blockPerm L 202) (FrontierSumCleanup1591Raw.fastCandidate L)
def plus (L : ControlledPointLayout) : Program := renameProgram (OwnPlusSquare.swap L) (initial L)
def guard (L : ControlledPointLayout) : Program := renameProgram (OwnGuardSquare.swap L) (plus L)
def minus (L : ControlledPointLayout) : Program := renameProgram (OwnQ4Square.swap L) (guard L)
def program (L : ControlledPointLayout) : Program := renameProgram (OwnQ5Square.swap L) (minus L)

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (FrontierSumCleanup1591Raw.fastCandidate L) := by
  intro X Y G origin s m v
  have old:=FrontierSumCleanup1591Raw.fast_step_square L hw hn X Y G origin s m v
  rw [FrontierSumCleanup1591Raw.fastSquare_state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean] at old
  exact old

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (program L) := by
  have a:=relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have b:=relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw)
    (OwnPlusSquare.outside L hw) _ a
  have c:=relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw)
    (OwnGuardSquare.outside L hw) _ b
  have d:=relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw)
    (OwnQ4Square.outside L hw) _ c
  exact relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw)
    (OwnQ5Square.outside L hw) _ d

end ECDSAAdd.Entrant.FrontierSumCleanup1591Placed


-- DIAGONAL COMPONENT Resources.lean

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=2*FrontierSumCleanup1591LowK.lowkcostTPair 128+FrontierSumCleanup1591LowK.lowkcostTPair 129+13554 ∧
    measurementCount (program L)=4*FrontierSumCleanup1591LowK.lowkcost2 128+2*FrontierSumCleanup1591LowK.lowkcost2 129+13566 := by
  have a:=renameProgram_counts (Square5Placement.blockPerm L 202) (FrontierSumCleanup1591Raw.fastCandidate L)
  have b:=renameProgram_counts (OwnPlusSquare.swap L) (initial L)
  have c:=renameProgram_counts (OwnGuardSquare.swap L) (plus L)
  have d:=renameProgram_counts (OwnQ4Square.swap L) (guard L)
  have e:=renameProgram_counts (OwnQ5Square.swap L) (minus L)
  have base:=FrontierSumCleanup1591Raw.fastCandidate_counts L hw
  exact ⟨e.1.trans (d.1.trans (c.1.trans (b.1.trans (a.1.trans base.1)))),
    e.2.trans (d.2.trans (c.2.trans (b.2.trans (a.2.trans base.2))))⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202)
    (Square5Placement.blockPerm L 202).injective _ (FrontierSumCleanup1591Raw.fastCandidate_physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 := by
  simpa only [program,minus,guard,plus,initial,Baselines.rename_gateSlots,
    FrontierSumCleanup1591Raw.fastCandidate] using
      FrontierSumCleanup1591Raw.accPrefixK_gateSlots_le L.dialogStreamedSquareWide
        (L.dialogStreamedSquareWide_widths hw) (FrontierSumCleanup1591Raw.kext L)
        L.core.generic (by simp [FrontierSumCleanup1591Raw.kext,OwnDiagAll12Square.kext,wireBlock_length])

end ECDSAAdd.Entrant.FrontierSumCleanup1591Placed


-- DIAGONAL COMPONENT Support.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag8_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem swap_support (P : Program) (a b : Wire) (S : Finset Wire)
    (old : wires P⊆S) (ha : a∈S) (hb : b∈S) :
    wires (renameProgram (Equiv.swap a b) P)⊆S := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=a
  · subst w; simpa only [Equiv.swap_apply_left] using hb
  · by_cases y:w=b
    · subst w; simpa only [Equiv.swap_apply_right] using ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne x y] using old used

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L) ⊆ (OB5Support.sites L).toFinset := by
  have oldGuard : wires (guard L)⊆(OB5Support.sites L).toFinset := by
    have previous : wires (plus L)⊆(OB5Support.sites L).toFinset := by
      have old : wires (initial L)⊆(OB5Support.sites L).toFinset := by
        rw [initial,renameProgram_support]
        intro q hq
        obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
        have support := FrontierSumCleanup1591Raw.fastCandidate_support L hw hn used
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at support
        apply List.mem_toFinset.mpr
        rcases support with h | h | h | h | h
        · subst old
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _
            (diag8_resident_away L hn _ (by simp [CompressedPointSquare.residents, inPlaceFlags]))]
          simp [OB5Support.sites]
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inr h)
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inl (Or.inr h))
        · rw [pool_block L hw 776 (by omega)] at h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
        · obtain ⟨i, h1, h2, h3, rfl⟩ := FrontierSumCleanup1591Raw.kext_index L _ h
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
      exact swap_support (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) _ old
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 766 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1530 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    exact swap_support (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) _ previous
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 765 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1531 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
  have oldQ4 := swap_support (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) _ oldGuard
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 767 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1532 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

  exact swap_support (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) _ oldQ4
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 770 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1536 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

end ECDSAAdd.Entrant.FrontierSumCleanup1591Placed


-- DIAGONAL COMPONENT Omissions.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag9_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (n : Nat) (allowed : n∈[1530,1531,1532,1536,1537]) :
    L.core.poolWire n∉wires (initial L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=FrontierSumCleanup1591Raw.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag9_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=FrontierSumCleanup1591Raw.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem swap_target_free (P : Program) (a b : Wire) (free : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back : (Equiv.swap a b) b=a := Equiv.swap_apply_right _ _
  have same : old=b := (Equiv.swap a b).injective (e.trans back.symm)
  exact free (same ▸ used)

private theorem diag9_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)


theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1530 (by simp)
  have p1 : L.core.poolWire 766∉wires (plus L) :=
    swap_target_free (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) p0
  have p2 : L.core.poolWire 766∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 766∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 766∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1531 (by simp)
  have p1 : L.core.poolWire 1531∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1531 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 765∉wires (guard L) :=
    swap_target_free (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) p1
  have p3 : L.core.poolWire 765∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 765∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1532 (by simp)
  have p1 : L.core.poolWire 1532∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1532∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 767∉wires (minus L) :=
    swap_target_free (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) p2
  have p4 : L.core.poolWire 767∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 767 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1536 (by simp)
  have p1 : L.core.poolWire 1536∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1536∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1536∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 770∉wires (program L) :=
    swap_target_free (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) p3
  exact p4

theorem free1537 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1537 (by simp)
  have p1 : L.core.poolWire 1537∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1537∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1537∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1537∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

end ECDSAAdd.Entrant.FrontierSumCleanup1591Placed


-- DIAGONAL COMPONENT PlacementQ6.lean
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)
def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (FrontierSumCleanup1591Placed.program L)

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1285
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1537 (by omega)
  · by_cases b:q=L.core.poolWire 1537
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1285 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1285:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1285 (by omega))
  have b:q≠L.core.poolWire 1537:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b


theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    FrontierSumCleanup1591Placed.SquareCorrect L (program L) :=
  FrontierSumCleanup1591Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (FrontierSumCleanup1591Placed.correct L hw hn)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285∉wires (program L) :=
  FrontierSumCleanup1591Placed.swap_target_free _ _ _ (FrontierSumCleanup1591Placed.free1537 L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=2*FrontierSumCleanup1591LowK.lowkcostTPair 128+FrontierSumCleanup1591LowK.lowkcostTPair 129+13554 ∧
    measurementCount (program L)=4*FrontierSumCleanup1591LowK.lowkcost2 128+2*FrontierSumCleanup1591LowK.lowkcost2 129+13566 := by
  have e:=renameProgram_counts (swap L) (FrontierSumCleanup1591Placed.program L)
  have c:=FrontierSumCleanup1591Placed.counts L hw
  exact ⟨e.1.trans c.1,e.2.trans c.2⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) :=
  gatePhysical_rename (swap L) (swap L).injective _ (FrontierSumCleanup1591Placed.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (Baselines.rename_gateSlots _ _).le.trans (FrontierSumCleanup1591Placed.slots L hw)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  FrontierSumCleanup1591Placed.swap_support _ _ _ _ (FrontierSumCleanup1591Placed.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1285
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1537
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

private theorem diag10_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (n : Nat) (hnn : n<2613) (a : n≠1285) (b : n≠1537) : swap L (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact a (pool_inj L hw hn n 1285 hnn (by omega) eq)
  · intro eq;exact b (pool_inj L hw hn n 1537 hnn (by omega) eq)

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 765 (by omega) (by omega) (by omega))
    (FrontierSumCleanup1591Placed.free765 L hw hn)

theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 766 (by omega) (by omega) (by omega))
    (FrontierSumCleanup1591Placed.free766 L hw hn)

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 767 (by omega) (by omega) (by omega))
    (FrontierSumCleanup1591Placed.free767 L hw hn)

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 770 (by omega) (by omega) (by omega))
    (FrontierSumCleanup1591Placed.free770 L hw hn)

end ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ6


-- DIAGONAL COMPONENT TailOmissions.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag11_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial1800_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (initial L) := by
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=FrontierSumCleanup1591Raw.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag11_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=FrontierSumCleanup1591Raw.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem diag11_fix1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b : Nat) (ha : a<2613) (hb : b<2613) (hna : 1800≠a) (hnb : 1800≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire 1800)=L.core.poolWire 1800 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn 1800 a (by omega) ha eq)
  · intro eq;exact hnb (pool_inj L hw hn 1800 b (by omega) hb eq)

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have p0:=initial1800_free L hw hn
  have p1 : L.core.poolWire 1800∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 766 1530 (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1800∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 765 1531 (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1800∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 767 1532 (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1800∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 770 1536 (by omega) (by omega) (by omega) (by omega)) p3
  exact p4
end ECDSAAdd.Entrant.FrontierSumCleanup1591Placed
namespace ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have same: swap L (L.core.poolWire 1800)=L.core.poolWire 1800 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e
      have :=pool_inj L hw hn 1800 1285 (by omega) (by omega) e
      omega
    · intro e
      have :=pool_inj L hw hn 1800 1537 (by omega) (by omega) e
      omega
  exact OwnPlusHost.rename_avoid _ _ _ same (FrontierSumCleanup1591Placed.free1800 L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (program L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact free1800 L hw hn
  · exact free766 L hw hn
  · exact free765 L hw hn
  · exact free767 L hw hn
  · exact free770 L hw hn
  · exact retired_free L hw hn
end ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ6


-- DIAGONAL COMPONENT CountsDiag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ7
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires
private theorem q7part34_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1538∉wires (FrontierSumCleanup1591Placed.initial L) := by
  rw [FrontierSumCleanup1591Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=FrontierSumCleanup1591Raw.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=q7part34_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · have away:=q7part34_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · have away:=q7part34_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1538 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=FrontierSumCleanup1591Raw.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1538 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem q7part34_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1538∉wires (FrontierSumCleanup1591PlacedQ6.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 1538∉wires (FrontierSumCleanup1591Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 766 1530 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1538∉wires (FrontierSumCleanup1591Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 765 1531 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1538∉wires (FrontierSumCleanup1591Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 767 1532 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1538∉wires (FrontierSumCleanup1591Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 770 1536 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 1538∉wires (FrontierSumCleanup1591PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 1285 1537 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  exact p5
def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)
def program (L : ControlledPointLayout) : Program := renameProgram (swap L) (FrontierSumCleanup1591PlacedQ6.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1286
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1538 (by omega)
  · by_cases b:q=L.core.poolWire 1538
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1286 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1286:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1286 (by omega))
  have b:q≠L.core.poolWire 1538:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : ∀q∈L.dialogPool,s.basis q=false)
    (hout : ∀q∈L.dialogPool,(run P m s).basis q=false) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw) P s m ((regValue_zero _ _).mpr hin) ((regValue_zero _ _).mpr hout)

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    FrontierSumCleanup1591Placed.SquareCorrect L (program L) := by
  unfold program
  exact FrontierSumCleanup1591Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (FrontierSumCleanup1591PlacedQ6.correct L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=toffoliCount (FrontierSumCleanup1591PlacedQ6.program L) ∧
    measurementCount (program L)=measurementCount (FrontierSumCleanup1591PlacedQ6.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _ (FrontierSumCleanup1591PlacedQ6.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 := by
  unfold program
  exact (Baselines.rename_gateSlots _ _).le.trans (FrontierSumCleanup1591PlacedQ6.slots L hw)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1286∉wires (program L) := by
  unfold program swap
  exact FrontierSumCleanup1591Placed.swap_target_free _ _ _ (spare_free L hw hn)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  unfold program swap
  exact FrontierSumCleanup1591Placed.swap_support _ _ _ _ (FrontierSumCleanup1591PlacedQ6.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1286
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1538
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h:k=1286
  · subst k; exact retired_free L hw hn
  have hkold : k∈[1800,766,765,767,770,1285] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    omega
  have f : swap L (L.core.poolWire k)=L.core.poolWire k :=
    q7part34_fix L hw hn 1286 1538 k (by omega) (by omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega) h
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega)
  unfold program
  exact OwnPlusHost.rename_avoid _ _ _ f (FrontierSumCleanup1591PlacedQ6.square_free L hw hn k hkold)
end ECDSAAdd.Entrant.FrontierSumCleanup1591PlacedQ7

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Square
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (FrontierSumCleanup1591Placed.initial L) := by
  rw [FrontierSumCleanup1591Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=FrontierSumCleanup1591Raw.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic
      (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=FrontierSumCleanup1591Raw.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1539
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b n : Nat)
    (ha : a<2613) (hb : b<2613) (hnn : n<2613) (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b))
      (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1539∉wires (FrontierSumCleanup1591PlacedQ7.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 1539∉wires (FrontierSumCleanup1591Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 766 1530 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1539∉wires (FrontierSumCleanup1591Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 765 1531 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1539∉wires (FrontierSumCleanup1591Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 767 1532 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1539∉wires (FrontierSumCleanup1591Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 770 1536 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 1539∉wires (FrontierSumCleanup1591PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1285 1537 1539
      (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  exact OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1286 1538 1539
    (by omega) (by omega) (by omega) (by omega) (by omega)) p5

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)

def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (FrontierSumCleanup1591PlacedQ7.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 769
  · subst q
    simpa only [swap,Equiv.swap_apply_left] using
      Square5Placement.pool_member L hw 1539 (by omega)
  · by_cases b:q=L.core.poolWire 1539
    · subst q
      simpa only [swap,Equiv.swap_apply_right] using
        Square5Placement.pool_member L hw 769 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 769:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 769 (by omega))
  have b:q≠L.core.poolWire 1539:=fun e=>
    hq (e.symm ▸ Square5Placement.pool_member L hw 1539 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : regValue L.dialogPool s.basis=0)
    (hout : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw)
    P s m hin hout

theorem program_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (FrontierSumCleanup1591PlacedQ7.program L) m s := by
  have old:=FrontierSumCleanup1591PlacedQ7.correct L hw hn X Y G origin s m v
  unfold program
  exact run_eq L hw _ s m v.clean old.2.clean

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    FrontierSumCleanup1591Placed.SquareCorrect L (program L) := by
  unfold program
  exact FrontierSumCleanup1591Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (FrontierSumCleanup1591PlacedQ7.correct L hw hn)

theorem counts (L : ControlledPointLayout) :
    toffoliCount (program L)=toffoliCount (FrontierSumCleanup1591PlacedQ7.program L) ∧
    measurementCount (program L)=measurementCount (FrontierSumCleanup1591PlacedQ7.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem slots_eq (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)=
      Challenge.gateSlots (FrontierSumCleanup1591PlacedQ7.program L) := by
  unfold program
  exact Baselines.rename_gateSlots _ _

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (slots_eq L).le.trans (FrontierSumCleanup1591PlacedQ7.slots L hw)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _
    (FrontierSumCleanup1591PlacedQ7.physical L hw hn)

theorem support_eq (L : ControlledPointLayout) :
    wires (program L)=(wires (FrontierSumCleanup1591PlacedQ7.program L)).image (swap L) := by
  unfold program
  exact renameProgram_support _ _

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  unfold program swap
  exact FrontierSumCleanup1591Placed.swap_support _ _ _ _ (FrontierSumCleanup1591PlacedQ7.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 769
      (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1539
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 769∉wires (program L) := by
  unfold program swap
  exact FrontierSumCleanup1591Placed.swap_target_free _ _ _ (spare_free L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h:k=769
  · subst k;exact retired_free L hw hn
  have hkold : k∈[1800,766,765,767,770,1285,1286] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    omega
  have f : swap L (L.core.poolWire k)=L.core.poolWire k :=
    pool_swap_fix L hw hn 769 1539 k (by omega) (by omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega) h
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega)
  unfold program
  exact OwnPlusHost.rename_avoid _ _ _ f (FrontierSumCleanup1591PlacedQ7.square_free L hw hn k hkold)

end ECDSAAdd.Entrant.FrontierSumCleanup1591Square


namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Raw
open Arithmetic ControlledPointLayout OwnDiagAll12Square
attribute [local irreducible] Challenge.gateSlots

theorem accPrefixK_slots_le (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    Challenge.gateSlots (accPrefixK L ext control)≤Challenge.gateSlots (OwnDiagAll12Square.accPrefixK L ext control) := by
  have a := FrontierSumCleanup1591LowK.withLowK2_slots_le L ext L.core.low (L.core.product.take 256)
    control (mixFoldsQ L true (accAMixQ L))
  have b := FrontierSumCleanup1591LowK.withLowK2_slots_le L ext L.core.high (L.core.product.take 256)
    control (mixFoldsQ L false (accBMixQ L))
  have c := FrontierSumCleanup1591LowK.withLowK2_slots_le L ext L.core.sum L.core.product control (bodyC L control)
  have oldPrep : OwnDiagAll12Square.gPrep L=ECDSAAdd.Entrant.gPrep L := rfl
  have oldClear : OwnDiagAll12Square.gClear L=ECDSAAdd.Entrant.gClear L := rfl
  have oldMixA : OwnDiagAll12Square.accAMixQ L=ECDSAAdd.Entrant.accAMixQ L := rfl
  have oldMixB : OwnDiagAll12Square.accBMixQ L=ECDSAAdd.Entrant.accBMixQ L := rfl
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,
    OwnDiagAll12Square.accPrefixK,OwnDiagAll12Square.accBranchAK,OwnDiagAll12Square.accBranchBK,
    OwnDiagAll12Square.accBranchCK,OwnDiagAll12Square.accMiddleCK,
    oldPrep,oldClear,oldMixA,oldMixB,Challenge.gateSlots_append]
  omega

theorem fastCandidate_slots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (fastCandidate L)≤Challenge.gateSlots (OwnDiagAll12Square.fastCandidate L) := by
  simpa only [fastCandidate,OwnDiagAll12Square.fastCandidate,kext] using
    accPrefixK_slots_le L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

end ECDSAAdd.Entrant.FrontierSumCleanup1591Raw

namespace ECDSAAdd.Entrant.FrontierSumCleanup1591Square
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] Challenge.gateSlots toffoliCount measurementCount

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1:Nat) else 0)) Y G origin) := by
  have h := correct L hw hn X Y G origin
  cases G <;> simpa only [FrontierSumCleanup1591Raw.cFlipK,OwnDiagAll12Square.cFlipK,
    Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+765=toffoliCount (PrefixFrontierSquare1591.program L) ∧
    measurementCount (program L)+42=measurementCount (PrefixFrontierSquare1591.program L) := by
  have a := counts L
  have b := FrontierSumCleanup1591PlacedQ7.counts L hw
  have c := FrontierSumCleanup1591PlacedQ6.counts L hw
  have d := PrefixFrontierSquare1591.counts L
  have e := OwnDiagAll12PlacedQ7.counts L hw
  have f := OwnDiagAll12PlacedQ6.counts L hw
  norm_num [FrontierSumCleanup1591LowK.lowkcostTPair,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2,
    OwnDiagLowK.lowkcost2] at c f
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (PrefixFrontierSquare1591.program L) := by
  have h := FrontierSumCleanup1591Raw.fastCandidate_slots_le L
  simpa only [program,FrontierSumCleanup1591PlacedQ7.program,FrontierSumCleanup1591PlacedQ6.program,
    FrontierSumCleanup1591Placed.program,FrontierSumCleanup1591Placed.minus,FrontierSumCleanup1591Placed.guard,
    FrontierSumCleanup1591Placed.plus,FrontierSumCleanup1591Placed.initial,
    PrefixFrontierSquare1591.program,OwnDiagAll12PlacedQ7.program,OwnDiagAll12PlacedQ6.program,
    OwnDiagAll12Placed.program,OwnDiagAll12Placed.minus,OwnDiagAll12Placed.guard,
    OwnDiagAll12Placed.plus,OwnDiagAll12Placed.initial,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.FrontierSumCleanup1591Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589SumCleanupSquare =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Square
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589Square

/-!675T cleanup with the two existing square-only Q1589 relabels.-/
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ControlLoan1589SumCleanupSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  MappedCompressed OwnDiagAll12Square
attribute [local irreducible] wires

private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem candidate_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (FrontierSumCleanup1591Raw.fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 775++OwnDiagAll12Square.kext L).toFinset := by
  have old:=FrontierSumCleanup1591Raw.accPrefixK_support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)
    (OwnDiagAll12Square.kext L) L.core.generic
    (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++OwnDiagAll12Square.kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 775++OwnDiagAll12Square.kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    tauto
  exact old.trans embed

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 775∉wires (FrontierSumCleanup1591Placed.initial L) := by
  rw [FrontierSumCleanup1591Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=candidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic
      (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 775 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 775 (by omega))
  · have away:=resident_away L hn old
      (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 775 (by omega))
  · rw [pool_block L hw 775 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<775:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 775
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 775
      (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b n : Nat)
    (ha : a<2613) (hb : b<2613) (hnn : n<2613) (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b))
      (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare775_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 775∉wires (FrontierSumCleanup1591Square.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 775∉wires (FrontierSumCleanup1591Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 766 1530 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 775∉wires (FrontierSumCleanup1591Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 765 1531 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 775∉wires (FrontierSumCleanup1591Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 767 1532 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 775∉wires (FrontierSumCleanup1591Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 770 1536 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 775∉wires (FrontierSumCleanup1591PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1285 1537 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  have p6 : L.core.poolWire 775∉wires (FrontierSumCleanup1591PlacedQ7.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 1286 1538 775
      (by omega) (by omega) (by omega) (by omega) (by omega)) p5
  exact OwnPlusHost.rename_avoid _ _ _ (pool_swap_fix L hw hn 769 1539 775
    (by omega) (by omega) (by omega) (by omega) (by omega)) p6


def withNorm (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    CuccaroStreamedSquareWideLayout :=
  ⟨{ L.core with normFlag := q }, L.overflowPad⟩

private theorem withNorm_widths (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (q : Wire) : (withNorm L q).Widths :=
  ⟨⟨hw.core.y, hw.core.out, hw.core.product, hw.core.pad, hw.core.work⟩,
    hw.overflowPad⟩

private theorem withNorm_nodup (L : CuccaroStreamedSquareWideLayout) (q : Wire)
    (hn : (q::L.wires).Nodup) : (withNorm L q).wires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro x
  have h := List.nodup_iff_count.mp hn x
  simp only [withNorm,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

/-- Every actual ordinary fold in these fixed schedules is canonical. -/
theorem old_program_withNorm (L : CuccaroStreamedSquareWideLayout)
    (ext : List Wire) (control q : Wire) :
    FrontierSumCleanup1591Raw.accPrefixK L ext control=
      FrontierSumCleanup1591Raw.accPrefixK (withNorm L q) ext control := by
  rfl

private theorem norm_absent_envelope (L : CuccaroStreamedSquareWideLayout)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (off : L.core.normFlag∉ext) :
    L.core.normFlag∉(control::(withNorm L control).wires++ext).toFinset := by
  intro used
  have positive := List.count_pos_iff.mpr (List.mem_toFinset.mp used)
  have bound := List.nodup_iff_count.mp hn L.core.normFlag
  have zero := List.count_eq_zero.mpr off
  simp only [withNorm,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,
    beq_self_eq_true,eq_self_iff_true,ite_true,zero] at positive bound
  omega

theorem old_raw_norm_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (length : 300≤ext.length) (off : L.core.normFlag∉ext) :
    L.core.normFlag∉wires (FrontierSumCleanup1591Raw.accPrefixK L ext control) := by
  rw [old_program_withNorm L ext control control]
  exact fun used => norm_absent_envelope L control hn ext off
    (FrontierSumCleanup1591Raw.accPrefixK_support (withNorm L control)
      (withNorm_widths L hw control) (withNorm_nodup L control hn)
      ext control length used)

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

private theorem norm_off_ext (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.poolWire 646∉kext L := by
  intro used
  obtain ⟨i,hi,hb,_,same⟩ := kext_index L _ used
  have eq := kpool_inj L hw hn 646 i (by omega) (by omega) same
  omega

theorem old_candidate646_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.poolWire 646∉wires (FrontierSumCleanup1591Raw.fastCandidate L) :=
  old_raw_norm_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic (control_nd L hw hn) (kext L) (by simp [kext,wireBlock_length])
    (norm_off_ext L hw hn)

private theorem block646 (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    Square5Placement.blockPerm L 202 (L.core.poolWire 646)=L.core.poolWire 907 := by
  rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 646 (by omega)]
  rfl

private theorem initial_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (P : Program) (off : L.core.poolWire 646∉wires P) :
    L.core.poolWire 907∉wires (renameProgram (Square5Placement.blockPerm L 202) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨q,used,eq⟩ := Finset.mem_image.mp used
  have same := (Square5Placement.blockPerm L 202).injective
    (eq.trans (block646 L hw hn).symm)
  exact off (same ▸ used)

private theorem swap907_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b : Nat) (ha : a<2613) (hb : b<2613)
    (na : 907≠a) (nb : 907≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire 907)=L.core.poolWire 907 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq
    exact na (pool_inj L hw hn 907 a (by omega) ha eq)
  · intro eq
    exact nb (pool_inj L hw hn 907 b (by omega) hb eq)

private theorem through_old_maps (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (P : Program) (off : L.core.poolWire 907∉wires P) :
    L.core.poolWire 907∉wires
      (renameProgram (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775))
      (renameProgram (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539))
      (renameProgram (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538))
      (renameProgram (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537))
      (renameProgram (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536))
      (renameProgram (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532))
      (renameProgram (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531))
      (renameProgram (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) P)))))))) := by
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 768 775 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 765 1531 (by omega) (by omega) (by omega) (by omega))
  exact OwnPlusHost.rename_avoid _ _ _ (swap907_fix L hw hn 766 1530 (by omega) (by omega) (by omega) (by omega)) off

theorem prefix1590_907_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.poolWire 907∉wires (renameProgram (Prefix1590Square.swap L) (FrontierSumCleanup1591Square.program L)) :=
  through_old_maps L hw hn _ (initial_free L hw hn _ (old_candidate646_free L hw hn))


end ECDSAAdd.Entrant.ControlLoan1589SumCleanupSupport

namespace ECDSAAdd.Entrant.ControlLoan1589SumCleanupSquare
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

def square1590 (L : ControlledPointLayout) : Program :=
  renameProgram (Prefix1590Square.swap L) (FrontierSumCleanup1591Square.program L)

def program (L : ControlledPointLayout) : Program :=
  renameProgram (ControlLoan1589Square.swap L) (square1590 L)
attribute [local irreducible] square1590 program

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare775_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 775∉wires (FrontierSumCleanup1591Square.program L) :=
  ControlLoan1589SumCleanupSupport.spare775_free L hw hn

theorem spare907_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 907∉wires (square1590 L) := by
  unfold square1590
  exact ControlLoan1589SumCleanupSupport.prefix1590_907_free L hw hn

theorem correct1590 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (square1590 L) := by
  unfold square1590
  exact OwnDiagAll12Placed.relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ (FrontierSumCleanup1591Square.correct L hw hn)

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) := by
  unfold program
  exact OwnDiagAll12Placed.relabel L (ControlLoan1589Square.swap L)
    (ControlLoan1589Square.pool L hw) (ControlLoan1589Square.outside L hw) _
    (correct1590 L hw hn)

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1:Nat) else 0)) Y G origin) := by
  have h := correct L hw hn X Y G origin
  cases G <;> simpa only [OwnDiagAll12Square.cFlipK,Bool.false_eq_true,
    if_false,if_true,Nat.cast_zero] using h

theorem program_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (FrontierSumCleanup1591Square.program L) m s := by
  have old := FrontierSumCleanup1591Square.correct L hw hn X Y G origin s m v
  have middle := correct1590 L hw hn X Y G origin s m v
  have first := Prefix1590Square.run_eq L hw (FrontierSumCleanup1591Square.program L)
    s m v.clean old.2.clean
  have last := ControlLoan1589Square.run_eq L hw (square1590 L) s m v.clean middle.2.clean
  unfold program square1590
  unfold square1590 at last
  exact last.trans first

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by
        simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

/-- Complete State equality for independent new and old measurement records. -/
theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (ControlLoan1589Square.program L) mOld s := by
  have fresh := correct L hw hn X Y G origin s m v
  have prior := ControlLoan1589Square.correct L hw hn X Y G origin s mOld v
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · exact values_unique fresh.2 prior.2

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

theorem counts_eq_base (L : ControlledPointLayout) :
    toffoliCount (program L)=toffoliCount (FrontierSumCleanup1591Square.program L) ∧
    measurementCount (program L)=measurementCount (FrontierSumCleanup1591Square.program L) := by
  have first := renameProgram_counts (Prefix1590Square.swap L) (FrontierSumCleanup1591Square.program L)
  have last := renameProgram_counts (ControlLoan1589Square.swap L) (square1590 L)
  unfold program square1590
  unfold square1590 at last
  exact ⟨last.1.trans first.1,last.2.trans first.2⟩

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+765=toffoliCount (ControlLoan1589Square.program L) ∧
    measurementCount (program L)+42=measurementCount (ControlLoan1589Square.program L) := by
  have a := counts_eq_base L
  have b := FrontierSumCleanup1591Square.counts_diff L hw
  have c := ControlLoan1589Square.counts L
  have d := PrefixFrontierSquare1591.counts L
  constructor <;> omega

theorem slots_eq_base (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)=Challenge.gateSlots (FrontierSumCleanup1591Square.program L) := by
  have first := Baselines.rename_gateSlots (Prefix1590Square.swap L) (FrontierSumCleanup1591Square.program L)
  have last := Baselines.rename_gateSlots (ControlLoan1589Square.swap L) (square1590 L)
  unfold program square1590
  unfold square1590 at last
  exact last.trans first

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ControlLoan1589Square.program L) := by
  calc
    Challenge.gateSlots (program L)=Challenge.gateSlots (FrontierSumCleanup1591Square.program L) := slots_eq_base L
    _≤Challenge.gateSlots (PrefixFrontierSquare1591.program L) := FrontierSumCleanup1591Square.slots_le L hw
    _=Challenge.gateSlots (ControlLoan1589Square.program L) :=
      (PrefixFrontierSquare1591.slots_eq L).trans (ControlLoan1589Square.slots_eq_old L).symm

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (slots_le L hw).trans (ControlLoan1589Square.slots L hw)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program square1590
  apply gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective
  exact gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective _
    (FrontierSumCleanup1591Square.physical L hw hn)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  have first : wires (square1590 L)⊆(OB5Support.sites L).toFinset := by
    unfold square1590 Prefix1590Square.swap
    exact OwnDiagAll12Placed.swap_support _ _ _ _ (FrontierSumCleanup1591Square.support L hw hn)
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 768
        (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 775
        (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
  unfold program ControlLoan1589Square.swap
  exact OwnDiagAll12Placed.swap_support _ _ _ _ first
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 718
      (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 907
      (Or.inr (Or.inl ⟨by omega,by omega⟩)))))

theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := by
  have first : L.core.poolWire 768∉wires (square1590 L) := by
    unfold square1590 Prefix1590Square.swap
    exact OwnDiagAll12Placed.swap_target_free _ _ _ (spare775_free L hw hn)
  unfold program ControlLoan1589Square.swap
  exact OwnPlusHost.rename_avoid _ _ _
    (pool_swap_fix L hw hn 718 907 768 (by omega) (by omega) (by omega) (by omega) (by omega)) first

theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := by
  unfold program ControlLoan1589Square.swap
  exact OwnDiagAll12Placed.swap_target_free _ _ _ (spare907_free L hw hn)

private theorem old_eight_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769]) :
    L.core.poolWire k∉wires (program L) := by
  have prior := FrontierSumCleanup1591Square.square_free L hw hn k hk
  have bounds : k<2613 ∧ k≠768 ∧ k≠775 ∧ k≠718 ∧ k≠907 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  have first : L.core.poolWire k∉wires (square1590 L) := by
    unfold square1590 Prefix1590Square.swap
    exact OwnPlusHost.rename_avoid _ _ _
      (pool_swap_fix L hw hn 768 775 k (by omega) (by omega) bounds.1 bounds.2.1 bounds.2.2.1) prior
  unfold program ControlLoan1589Square.swap
  exact OwnPlusHost.rename_avoid _ _ _
    (pool_swap_fix L hw hn 718 907 k (by omega) (by omega) bounds.1 bounds.2.2.2.1 bounds.2.2.2.2) first

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h768 : k=768
  · subst k;exact retired_free768 L hw hn
  by_cases h718 : k=718
  · subst k;exact retired_free718 L hw hn
  apply old_eight_free L hw hn k
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
  omega

theorem old_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718]) :
    L.core.poolWire k∉wires (program L) := square_free L hw hn k hk

end ECDSAAdd.Entrant.ControlLoan1589SumCleanupSquare
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589SumCleanupFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589Actual
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589SumCleanupSquare

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.ControlLoan1589SumCleanupFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (division ControlLoan1589.entryKernel L)
    (ControlLoan1589SumCleanupSquare.program L) (exit ControlLoan1589.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+765=toffoliCount Q ∧ measurementCount P+42=measurementCount Q ∧
    gateSlots P≤gateSlots Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=All12Generic.gen L D S P cx cy)
    (hG0 : G0=All12Generic.gen L D Old P cx cy) (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  simp only [Metrics,All12Generic.gen,All12Generic.mid,All12Generic.generic,
    toffoliCount_append,measurementCount_append,gateSlots_append,
    renameProgram_counts,rename_gateSlots] at hs ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Old : Program) (h : Metrics P Old) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Old) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at h ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (ControlLoan1589.gen L cx cy) := by
  have counts:=ControlLoan1589SumCleanupSquare.counts_diff L hw
  have slots:=ControlLoan1589SumCleanupSquare.slots_le L hw
  exact gen_metrics_of_shapes L (division ControlLoan1589.entryKernel L)
    (ControlLoan1589SumCleanupSquare.program L) (ControlLoan1589Square.program L)
    (exit ControlLoan1589.exitKernel L) (gen L cx cy) (ControlLoan1589.gen L cx cy)
    cx cy (by unfold gen; rfl) (by unfold ControlLoan1589.gen ControlLoan1589.square; rfl)
    ⟨counts.1,counts.2,slots⟩

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+765=toffoliCount (ControlLoan1589.gen L cx cy) ∧
    measurementCount (gen L cx cy)+42=measurementCount (ControlLoan1589.gen L cx cy) :=
  ⟨(gen_metrics L hw cx cy).1,(gen_metrics L hw cx cy).2.1⟩

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact All12Generic.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct ControlLoan1589.exitKernel
      ControlLoan1589.exitKernel_support ControlLoan1589.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step ControlLoan1589.entryKernel
      ControlLoan1589.entryKernel_support ControlLoan1589.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (ControlLoan1589SumCleanupSquare.step L hw hn) hc

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  Q1591Resources.gen_sites L hw hn _ _ _
    (division_support ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support L hw)
    (ControlLoan1589SumCleanupSquare.support L hw hn)
    (exit_support ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support L hw) cx cy

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Q1591Resources.gen_physical L hw hn _ _ _
    (division_physical ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_physical L hw hn)
    (ControlLoan1589SumCleanupSquare.physical L hw hn)
    (placed_physical ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_physical L hw hn) cx cy

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤49207648 :=
  (gen_metrics L hw cx cy).2.2.trans (ControlLoan1589.gen_slots L hw cx cy)

private theorem logical718 : base 718∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨718,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  omega

private theorem placed718 (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : base 718∉wires K) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (renameProgram (wireFn2 L) K) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,oldUsed,eq⟩:=Finset.mem_image.mp used
  have mapped : wireFn2 L old=wireFn2 L (base 718) := by
    simpa only [show wireFn2 L (base 718)=L.core.poolWire 718 from rfl] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks oldUsed)) (base 718)
    (ArithmeticOB5.logical_sub_old logical718) mapped
  exact kf (back ▸ oldUsed)

private theorem division718 (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Fp) :
    L.core.poolWire 718∉wires (division ControlLoan1589.entryKernel L c) := by
  have constant:=ExitGenericQ5.constant_ports_avoid_large L hw hn 718 (by omega) L.point.y (Or.inr rfl)
  simp only [division,FrontierEntry1591Callers.entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun used=>constant (EntryFuse.fusedY_support L hw c used),
    placed718 ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_718_free L hw hn⟩

private theorem square_old_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (ControlLoan1589SumCleanupSquare.program L) := by
  apply ControlLoan1589SumCleanupSquare.square_free L hw hn k
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
  tauto

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1589 := by
  unfold gen
  exact ControlLoan1589Inventory.gen_qubits
    (division ControlLoan1589.entryKernel layout) (ControlLoan1589SumCleanupSquare.program layout)
    (exit ControlLoan1589.exitKernel layout)
    (division_support ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support layout layout_widths)
    (ControlLoan1589SumCleanupSquare.support layout layout_widths layout_nodup)
    (exit_support ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support layout layout_widths)
    (division_free ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_free layout layout_widths layout_nodup)
    (square_old_free layout layout_widths layout_nodup)
    (placed_omissions ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_free layout layout_widths layout_nodup)
    (Prefix1590Point.division_768_free ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_768_free layout layout_widths layout_nodup)
    (ControlLoan1589SumCleanupSquare.retired_free768 layout layout_widths layout_nodup)
    (Prefix1590Point.placed_768_free ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_768_free layout layout_widths layout_nodup)
    (division718 layout layout_widths layout_nodup)
    (ControlLoan1589SumCleanupSquare.retired_free718 layout layout_widths layout_nodup)
    (placed718 ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_718_free layout layout_widths layout_nodup) C cx cy

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2154443 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=ControlLoan1589.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1500572 := by
  have h := (wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2.1
  have k := ControlLoan1589.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50007652 :=
  (wrapper_metrics layout C cy _ _ (gen_metrics layout layout_widths cx cy)).2.2.trans
    (ControlLoan1589.wrapper_slots C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2154443,1500572,1589,50007652⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2154443 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1500572 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1589 := by
  cases C with
  | zero => change qubits []≤1589;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50007652 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1500572
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1589
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50007652
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.ControlLoan1589SumCleanupFinal
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589BFFoldCore =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591Square

/-! BF square follow-up. Arithmetic and frame proofs from accepted submission
c7dd1650-6923-4421-88ed-4b740d596c87, pinned commit
12d970b95b7df8a4ec107141cb04aaaba11a0258, DiagSquare.lean:6884-7748.
Source SHA256:9c87c6f99b5428cd1021bdac1f5c230fd5eccd64e459aa31c1d4dee2a42905c9.
The donor comments and proof bodies are retained. This file changes only the
namespace. The 675 T leaf binding is in the separate BFFold module.
Port implementation: GPT6.1Sol Max, Codex.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Classical offset of the restructured B fold. -/
def K : Nat := 4294968272*(2^129-1)

theorem K_lt : K<SquareReduction.p := by
  norm_num [K,SquareReduction.p,SquareReduction.B,SquareReduction.c]

/-- Controlled complement of a register, as a frame transformer. -/
theorem complement_frame (r : List Wire) (hr : r.Nodup) (c : Wire) (hc : c∉r)
    (b : BasisState) (A : Nat) :
    Triple (SquareFrame r b A) (maskedConstant c r (2^r.length-1))
      (SquareFrame r b (if b c then 2^r.length-1-A else A)) := by
  intro s m h
  rw [maskedConstant_run c r _ hc]
  have hcs : s.basis c=b c := h.2 c hc
  cases hb : b c
  · simp only [hcs,hb,Bool.false_eq_true,if_false]
    exact ⟨trivial,h⟩
  · simp only [hcs,hb,if_true]
    rw [OwnDiagAll12Square.xorConstant_ones,notRegister_correct r hr]
    refine ⟨rfl,?_,?_⟩
    · change regValue r (fun w => if w∈r then !s.basis w else s.basis w)=_
      rw [regValue_congr r _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
        regValue_complement,h.1]
    · intro q hq
      change (if q∈r then !s.basis q else s.basis q)=b q
      simp only [hq,if_false]
      exact h.2 q hq

def eReg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.product.take 128++L.core.product.drop 256
def rotWork (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 128++L.core.work.take 128
def rotWCore (L : CuccaroStreamedSquareWideLayout) : MeasuredCanonicalModLayout := {L.measuredCore with src:=rotWork L}
def eBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 129
def eZ (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 129).take 2
def b1Src (L : CuccaroStreamedSquareWideLayout) : List Wire := hiReg L++eZ L
def whiSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 128++eZ L
def wTerms (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold := earlyHTerms (hiReg L)
def eItem (L : CuccaroStreamedSquareWideLayout) : AccItem := ⟨false,[],earlyHTerms (eReg L),earlyHTerms (eReg L)⟩

def wBuild (L : CuccaroStreamedSquareWideLayout) : Program :=
  Acc.sbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 (wTerms L)
def wUnbuild (L : CuccaroStreamedSquareWideLayout) : Program :=
  Acc.sunbuild (accReg L) (accZ L) (accBank L) L.core.cin 163 (wTerms L)
def wCore (L : CuccaroStreamedSquareWideLayout) : Program := qprog (rotWCore L) SquareReduction.p
def eSub (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  subInPlace src (eReg L) (eBank L) L.core.cin
def eAdd (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  addInPlace src (eReg L) (eBank L) L.core.cin
def eFlip (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  maskedConstant c ((eReg L).take 129) (2^129-1)

/-- `-rotW` through the reflected core, forming `e` meanwhile. -/
def wFold (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++(wCore L++(eSub L (b1Src L)++(eAdd L (whiSrc L)++wUnbuild L)))
/-- `+(c-1)·e''` through the reflected core. -/
def eFold (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  eFlip L c++(accFoldQ L (eItem L)++eFlip L c)
/-- Rebuild `W` to restore `b0` from `e`. -/
def wRestore (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++(eSub L (whiSrc L)++(eAdd L (b1Src L)++wUnbuild L))
def bBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQ L (negP L)++(measuredFoldQ L (rot128F L)++(wFold L++(eFold L c++wRestore L)))

/-! Register bookkeeping. -/

theorem layoutCount (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) :
    L.core.y.count q+L.core.out.count q+L.core.product.count q+L.foldPad.count q+L.core.work.count q+
      [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag,
        L.core.sumCarry].count q≤1 := by
  have h := List.nodup_iff_count_le_one.mp hn q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append] at h ⊢
  omega

theorem productSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.product.count q=(L.core.product.take 128).count q+(hiReg L).count q+
      (L.core.product.drop 256).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 256 L.core.product)
  have b := congrArg (List.count q) (List.take_append_drop 128 (L.core.product.take 256))
  rw [List.take_take,show min 128 256=128 by decide] at b
  simp only [List.count_append] at a b
  simp only [hiReg]
  omega

theorem workSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.work.count q=(accReg L).count q+(L.core.work.drop 163).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 163 L.core.work)
  simp only [List.count_append] at a
  simp only [accReg]
  omega

theorem work128Split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.work.count q=(L.core.work.take 128).count q+(L.core.work.drop 128).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 128 L.core.work)
  simp only [List.count_append] at a
  omega

theorem padSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.foldPad.count q=(eBank L).count q+(eZ L).count q+((L.foldPad.drop 129).drop 2).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 129 L.foldPad)
  have b := congrArg (List.count q) (List.take_append_drop 2 (L.foldPad.drop 129))
  simp only [List.count_append] at a b
  simp only [eBank,eZ]
  omega

theorem eReg_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (eReg L).count q=(L.core.product.take 128).count q+(L.core.product.drop 256).count q := by
  simp [eReg,List.count_append]

/-- Registers that the B body never changes outside its sub-steps. -/
theorem other_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (h : q∈hiReg L ∨ q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.out ∧ q∉eReg L ∧ q∉accReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := workSplit L q
  have ec := eReg_count L q
  have pos : 0<(hiReg L).count q ∨ 0<(L.core.work.drop 163).count q ∨ 0<L.foldPad.count q ∨
      0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry].count q := by
    rcases h with h|h|h|h
    · exact Or.inl (List.count_pos_iff.mpr h)
    · exact Or.inr (Or.inl (List.count_pos_iff.mpr h))
    · exact Or.inr (Or.inr (Or.inl (List.count_pos_iff.mpr h)))
    · refine Or.inr (Or.inr (Or.inr (List.count_pos_iff.mpr ?_)))
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  refine ⟨fun h1 => ?_,fun h1 => ?_,fun h1 => ?_⟩
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega

theorem eReg_product (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈eReg L) : q∈L.core.product := by
  simp only [eReg,List.mem_append] at h
  rcases h with h|h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

theorem eReg_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q∈eReg L) :
    q∉L.core.out ∧ q∉accReg L ∧ q∉hiReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := workSplit L q
  have ec := eReg_count L q
  have a := List.count_pos_iff.mpr h
  refine ⟨fun h1 => ?_,fun h1 => ?_,fun h1 => ?_⟩
  · have b := List.count_pos_iff.mpr h1; omega
  · have b := List.count_pos_iff.mpr h1; omega
  · have b := List.count_pos_iff.mpr h1; omega

theorem accReg_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q∈accReg L) :
    q∉L.core.out := by
  have lc := layoutCount L hn q
  have ws := workSplit L q
  have a := List.count_pos_iff.mpr h
  intro h1
  have b := List.count_pos_iff.mpr h1
  omega

theorem eReg_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (eReg L).length=130 := by
  simp [eReg,hw.core.product]

theorem eReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (eReg L).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ec := eReg_count L q
  omega

theorem eReg_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) : regValue (eReg L) t=P%2^128 := by
  rw [eReg,regValue_append,L.product_take_value hw t P hP 128 (by omega),
    L.product_drop_value hw t P hP 256 (by omega),Nat.div_eq_of_lt hb]
  simp

/-! The B-body state: `out`, `e` and the accumulator hold given values, all else is `base`. -/

def BState (L : CuccaroStreamedSquareWideLayout) (base : BasisState) (O E A : Nat) (s : BasisState) : Prop :=
  regValue L.core.out s=O ∧ regValue (eReg L) s=E ∧ regValue (accReg L) s=A ∧
    ∀q,q∉L.core.out → q∉eReg L → q∉accReg L → s q=base q

theorem bstate_other (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A : Nat) (s : BasisState) (h : BState L base O E A s) (q : Wire)
    (hq : q∈hiReg L ∨ q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    s q=base q :=
  let a := other_away L hn q hq
  h.2.2.2 q a.1 a.2.1 a.2.2

theorem bstate_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (hc : L.PairClean base) (O E : Nat) (s : BasisState) (h : BState L base O E 0 s) : L.PairClean s := by
  have keep (q : Wire) (hq : q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
      s q=base q := bstate_other L hn base O E 0 s h q (Or.inr hq)
  constructor
  · exact (regValue_congr _ _ _ (fun q hq => keep q (Or.inr (Or.inl hq)))).trans hc.pad
  · have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) s
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) s=0 :=
      (regValue_congr _ _ _ (fun q hq => keep q (Or.inl hq))).trans
        ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using h.2.2.1
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

/-- Lifting single-register steps to the B-body state. -/
theorem lift_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A O' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue L.core.out (run pr m s).basis=O' ∧
        ∀q,q∉L.core.out → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O' E A) := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,hv,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (eReg_away L hn q hq).1)).trans h.2.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (accReg_out L hn q hq))).trans h.2.2.1
  · intro q h1 h2 h3
    exact (hf q h1).trans (h.2.2.2 q h1 h2 h3)

theorem lift_e (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A E' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue (eReg L) (run pr m s).basis=E' ∧
        ∀q,q∉eReg L → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O E' A) := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,?_,hv,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun he => (eReg_away L hn q he).1 hq))).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun he => (eReg_away L hn q he).2.1 hq))).trans h.2.2.1
  · intro q h1 h2 h3
    exact (hf q h2).trans (h.2.2.2 q h1 h2 h3)

theorem lift_acc (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A A' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue (accReg L) (run pr m s).basis=A' ∧
        ∀q,q∉accReg L → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O E A') := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,?_,?_,hv,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun ha => accReg_out L hn q ha hq))).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun ha => (eReg_away L hn q hq).2.1 ha))).trans h.2.1
  · intro q h1 h2 h3
    exact (hf q h3).trans (h.2.2.2 q h1 h2 h3)


/-! Source values and static facts. -/

theorem accVal_earlyH (t : BasisState) (src : List Wire) :
    Acc.accVal t 0 (earlyHTerms src)=4294968272*regValue src t := by
  simp only [earlyHTerms,Acc.accVal,Acc.step,Acc.earlyTerm,Bool.false_eq_true,if_false,if_true]
  omega

theorem validH (t : BasisState) (src : List Wire) (hl : src.length≤130) :
    Acc.Valid t 163 0 (earlyHTerms src) := by
  have hT := regValue_lt src t
  have hT' : regValue src t<2^130 := lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) hl)
  simp [Acc.Valid,Acc.step,earlyHTerms,Acc.earlyTerm]
  generalize regValue src t=T at hT' ⊢
  omega

theorem earlyH_static (L : CuccaroStreamedSquareWideLayout) (src : List Wire)
    (hs : ∀q,src.count q≤L.core.product.count q) (hl0 : 5≤src.length) (hl : src.length≤130) :
    (∀f∈earlyHTerms src,∀q,f.src.count q≤L.core.product.count q) ∧ (∀f∈earlyHTerms src,TermOK f) := by
  constructor
  · intro f hf
    obtain ⟨e,_⟩ := naf_facts false src f ((earlyH_mem _ _).mp hf)
    rw [e]; exact hs
  · intro f hf
    obtain ⟨e,sh⟩ := naf_facts false src f ((earlyH_mem _ _).mp hf)
    simp only [TermOK,e]
    omega

theorem hiReg_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (hiReg L).count q≤L.core.product.count q := by
  have := productSplit L q; omega

theorem eReg_count_le (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (eReg L).count q≤L.core.product.count q := by
  have := productSplit L q; have := eReg_count L q; omega

theorem hiReg_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (hiReg L).length=128 :=
  (split_lengths L hw).2.1

theorem wTerms_fits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀f∈wTerms L,Acc.Fits (accReg L) (accZ L) (accBank L) L.core.cin 163 f := by
  have st := earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega) (by rw [hiReg_length L hw]; omega)
  intro f hf
  exact fits_of L hw hn f (fun q => by have h := st.1 f hf q; simp only [List.count_append]; omega) (st.2 f hf)

theorem eTerms_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀f∈earlyHTerms (eReg L),∀q,f.src.count q≤L.core.product.count q) ∧
      (∀f∈earlyHTerms (eReg L),TermOK f) :=
  earlyH_static L (eReg L) (eReg_count_le L) (by rw [eReg_length L hw]; omega) (by rw [eReg_length L hw])

theorem eItem_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    AccView L t (eItem L) :=
  plain_view L t false _ (eTerms_static L hw).1 (eTerms_static L hw).2 (validH t (eReg L) (by rw [eReg_length L hw]))

theorem eItem_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : MixStatic L (.inr (eItem L)) := by
  let z : BasisState := fun _ => false
  have h := eItem_view L hw z
  exact ⟨h.count,h.ok,h.preCount,h.preOk⟩

/-! The single steps of the B body. -/

theorem zero_regs (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (hc : L.PairClean base) (O E A : Nat) (s : BasisState) (h : BState L base O E A s) :
    (∀q∈accZ L,s q=false) ∧ (∀q∈accBank L,s q=false) ∧ s L.core.cin=false ∧
      (∀q∈L.foldPad,s q=false) ∧ (∀q∈L.core.work.drop 163,s q=false) := by
  have padZ : ∀q∈L.foldPad,s q=false := fun q hq =>
    (bstate_other L hn base O E A s h q (Or.inr (Or.inr (Or.inl hq)))).trans ((regValue_zero _ _).mp hc.pad q hq)
  have workZ : ∀q∈L.core.work.drop 163,s q=false := fun q hq =>
    (bstate_other L hn base O E A s h q (Or.inr (Or.inl hq))).trans
      ((regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq))
  have dd : (L.core.work.drop 163).drop 33=L.core.work.drop 196 := by simp [List.drop_drop]
  refine ⟨?_,fun q hq => padZ q (List.mem_of_mem_take hq),?_,padZ,workZ⟩
  · intro q hq
    rcases accZ_mem L q hq with h1|h1
    · exact padZ q h1
    · rw [← dd] at h1; exact workZ q (List.mem_of_mem_drop h1)
  · exact (bstate_other L hn base O E A s h _ (Or.inr (Or.inr (Or.inr (by simp))))).trans hc.cin

theorem wBuild_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E 0) (wBuild L) (BState L base O E (4294968272*regValue (hiReg L) base)) := by
  apply lift_acc L hn base O E 0 _ (wBuild L)
  intro s m h
  obtain ⟨hz,hb,hi,_,_⟩ := zero_regs L hn base hc O E 0 s.basis h
  have tr := Acc.sbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    s.basis hz hb hi (wTerms L) (wTerms_fits L hw hn) (validH s.basis (hiReg L) (by rw [hiReg_length L hw]; omega))
    s m ⟨h.2.2.1,fun _ _ => rfl⟩
  have hh : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E 0 s.basis h q (Or.inl hq))
  refine ⟨tr.1,tr.2.1.trans (by rw [wTerms,accVal_earlyH,hh]),tr.2.2⟩

theorem wUnbuild_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (wUnbuild L) (BState L base O E 0) := by
  apply lift_acc L hn base O E _ 0 (wUnbuild L)
  intro s m h
  obtain ⟨hz,hb,hi,_,_⟩ := zero_regs L hn base hc O E _ s.basis h
  have hh : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E _ s.basis h q (Or.inl hq))
  have tr := Acc.sunbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    s.basis hz hb hi (wTerms L) (wTerms_fits L hw hn) (validH s.basis (hiReg L) (by rw [hiReg_length L hw]; omega))
    s m ⟨by rw [wTerms,accVal_earlyH,hh]; exact h.2.2.1,fun _ _ => rfl⟩
  exact ⟨tr.1,tr.2.1,tr.2.2⟩

theorem rotWCore_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (rotWCore L).Widths 256 := by
  have mc := L.measuredCore_widths hw
  refine ⟨?_,mc.out,mc.carry⟩
  simp [rotWCore,rotWork,hw.core.work]

theorem rotWCore_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (rotWCore L).wires.Nodup := by
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp coreNd q
  have w := work128Split L q
  simp only [rotWCore,rotWork,measuredCore,MeasuredCanonicalModLayout.wires,List.count_append] at h ⊢
  omega

theorem rotWork_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (s : BasisState) (W : Nat)
    (hA : regValue (accReg L) s=W) (hz : ∀q∈L.core.work.drop 163,s q=false) :
    regValue (rotWork L) s=W/2^128+2^128*(W%2^128) := by
  have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) s
  rw [List.take_append_drop] at sp
  have hi : regValue (L.core.work.drop 163) s=0 := (regValue_zero _ _).mpr hz
  have wv : regValue L.core.work s=W := by
    rw [sp,hi]; simpa [accReg] using hA
  rw [rotWork,regValue_append,regValue_drop_div _ 128 (by rw [hw.core.work]; omega),
    regValue_take_mod _ 128 (by rw [hw.core.work]; omega),wv]
  simp [hw.core.work]

theorem wCore_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (hO : O<SquareReduction.p) (hW : W<2^163) :
    Triple (BState L base O E W) (wCore L)
      (BState L base ((W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E W) := by
  apply lift_out L hn base O E W _ (wCore L)
  intro s m h
  obtain ⟨_,_,hi,padZ,workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hR : W/2^128+2^128*(W%2^128)<SquareReduction.p := by
    have a : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hW
        _ = 2^35*2^128 := by norm_num
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at a b ⊢
    omega
  have keep (q : Wire) (hq : q=L.core.outHigh ∨ q=L.core.modFlag ∨ q=L.core.productHigh ∨ q=L.core.workHigh) :
      s.basis q=base q :=
    bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl <;> simp))))
  have carryZ : ∀q∈(rotWCore L).carry,s.basis q=false := by
    intro q hq
    simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact padZ q hq
    · exact (keep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hc.productHigh
    · exact (keep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hc.workHigh
  have ek := QCore.qprog_correct (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
    (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hR hO s m
    (rotWork_value L hw s.basis W h.2.2.1 workZ) h.1
    ((keep _ (Or.inl rfl)).trans hc.outHigh) ((keep _ (Or.inr (Or.inl rfl))).trans hc.modFlag) carryZ hi
  exact ⟨ek.1,ek.2.1,ek.2.2⟩

theorem eAdder_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (src : List Wire)
    (hs : src=b1Src L ∨ src=whiSrc L) : (L.core.cin::(src++eReg L++eBank L)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := work128Split L q
  have pd := padSplit L q
  have ec := eReg_count L q
  rcases hs with rfl|rfl <;>
    simp only [b1Src,whiSrc,List.count_cons,List.count_append,List.count_nil] at lc ⊢ <;>
    split <;> split at lc <;> omega

theorem eSrc_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (src : List Wire)
    (hs : src=b1Src L ∨ src=whiSrc L) : src.length=(eReg L).length ∧ (eBank L).length+1=(eReg L).length := by
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  rcases hs with rfl|rfl <;> simp [b1Src,whiSrc,eZ,eBank,eReg,hiReg,fp,hw.core.product,hw.core.work]

theorem eSub_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L)
    (O E A S : Nat) (hval : ∀t,BState L base O E A t → regValue src t=S) :
    Triple (BState L base O E A) (eSub L src) (BState L base O ((E+2^130-S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eSub L src)
  intro s m h
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have nd := eAdder_nodup L hn src hs
  have lens := eSrc_length L hw src hs
  have bank0 : regValue (eBank L) s.basis=0 := (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take hq))
  have spec := subInPlace_spec src (eReg L) (eBank L) L.core.cin nd lens.1 lens.2 S E s m
    ⟨⟨⟨hval s.basis h,h.2.1⟩,hi⟩,bank0⟩
  have hv : regValue (eReg L) (run (subInPlace src (eReg L) (eBank L) L.core.cin) m s).basis=
      (E+2^(eReg L).length-S)%2^(eReg L).length := spec.2.1.1.2
  rw [eReg_length L hw] at hv
  exact ⟨spec.1,hv,fun q hq => subInPlace_frame src (eReg L) (eBank L) L.core.cin nd lens.1 lens.2 s m hi bank0 q hq⟩

theorem eAdd_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L)
    (O E A S : Nat) (hval : ∀t,BState L base O E A t → regValue src t=S) :
    Triple (BState L base O E A) (eAdd L src) (BState L base O ((E+S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eAdd L src)
  intro s m h
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have nd := eAdder_nodup L hn src hs
  have lens := eSrc_length L hw src hs
  have bank0 : regValue (eBank L) s.basis=0 := (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take hq))
  have tr := addInPlace_cin_frame L.core.cin src (eReg L) (eBank L) nd lens.1 lens.2 s.basis false hi bank0 E
    s m ⟨h.2.1,fun _ _ => rfl⟩
  have hv := tr.2.1
  rw [hval s.basis h,eReg_length L hw] at hv
  simp only [Bool.toNat_false,Nat.add_zero] at hv
  exact ⟨tr.1,hv,tr.2.2⟩

def flipE (g : Bool) (E : Nat) : Nat := if g then 2^129*(E/2^129)+(2^129-1-E%2^129) else E

theorem eFlip_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (c : Wire) (hcw : c∉L.wires) (O E A : Nat) :
    Triple (BState L base O E A) (eFlip L c) (BState L base O (flipE (base c) E) A) := by
  apply lift_e L hn base O E A _ (eFlip L c)
  intro s m h
  have nd : ((eReg L).take 129).Nodup := (List.take_sublist _ _).nodup (eReg_nodup L hn)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have cs : s.basis c=base c := h.2.2.2 c
    (fun hm => hcw (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hm]))
    (fun hm => hcw (by have := eReg_product L c hm; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this]))
    (fun hm => hcw (by have := accReg_work L c hm; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this]))
  have lt : ((eReg L).take 129).length=129 := by simp [eReg_length L hw]
  have cmp := complement_frame ((eReg L).take 129) nd c hct s.basis (regValue ((eReg L).take 129) s.basis)
  rw [lt,cs] at cmp
  have tr : (run (eFlip L c) m s).phase=s.phase ∧ SquareFrame ((eReg L).take 129) s.basis
      (if base c then 2^129-1-regValue ((eReg L).take 129) s.basis else regValue ((eReg L).take 129) s.basis)
      (run (eFlip L c) m s).basis := cmp s m ⟨rfl,fun _ _ => rfl⟩
  have el := eReg_length L hw
  have lo : regValue ((eReg L).take 129) s.basis=E%2^129 := by
    rw [regValue_take_mod _ 129 (by omega),h.2.1]
  have hiv : regValue ((eReg L).drop 129) s.basis=E/2^129 := by
    rw [regValue_drop_div _ 129 (by omega),h.2.1]
  have sp := regValue_append ((eReg L).take 129) ((eReg L).drop 129) (run (eFlip L c) m s).basis
  rw [List.take_append_drop,lt] at sp
  have hd : regValue ((eReg L).drop 129) (run (eFlip L c) m s).basis=E/2^129 := by
    rw [← hiv]
    apply regValue_congr
    intro q hq
    apply tr.2.2 q
    intro hm
    have nd2 := eReg_nodup L hn
    rw [← List.take_append_drop 129 (eReg L)] at nd2
    exact List.disjoint_of_nodup_append nd2 hm hq
  refine ⟨tr.1,?_,fun q hq => tr.2.2 q (fun hm => hq (List.mem_of_mem_take hm))⟩
  rw [sp,hd,tr.2.1,lo]
  unfold flipE
  cases base c <;> simp <;> omega

theorem eCore_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (hO : O<SquareReduction.p) :
    Triple (BState L base O E 0) (accFoldQ L (eItem L))
      (BState L base ((4294968272*E+(SquareReduction.p-1-O))%SquareReduction.p) E 0) := by
  apply lift_out L hn base O E 0 _ (accFoldQ L (eItem L))
  intro s m h
  have tr := accFoldQ_frame L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO s m ⟨h.1,fun _ _ => rfl⟩
  have e : Acc.accVal s.basis 0 (eItem L).spec=4294968272*E := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
  rw [e] at tr
  exact ⟨tr.1,tr.2.1,tr.2.2⟩

/-! Composition of the B body. -/

theorem flipE_flipE (g : Bool) (E : Nat) : flipE g (flipE g E)=E := by
  unfold flipE
  cases g
  · simp
  · simp only [if_true]
    have h1 : (2^129*(E/2^129)+(2^129-1-E%2^129))/2^129=E/2^129 := by omega
    have h2 : (2^129*(E/2^129)+(2^129-1-E%2^129))%2^129=2^129-1-E%2^129 := by omega
    rw [h1,h2]
    omega

def bE1 (P : Nat) : Nat := ((P%2^128+2^130-P/2^128)%2^130+(4294968272*(P/2^128))/2^128)%2^130

def bO4 (P : Nat) (g : Bool) (O : Nat) : Nat :=
  (4294968272*flipE g (bE1 P)+(SquareReduction.p-1-
    (((4294968272*(P/2^128))/2^128+2^128*((4294968272*(P/2^128))%2^128)+(SquareReduction.p-1-
      (((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-
        ((P+(SquareReduction.p-1-O))%SquareReduction.p)))%SquareReduction.p)))%SquareReduction.p)))%SquareReduction.p

theorem b1Src_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A : Nat) (t : BasisState) (h : BState L base O E A t) :
    regValue (b1Src L) t=regValue (hiReg L) base := by
  have ez : regValue (eZ L) t=0 := (regValue_zero _ _).mpr (fun q hq =>
    (zero_regs L hn base hc O E A t h).2.2.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  rw [b1Src,regValue_append,ez,Nat.mul_zero,Nat.add_zero]
  exact regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E A t h q (Or.inl hq))

theorem whiSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (t : BasisState) (h : BState L base O E W t) :
    regValue (whiSrc L) t=W/2^128 := by
  have zr := zero_regs L hn base hc O E W t h
  have ez : regValue (eZ L) t=0 := (regValue_zero _ _).mpr (fun q hq =>
    zr.2.2.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) t
  rw [List.take_append_drop] at sp
  have hi : regValue (L.core.work.drop 163) t=0 := (regValue_zero _ _).mpr zr.2.2.2.2
  have wv : regValue L.core.work t=W := by
    rw [sp,hi]; simpa [accReg] using h.2.2.1
  rw [whiSrc,regValue_append,ez,Nat.mul_zero,Nat.add_zero,regValue_drop_div _ 128 (by rw [hw.core.work]; omega),wv]

theorem bBody_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (bBody L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let E1 := bE1 P
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  let O3 := (W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O2))%SquareReduction.p
  let O4 := (4294968272*flipE g E1+(SquareReduction.p-1-O3))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQ L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frame L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQ L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frame L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0
  -- wFold
  have w1 := wBuild_step L hw hn base hc O2 b0
  rw [hb1] at w1
  have w2 := wCore_step L hw hn base hc O2 b0 W hO2 hWlt
  have w3 := eSub_step L hw hn base hc (b1Src L) (Or.inl rfl) O3 b0 W b1
    (fun t h => (b1Src_value L hw hn base hc O3 b0 W t h).trans hb1)
  have w4 := eAdd_step L hw hn base hc (whiSrc L) (Or.inr rfl) O3 ((b0+2^130-b1)%2^130) W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O3 _ W t h)
  have w5 := wUnbuild_step L hw hn base hc O3 (((b0+2^130-b1)%2^130+W/2^128)%2^130)
  rw [hb1] at w5
  have tw : Triple (BState L base O2 b0 0) (wFold L) (BState L base O3 E1 0) :=
    w1.seq (w2.seq (w3.seq (w4.seq w5)))
  -- eFold
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_step L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFold L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestore
  have r1 := wBuild_step L hw hn base hc O4 E1
  rw [hb1] at r1
  have r2 := eSub_step L hw hn base hc (whiSrc L) (Or.inr rfl) O4 E1 W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O4 E1 W t h)
  have r3 := eAdd_step L hw hn base hc (b1Src L) (Or.inl rfl) O4 ((E1+2^130-W/2^128)%2^130) W b1
    (fun t h => (b1Src_value L hw hn base hc O4 _ W t h).trans hb1)
  have back : ((E1+2^130-W/2^128)%2^130+b1)%2^130=b0 := by
    have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
    have hwh : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hWlt
        _ = 2^35*2^128 := by norm_num
    have e0' : b0=P%2^128 := rfl
    have e1' : b1=P/2^128 := rfl
    have hb0' : P%2^128<2^128 := Nat.mod_lt _ (by positivity)
    show ((bE1 P+2^130-W/2^128)%2^130+b1)%2^130=b0
    unfold bE1
    generalize hx : W/2^128=x at hwh
    norm_num at hb0 hb0' hb1lt hwh ⊢
    omega
  have r4 := wUnbuild_step L hw hn base hc O4 b0
  rw [hb1] at r4
  rw [back] at r3
  have tr : Triple (BState L base O4 E1 0) (wRestore L) (BState L base O4 b0 0) :=
    r1.seq (r2.seq (r3.seq r4))
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  exact all

/-! Value of the B body. -/

theorem bO4_cast (M O : Nat) (g : Bool) (hM : M<2^128) (hg : g=false → M=0) (hO : O<SquareReduction.p) :
    ((bO4 (M^2) g O : Nat) : ZMod SquareReduction.p)=(O : ZMod SquareReduction.p)+
      (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p)+
        (if g then (K : ZMod SquareReduction.p) else 0)) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  generalize hPdef : M^2=P at hb ⊢
  have hb1lt : P/2^128<2^128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hb0lt : P%2^128<2^128 := Nat.mod_lt _ (by positivity)
  have hwhi : 4294968272*(P/2^128)/2^128<2^35 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hb1lt ⊢
    omega
  have hEn : g=true → flipE g (bE1 P)+P%2^128+4294968272*(P/2^128)/2^128+1=2^129+P/2^128 := by
    intro hgt
    subst hgt
    unfold flipE bE1
    simp only [if_true]
    generalize 4294968272*(P/2^128)/2^128=x at hwhi ⊢
    norm_num at hb0lt hb1lt hwhi ⊢
    omega
  unfold bO4
  generalize hX1 : (P+(SquareReduction.p-1-O))%SquareReduction.p=X1
  generalize hR : (P/2^128)%2^128+2^128*(P%2^128)=R
  generalize hX2 : (R+(SquareReduction.p-1-X1))%SquareReduction.p=X2
  generalize hW : 4294968272*(P/2^128)=W at hwhi hEn
  generalize hX3 : (W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-X2))%SquareReduction.p=X3
  generalize hE2 : flipE g (bE1 P)=E2 at hEn
  have b1 : X1<SquareReduction.p := by rw [← hX1]; exact Nat.mod_lt _ pmod
  have b2 : X2<SquareReduction.p := by rw [← hX2]; exact Nat.mod_lt _ pmod
  have b3 : X3<SquareReduction.p := by rw [← hX3]; exact Nat.mod_lt _ pmod
  have k1 : (X1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    rw [← hX1,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod O hO]
  have k2 : (X2 : ZMod SquareReduction.p)=(R : ZMod SquareReduction.p)+(-1-(X1 : ZMod SquareReduction.p)) := by
    rw [← hX2,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X1 b1]
  have k3 : (X3 : ZMod SquareReduction.p)=((W/2^128+2^128*(W%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(X2 : ZMod SquareReduction.p)) := by
    rw [← hX3,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X2 b2]
  rw [ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X3 b3,k3,k2,k1]
  have hc : ((SquareReduction.c : Nat) : ZMod SquareReduction.p)=4294968273 := by norm_num [SquareReduction.c]
  have hK : ((K : Nat) : ZMod SquareReduction.p)=4294968272*(2^129-1) := by norm_num [K,SquareReduction.c]
  have hh : (2 : ZMod SquareReduction.p)^256=4294968273 := by rw [← hc]; exact_mod_cast radix_cast
  have nP : P=P%2^128+2^128*(P/2^128) := (Nat.mod_add_div P (2^128)).symm
  have nR : R=P/2^128+2^128*(P%2^128) := by rw [← hR,Nat.mod_eq_of_lt hb1lt]
  have nW : W=W%2^128+2^128*(W/2^128) := (Nat.mod_add_div W (2^128)).symm
  have zP := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nP
  have zR := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nR
  have zW := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nW
  have zW2 := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) hW
  push_cast at zP zR zW zW2 ⊢
  rw [hc]
  cases hgv : g
  · have M0 := hg hgv
    have P0 : P=0 := by rw [← hPdef,M0]; norm_num
    subst P0
    have W0 : W=0 := by rw [← hW]; simp
    subst W0
    have R0 : R=0 := by rw [← hR]; simp
    subst R0
    have E0 : E2=0 := by rw [← hE2,hgv]; simp [flipE,bE1]
    subst E0
    simp only [Bool.false_eq_true,if_false]
    push_cast
    ring
  · have hE := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) (hEn hgv)
    push_cast at hE
    simp only [if_true]
    rw [hK]
    linear_combination 4294968272*hE+zR+zP*(4294968272-2^128)+2^128*zW2+2^128*zW+((W/2^128 : Nat)-(P/2^128 : Nat) : ZMod SquareReduction.p)*hh

def resBF (P O : Nat) (g : Bool) : Nat :=
  ofCast false (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P+
    (if g then (K : ZMod SquareReduction.p) else 0)))

theorem bO4_eq (M O : Nat) (g : Bool) (hM : M<2^128) (hg : g=false → M=0) (hO : O<SquareReduction.p) :
    bO4 (M^2) g O=resBF (M^2) O g := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h := bO4_cast M O g hM hg hO
  have lt : bO4 (M^2) g O<SquareReduction.p := Nat.mod_lt _ pmod
  have v := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt lt] at v
  rw [v]
  simp only [resBF,ofCast,Bool.false_eq_true,if_false,measuredOrientationCast]

/-! Branch A from the plain orientation: `-P`, `+rot128`, `-(complemented acc)` (ends reflected). -/

def aAcc (L : CuccaroStreamedSquareWideLayout) : AccItem :=
  ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩

def aBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQ L (negP L)++(measuredFoldQ L (rot128F L)++OwnDiagAll12Square.accFoldQF L c (aAcc L))

def resAF (P O : Nat) (g : Bool) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P-
    (if g then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))

theorem aBody_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBody L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQ L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frame L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQ L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frame L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have t3 := OwnDiagAll12Square.accFoldQF_frame L hw hn c hcw base (aAcc L) v3 hc O2 hO2
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589BFFold =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589BFFoldCore

/-! BF square on the checked 675 T cleanup leaves, without Trim42.
Adapted from accepted c7dd1650-6923-4421-88ed-4b740d596c87,
commit 12d970b95b7df8a4ec107141cb04aaaba11a0258,
DiagSquare.lean:7749-8372, SHA256
9c87c6f99b5428cd1021bdac1f5c230fd5eccd64e459aa31c1d4dee2a42905c9.
The donor comments and proof bodies are retained. The leaf and branch-C calls
bind to the checked 675 T implementation; no Trim42 program is used.
Port implementation: GPT6.1Sol Max, Codex.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-! Branch wrappers. -/

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591LowK.withLowK2 L ext control L.core.high (L.core.product.take 256) (bBody L control)
def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591LowK.withLowK2 L ext control L.core.low (L.core.product.take 256) (aBody L control)

theorem wires_in (L : CuccaroStreamedSquareWideLayout) (control q : Wire)
    (h : q∈L.core.out ∨ q∈L.core.product ∨ q∈L.core.work ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∈(control::L.wires).toFinset := by
  simp only [List.mem_toFinset,List.mem_cons,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.mem_append,foldPad,List.not_mem_nil,or_false] at h ⊢
  tauto

theorem bBody_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (bBody L control)⊆(control::L.wires).toFinset := by
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have a1 := measuredFoldQ_support L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_support L control (rot128F L) (memP _ sR)
  have wb := Acc.sbuild_support (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_fits L hw hn) (control::L.wires).toFinset (by
      intro f hf q hq
      have st := (earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega)
        (by rw [hiReg_length L hw]; omega)).1 f hf
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      apply wires_in L control q
      rcases hq with rfl|((h|h)|h)|h
      · simp
      · exact Or.inr (Or.inl (memP f st q h))
      · exact Or.inr (Or.inr (Or.inl (accReg_work L q h)))
      · rcases accZ_mem L q h with h1|h1
        · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))))
  have wc : ECDSAAdd.wires (wCore L)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (QCore.qprog_support (rotWCore L) SquareReduction.p hq)
    have hd : q∈L.core.work.drop 128 → q∈L.core.work := List.mem_of_mem_drop
    have ht : q∈L.core.work.take 128 → q∈L.core.work := List.mem_of_mem_take
    apply wires_in L control q
    simp only [rotWCore,rotWork,measuredCore,foldCarry,MeasuredCanonicalModLayout.wires,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have adder (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::(src++eReg L++eBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    apply wires_in L control q
    rcases hq with rfl|((h|h)|h)
    · simp
    · rcases hs with rfl|rfl <;> simp only [b1Src,whiSrc,eZ,List.mem_append] at h
      · rcases h with h|h
        · exact Or.inr (Or.inl (hiReg_product L q h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
      · rcases h with h|h
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
    · exact Or.inr (Or.inl (eReg_product L q h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eSub L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eSub,subInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eAdd L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eAdd,addInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have fl : ECDSAAdd.wires (eFlip L control)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset control ((eReg L).take 129) (2^129-1) hq)
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · exact wires_in L control q (Or.inr (Or.inl (eReg_product L q (List.mem_of_mem_take h))))
  have st := eItem_static L hw
  have ac := accFoldQ_support L hw hn control (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  simp only [bBody,wFold,eFold,wRestore,wBuild,wUnbuild,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩

theorem aBody_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (aBody L control)⊆(control::L.wires).toFinset := by
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have a1 := measuredFoldQ_support L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_support L control (rot128F L) (memP _ sR)
  have a3 := OwnDiagAll12Square.accFoldQF_support L hw hn control (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [aBody,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,a3⟩


/-! Resources of the two bodies. -/

theorem wTerms_okLen (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    ∀f∈wTerms L,Acc.FitsLen (accZ L) (accBank L) 163 f := by
  have st := earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega)
    (by rw [hiReg_length L hw]; omega)
  intro f hf
  exact fitsLen_of L hw f (st.2 f hf)

theorem wTerms_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : Acc.sbuildT 163 (wTerms L)=394 := by
  have hl := hiReg_length L hw
  norm_num [wTerms,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,Acc.buildT,hl]

theorem eItem_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQ (eItem L)=1555 := by
  have hl := eReg_length L hw
  norm_num [eItem,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hl]

theorem aAcc_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQ (aAcc L)=1555 := by
  norm_num [aAcc,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hw.core.product]

theorem bBody_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBody L c)=5948 ∧ measurementCount (bBody L c)=5952 := by
  have q1 := measuredFoldQ_counts L hw (negP L)
  have q2 := measuredFoldQ_counts L hw (rot128F L)
  have bc := Acc.sbuild_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_okLen L hw)
  rw [wTerms_price L hw] at bc
  have wb : toffoliCount (wBuild L)=394 ∧ measurementCount (wBuild L)=394 := bc.1
  have wu : toffoliCount (wUnbuild L)=394 ∧ measurementCount (wUnbuild L)=394 := bc.2
  have core := QCore.qprog_counts (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)
  have wc : toffoliCount (wCore L)=767 ∧ measurementCount (wCore L)=768 :=
    ⟨core.1.trans (by norm_num),core.2.trans (by norm_num)⟩
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have s1 : toffoliCount (eSub L (b1Src L))=129 ∧ measurementCount (eSub L (b1Src L))=129 := by
    have h := subInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have s2 : toffoliCount (eSub L (whiSrc L))=129 ∧ measurementCount (eSub L (whiSrc L))=129 := by
    have h := subInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a1 : toffoliCount (eAdd L (b1Src L))=129 ∧ measurementCount (eAdd L (b1Src L))=129 := by
    have h := addInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a2 : toffoliCount (eAdd L (whiSrc L))=129 ∧ measurementCount (eAdd L (whiSrc L))=129 := by
    have h := addInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have fl : toffoliCount (eFlip L c)=0 ∧ measurementCount (eFlip L c)=0 :=
    maskedConstant_counts c ((eReg L).take 129) (2^129-1)
  have st := eItem_static L hw
  have ac := accFoldQ_counts L hw (eItem L) st.2.1 st.2.2.2
  rw [eItem_price L hw] at ac
  simp only [bBody,wFold,eFold,wRestore,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1.1,s1.2,s2.1,s2.2,a1.1,a1.2,a2.1,a2.2,fl.1,fl.2,ac.1,ac.2]
  exact ⟨trivial,trivial⟩

theorem aBody_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (aBody L c)=3089 ∧ measurementCount (aBody L c)=3092 := by
  have q1 := measuredFoldQ_counts L hw (negP L)
  have q2 := measuredFoldQ_counts L hw (rot128F L)
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have k := OwnDiagAll12Square.accFoldQF_counts L c (aAcc L)
  have a := accFoldQ_counts L hw (aAcc L) sA.2.1 sA.2.2.2
  rw [aAcc_price L hw] at a
  simp only [aBody,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,k.1,k.2,a.1,a.2]
  exact ⟨trivial,trivial⟩

theorem bBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBody L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physical L hw nd (negP L) sP
  have p2 := measuredFoldQ_physical L hw nd (rot128F L) sR
  have wb := Acc.sbuild_physical (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_fits L hw nd)
  have wc := QCore.qprog_physical (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have adderNd (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::src++eReg L++eBank L).Nodup := by
    have h := eAdder_nodup L nd src hs
    simpa only [List.cons_append,List.append_assoc] using h
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eSub L src) :=
    subInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eAdd L src) :=
    addInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := accFoldQ_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  simp only [bBody,wFold,eFold,wRestore,gatePhysical_append]
  exact ⟨p1,p2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩

theorem aBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (aBody L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have p1 := measuredFoldQ_physical L hw nd (negP L) sP
  have p2 := measuredFoldQ_physical L hw nd (rot128F L) sR
  have p3 := OwnDiagAll12Square.accFoldQF_physical L hw nd c hcw (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [aBody,gatePhysical_append]
  exact ⟨p1,p2,p3⟩

theorem bBody_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Challenge.gateSlots (bBody L c)≤300000 := by
  have q1 := measuredFoldQ_gateSlots L hw (negP L)
  have q2 := measuredFoldQ_gateSlots L hw (rot128F L)
  have bs := Acc.sbuild_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_okLen L hw)
  have wl : (wTerms L).length=4 := by simp [wTerms,earlyHTerms]
  rw [wl] at bs
  have wb : Challenge.gateSlots (wBuild L)≤4*(14*163) := bs.1
  have wu : Challenge.gateSlots (wUnbuild L)≤4*(14*163) := bs.2
  have wc : Challenge.gateSlots (wCore L)≤67*256+41 :=
    QCore.qprog_gateSlots (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw)
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have s1 : Challenge.gateSlots (eSub L (b1Src L))≤12*130+2*130 := by
    have h := Baselines.subInPlace_gateSlots_le (b1Src L) (eReg L) (eBank L) L.core.cin
    rw [l1.1,el] at h; exact h
  have s2 : Challenge.gateSlots (eSub L (whiSrc L))≤12*130+2*130 := by
    have h := Baselines.subInPlace_gateSlots_le (whiSrc L) (eReg L) (eBank L) L.core.cin
    rw [l2.1,el] at h; exact h
  have a1 : Challenge.gateSlots (eAdd L (b1Src L))≤12*130 := by
    have h := Baselines.addInPlace_gateSlots_le (b1Src L) (eReg L) (eBank L) L.core.cin
    rw [l1.1,el] at h; exact h
  have a2 : Challenge.gateSlots (eAdd L (whiSrc L))≤12*130 := by
    have h := Baselines.addInPlace_gateSlots_le (whiSrc L) (eReg L) (eBank L) L.core.cin
    rw [l2.1,el] at h; exact h
  have fl : Challenge.gateSlots (eFlip L c)≤129 := by
    have h := Baselines.maskedConstant_gateSlots_le c ((eReg L).take 129) (2^129-1)
    have fll : ((eReg L).take 129).length=129 := by simp [el]
    rw [fll] at h; exact h
  have st := eItem_static L hw
  have ac := accFoldQ_gateSlots L hw (eItem L) st.2.1 st.2.2.2
  have tl : (eItem L).terms.length=4 := by simp [eItem,earlyHTerms]
  have pl : (eItem L).pre.length=0 := by simp [eItem]
  rw [tl,pl] at ac
  simp only [bBody,wFold,eFold,wRestore,Challenge.gateSlots_append]
  omega

theorem aBody_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Challenge.gateSlots (aBody L c)≤150000 := by
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have q1 := measuredFoldQ_gateSlots L hw (negP L)
  have q2 := measuredFoldQ_gateSlots L hw (rot128F L)
  have b := OwnDiagAll12Square.accFoldQF_gateSlots L hw c (aAcc L) sA.2.1 sA.2.2.2
  have lt : (aAcc L).terms.length=4 := by simp [aAcc,earlyHTerms]
  have lp : (aAcc L).pre.length=0 := by simp [aAcc]
  rw [lt,lp] at b
  simp only [aBody,Challenge.gateSlots_append]
  omega

/-! The two restructured branches. -/

theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchBF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bBody_support L hw nd control hw'))
  apply FrontierSumCleanup1591LowK.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (bBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have frame := bBody_frame L hw nd control hcw t.basis M mb full clean O hO t m ⟨outO,fun _ _ => rfl⟩
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  rw [bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchAF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (aBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (aBody_support L hw nd control hw'))
  apply FrontierSumCleanup1591LowK.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (aBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have frame := aBody_frame L hw nd control hcw t.basis M mb full clean O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

/-! The whole square: B, C, A, then one output reflection. -/

/-- Branch C of `OwnDiagAll12Square` (plain → plain), branch B (restructured fold, plain → plain),
branch A (plain → reflected), then one output reflection: nine reflected cores and the reflection leave
the plain orientation; the complemented accumulators of C and A cancel, the classical offset is `control·K`. -/
def program (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  FrontierSumCleanup1591Raw.accBranchCK L ext control++branchBF L ext control++branchAF L ext control++L.reflectOutput

theorem complete_exact (enabled : Bool) (A B O : Nat) :
    SquareReduction.p-1-resAF ((if enabled then A else 0)^2)
      (resBF ((if enabled then B else 0)^2) (OwnDiagAll12Square.resCF enabled ((if enabled then A+B else 0)^2) O) enabled)
        enabled=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := resBF PB OC enabled
  let OA := resAF PA OB enabled
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then OwnDiagAll12Square.cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast false OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB+
        (if enabled then (K : ZMod SquareReduction.p) else 0)) := cast_ofCast _ _
  have ea : measuredOrientationCast true OA=measuredOrientationCast false OB+
      ((PA : ZMod SquareReduction.p)*2^128-PA-(if enabled then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)) :=
    cast_ofCast _ _
  rw [Nat.cast_ite,Nat.cast_zero] at ec
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have hrefl := measuredReflection_zmod OA oaBound
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%
      SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have ite_cast : (((if enabled then K else 0 : Nat)) : ZMod SquareReduction.p)=
      (if enabled then (K : ZMod SquareReduction.p) else 0) := by
    cases enabled <;> simp
  have cast : ((SquareReduction.p-1-OA : Nat) : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%
        SquareReduction.p : Nat) : ZMod SquareReduction.p) := by
    rw [hrefl,ZMod.natCast_mod,Nat.cast_add,subModValue_cast,ite_cast]
    linear_combination ea+ec+eb+identity
  have lhsBound : SquareReduction.p-1-OA<SquareReduction.p := by
    have : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
    omega
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt lhsBound,ZMod.val_natCast_of_lt targetBound] using value

theorem correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (program L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (program L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (program L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := resBF PB OC enabled
  let OA := resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (FrontierSumCleanup1591Raw.accBranchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := FrontierSumCleanup1591Raw.accBranchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepR : Triple (SquareFrame L.core.out s.basis OA) L.reflectOutput
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := L.reflectOutput_correct hw nd OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (program L ext control)=2*FrontierSumCleanup1591LowK.lowkcostTPair 128+FrontierSumCleanup1591LowK.lowkcostTPair 129+12708 ∧
      measurementCount (program L ext control)=4*FrontierSumCleanup1591LowK.lowkcost2 128+2*FrontierSumCleanup1591LowK.lowkcost2 129+12717 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) (by omega) (by omega) (by omega) he
  have b := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) (by omega) (by omega) (by omega) he
  have c := FrontierSumCleanup1591LowK.withLowK2_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := aBody_counts L hw control
  have fb := bBody_counts L hw control
  have fc := OwnDiagAll12Square.bodyC_counts L hw control
  have sum := ECDSAAdd.Entrant.gSum_counts L hw
  have r := (L.measured_small_operation_counts hw).2.2
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [program,branchAF,branchBF,FrontierSumCleanup1591Raw.accBranchCK,FrontierSumCleanup1591Raw.accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2,r.1,r.2]
  constructor <;> omega

theorem reflect_support (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
  (L.measured_small_support control).2.2.1

theorem support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (program L ext control)⊆(control::L.wires++ext).toFinset := by
  have a := aBody_support L hw hn control
  have b := bBody_support L hw hn control
  have c := OwnDiagAll12Square.bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) hl hp (by omega) (by omega) (by omega) he a
  have sb := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) hb hp (by omega) (by omega) (by omega) he b
  have sc := FrontierSumCleanup1591LowK.withLowK2_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (ECDSAAdd.Entrant.gSum_support L hw control).1.trans embed
  have unprep := (ECDSAAdd.Entrant.gSum_support L hw control).2.trans embed
  have rf := (reflect_support L control).trans embed
  simp only [program,branchAF,branchBF,FrontierSumCleanup1591Raw.accBranchCK,FrontierSumCleanup1591Raw.accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩,rf⟩

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : ECDSAAdd.Entrant.ExtOK L control ext) :
    GatePhysical (program L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (aBody_physical L hw control hn)
  have b := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (bBody_physical L hw control hn)
  have c := FrontierSumCleanup1591LowK.withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _ (OwnDiagAll12Square.bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (ECDSAAdd.Entrant.gSum_physical L hw nd).1
  have clear := (ECDSAAdd.Entrant.gSum_physical L hw nd).2
  have rf := L.reflectOutput_physical nd
  simp only [program,branchAF,branchBF,FrontierSumCleanup1591Raw.accBranchCK,FrontierSumCleanup1591Raw.accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩,rf⟩

theorem gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (program L ext control) ≤ 8000000 := by
  have ha := aBody_gateSlots L hw control
  have hb := bBody_gateSlots L hw control
  have hc := OwnDiagAll12Square.bodyC_gateSlots L hw control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) (by omega) (by omega) (by omega) he
  have b := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) (by omega) (by omega) (by omega) he
  have c := FrontierSumCleanup1591LowK.withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := ECDSAAdd.Entrant.gSum_gateSlots L hw
  have rf := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [program,branchAF,branchBF,FrontierSumCleanup1591Raw.accBranchCK,FrontierSumCleanup1591Raw.accMiddleCK,Challenge.gateSlots_append]
  omega


theorem counts_exact (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (program L ext control)=52337 ∧
      measurementCount (program L ext control)=53069 := by
  have h := counts L hw ext control he
  norm_num [FrontierSumCleanup1591LowK.lowkcostTPair,
    FrontierSumCleanup1591LowK.lowkcostTMake,FrontierSumCleanup1591LowK.lowkcostTClear,
    FrontierSumCleanup1591LowK.lowkcost2] at h
  exact h

/-- NormFlag is absent from every emitted BF block. -/
def withNorm (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    CuccaroStreamedSquareWideLayout :=
  ⟨{L.core with normFlag:=q},L.overflowPad⟩

theorem program_withNorm (L : CuccaroStreamedSquareWideLayout)
    (ext : List Wire) (control q : Wire) :
    program L ext control=program (withNorm L q) ext control := by
  rfl

private theorem withNorm_widths (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (q : Wire) : (withNorm L q).Widths :=
  ⟨⟨hw.core.y,hw.core.out,hw.core.product,hw.core.pad,hw.core.work⟩,hw.overflowPad⟩

private theorem withNorm_nodup (L : CuccaroStreamedSquareWideLayout) (q : Wire)
    (hn : (q::L.wires).Nodup) : (withNorm L q).wires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro x
  have h := List.nodup_iff_count.mp hn x
  simp only [withNorm,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

private theorem norm_absent_envelope (L : CuccaroStreamedSquareWideLayout)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (off : L.core.normFlag∉ext) :
    L.core.normFlag∉(control::(withNorm L control).wires++ext).toFinset := by
  intro used
  have positive := List.count_pos_iff.mpr (List.mem_toFinset.mp used)
  have bound := List.nodup_iff_count.mp hn L.core.normFlag
  have zero := List.count_eq_zero.mpr off
  simp only [withNorm,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,
    beq_self_eq_true,eq_self_iff_true,ite_true,zero] at positive bound
  omega

theorem norm_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (length : 300≤ext.length) (off : L.core.normFlag∉ext) :
    L.core.normFlag∉wires (program L ext control) := by
  rw [program_withNorm L ext control control]
  exact fun used => norm_absent_envelope L control hn ext off
    (support (withNorm L control) (withNorm_widths L hw control)
      (withNorm_nodup L control hn) ext control length used)

end ECDSAAdd.Entrant.ControlLoan1589BFFold
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589BFSquare =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589BFFold
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589Square

/-! BF square with the existing Q1589 placement, 675 T leaves and no Trim42.
The BF arithmetic is from accepted c7dd1650-6923-4421-88ed-4b740d596c87,
commit 12d970b95b7df8a4ec107141cb04aaaba11a0258, DiagSquare.lean,
SHA256: 9c87c6f99b5428cd1021bdac1f5c230fd5eccd64e459aa31c1d4dee2a42905c9.
Placement and omission proofs retain the fixed accepted682/783 layout and
existing 775/907 maps. No point adapter or rolling719 program is changed.
Port implementation: GPT6.1Sol Max, Codex.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ControlLoan1589BFSquare
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  Arithmetic.CuccaroStreamedSquareWideLayout OwnDiagAll12Square
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def fastCandidate (L : ControlledPointLayout) : Program :=
  ControlLoan1589BFFold.program L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := ControlLoan1589BFFold.correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply ControlLoan1589BFFold.physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (OwnDiagAll12Square.kext L)
  · have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢; omega
  · exact kext_ok L hw hn

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 775++OwnDiagAll12Square.kext L).toFinset := by
  have old:=ControlLoan1589BFFold.support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)
    (OwnDiagAll12Square.kext L) L.core.generic
    (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++OwnDiagAll12Square.kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 775++OwnDiagAll12Square.kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    tauto
  exact old.trans embed


def initial (L : ControlledPointLayout) : Program :=
  renameProgram (Square5Placement.blockPerm L 202) (fastCandidate L)
def plus (L : ControlledPointLayout) : Program := renameProgram (OwnPlusSquare.swap L) (initial L)
def guard (L : ControlledPointLayout) : Program := renameProgram (OwnGuardSquare.swap L) (plus L)
def minus (L : ControlledPointLayout) : Program := renameProgram (OwnQ4Square.swap L) (guard L)
def placed5 (L : ControlledPointLayout) : Program := renameProgram (OwnQ5Square.swap L) (minus L)
def placed6 (L : ControlledPointLayout) : Program := renameProgram (OwnDiagAll12PlacedQ6.swap L) (placed5 L)
def placed7 (L : ControlledPointLayout) : Program := renameProgram (OwnDiagAll12PlacedQ7.swap L) (placed6 L)
def baseProgram (L : ControlledPointLayout) : Program := renameProgram (PrefixFrontierSquare1591.swap L) (placed7 L)
def square1590 (L : ControlledPointLayout) : Program := renameProgram (Prefix1590Square.swap L) (baseProgram L)
def program (L : ControlledPointLayout) : Program := renameProgram (ControlLoan1589Square.swap L) (square1590 L)

/-- Explicit-offset contract. The BF offset is not the old square offset. -/
def SquareCorrectK (L : ControlledPointLayout) (offset : Nat) (P : Program) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState),
    Triple (PointDialogValues L X Y G origin) P
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (offset : Fp) else 0)) Y G origin)

private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrectK L K (fastCandidate L) := by
  intro X Y G origin s m v
  obtain ⟨hp,hx,hf⟩ := fastCandidate_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  have hK : ((K : Nat) : Fp).val=K := ZMod.val_natCast_of_lt
    (by norm_num [K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul,hK] using hx

private theorem relabel (L : ControlledPointLayout) (offset : Nat) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool)
    (hf : ∀q,q∉L.dialogPool → e q=q) (P : Program) (correct : SquareCorrectK L offset P) :
    SquareCorrectK L offset (renameProgram e P) := by
  intro X Y G origin s m v
  have old := correct X Y G origin s m v
  have eq := Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean old.2.clean
  simpa only [eq] using old

theorem correct_base (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrectK L K (baseProgram L) := by
  have a := relabel L K (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have b := relabel L K (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw)
    (OwnPlusSquare.outside L hw) _ a
  have c := relabel L K (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw)
    (OwnGuardSquare.outside L hw) _ b
  have d := relabel L K (OwnQ4Square.swap L) (OwnQ4Square.pool L hw)
    (OwnQ4Square.outside L hw) _ c
  have e := relabel L K (OwnQ5Square.swap L) (OwnQ5Square.pool L hw)
    (OwnQ5Square.outside L hw) _ d
  have f := relabel L K (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw)
    (OwnDiagAll12PlacedQ6.outside L hw) _ e
  have g := relabel L K (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw)
    (OwnDiagAll12PlacedQ7.outside L hw) _ f
  exact relabel L K (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw)
    (PrefixFrontierSquare1591.outside L hw) _ g

theorem correct1590 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrectK L K (square1590 L) :=
  relabel L K (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ (correct_base L hw hn)

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrectK L K (program L) :=
  relabel L K (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw)
    (ControlLoan1589Square.outside L hw) _ (correct1590 L hw hn)

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K : Fp) else 0)) Y G origin) :=
  correct L hw hn X Y G origin

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

theorem independent_records (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m n : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (program L) n s := by
  have a := correct L hw hn X Y G origin s m v
  have b := correct L hw hn X Y G origin s n v
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · exact values_unique a.2 b.2

private theorem tRename (f : Wire→Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mRename (f : Wire→Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52337 ∧ measurementCount (program L)=53069 := by
  have h := ControlLoan1589BFFold.counts_exact L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (OwnDiagAll12Square.kext L) L.core.generic
    (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,square1590,baseProgram,placed7,placed6,placed5,minus,guard,plus,initial,
    fastCandidate,tRename,mRename] using h

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+846=toffoliCount (FrontierSumCleanup1591Square.program L) ∧
    measurementCount (program L)+849=measurementCount (FrontierSumCleanup1591Square.program L) := by
  have a := counts L hw
  have b := FrontierSumCleanup1591Square.counts L
  have c := FrontierSumCleanup1591PlacedQ7.counts L hw
  have d := FrontierSumCleanup1591PlacedQ6.counts L hw
  norm_num [FrontierSumCleanup1591LowK.lowkcostTPair,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2] at d
  constructor <;> omega

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 := by
  have h := ControlLoan1589BFFold.gateSlots_le L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (OwnDiagAll12Square.kext L) L.core.generic
    (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,square1590,baseProgram,placed7,placed6,placed5,minus,guard,plus,initial,
    fastCandidate,Baselines.rename_gateSlots] using h


theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have a := gatePhysical_rename (Square5Placement.blockPerm L 202)
    (Square5Placement.blockPerm L 202).injective _ (fastCandidate_physical L hw hn)
  have p0 := gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective _ a
  have p1 := gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective _ p0
  have p2 := gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective _ p1
  have p3 := gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective _ p2
  have p4 := gatePhysical_rename (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.swap L).injective _ p3
  have p5 := gatePhysical_rename (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.swap L).injective _ p4
  have p6 := gatePhysical_rename (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.swap L).injective _ p5
  have p7 := gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective _ p6
  exact gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective _ p7

private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

private theorem pool_site (L : ControlledPointLayout) (n : Nat)
    (hn : (717≤n ∧ n<1029) ∨ (1284≤n ∧ n<1540)) :
    L.core.poolWire n∈(OB5Support.sites L).toFinset := by
  apply List.mem_toFinset.mpr
  apply OB5Support.pool_in_sites
  apply OB5Support.pool_mem
  rcases hn with h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1,by omega⟩))

private theorem initial_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (initial L)⊆(OB5Support.sites L).toFinset := by
  rw [initial,renameProgram_support]
  intro q hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  have support := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  apply List.mem_toFinset.mpr
  rcases support with h|h|h|h|h
  · subst old
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _
      (resident_away L hn _ (by simp [CompressedPointSquare.residents,inPlaceFlags]))]
    simp [OB5Support.sites]
  · have away := resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
    simp only [OB5Support.sites,List.mem_cons,List.mem_append]
    exact Or.inl (Or.inr h)
  · have away := resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
    simp only [OB5Support.sites,List.mem_cons,List.mem_append]
    exact Or.inl (Or.inl (Or.inr h))
  · rw [pool_block L hw 775 (by omega)] at h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have bound : i<775 := by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
    apply OB5Support.pool_in_sites
    apply OB5Support.pool_mem
    unfold Square5Placement.blockIndex
    split_ifs <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩ := OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
    apply OB5Support.pool_in_sites
    apply OB5Support.pool_mem
    unfold Square5Placement.blockIndex
    split_ifs <;> omega

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  have a := initial_support L hw hn
  have p0 := FrontierSumCleanup1591Placed.swap_support (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) _ a
    (pool_site L 766 (by omega)) (pool_site L 1530 (by omega))
  have p1 := FrontierSumCleanup1591Placed.swap_support (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) _ p0
    (pool_site L 765 (by omega)) (pool_site L 1531 (by omega))
  have p2 := FrontierSumCleanup1591Placed.swap_support (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) _ p1
    (pool_site L 767 (by omega)) (pool_site L 1532 (by omega))
  have p3 := FrontierSumCleanup1591Placed.swap_support (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) _ p2
    (pool_site L 770 (by omega)) (pool_site L 1536 (by omega))
  have p4 := FrontierSumCleanup1591Placed.swap_support (placed5 L) (L.core.poolWire 1285) (L.core.poolWire 1537) _ p3
    (pool_site L 1285 (by omega)) (pool_site L 1537 (by omega))
  have p5 := FrontierSumCleanup1591Placed.swap_support (placed6 L) (L.core.poolWire 1286) (L.core.poolWire 1538) _ p4
    (pool_site L 1286 (by omega)) (pool_site L 1538 (by omega))
  have p6 := FrontierSumCleanup1591Placed.swap_support (placed7 L) (L.core.poolWire 769) (L.core.poolWire 1539) _ p5
    (pool_site L 769 (by omega)) (pool_site L 1539 (by omega))
  have p7 := FrontierSumCleanup1591Placed.swap_support (baseProgram L) (L.core.poolWire 768) (L.core.poolWire 775) _ p6
    (pool_site L 768 (by omega)) (pool_site L 775 (by omega))
  exact FrontierSumCleanup1591Placed.swap_support (square1590 L) (L.core.poolWire 718) (L.core.poolWire 907) _ p7
    (pool_site L 718 (by omega)) (pool_site L 907 (by omega))

private theorem initial_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (n : Nat) (allowed : n∈[1800,1530,1531,1532,1536,1537,1538,1539,775]) :
    L.core.poolWire n∉wires (initial L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · rw [pool_block L hw 775 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<775:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega


private theorem norm_off_ext (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.poolWire 646∉OwnDiagAll12Square.kext L := by
  intro used
  obtain ⟨i,hi,hb,_,same⟩ := OwnDiagAll12Square.kext_index L _ used
  have eq := OwnDiagAll12Square.kpool_inj L hw hn 646 i (by omega) (by omega) same
  omega

private theorem candidate646_free (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.core.poolWire 646∉wires (fastCandidate L) :=
  ControlLoan1589BFFold.norm_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic (control_nd L hw hn) (OwnDiagAll12Square.kext L)
    (by simp [OwnDiagAll12Square.kext,wireBlock_length]) (norm_off_ext L hw hn)

private theorem initial907_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 907∉wires (initial L) := by
  have hit : Square5Placement.blockPerm L 202 (L.core.poolWire 646)=L.core.poolWire 907 := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 646 (by omega)]
    rfl
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨q,used,eq⟩ := Finset.mem_image.mp used
  have same := (Square5Placement.blockPerm L 202).injective (eq.trans hit.symm)
  exact candidate646_free L hw hn (same ▸ used)

private theorem rename_free (e : Equiv.Perm Wire) (P : Program) (pre target : Wire)
    (hit : e pre=target) (off : pre∉wires P) : target∉wires (renameProgram e P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
  have same := e.injective (eq.trans hit.symm)
  exact off (same ▸ hq)

private theorem pool_swap_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613) (hna : n≠a) (hnb : n≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare775_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 775∉wires (baseProgram L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 769 1539 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 1286 1538 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 1285 1537 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 770 1536 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 767 1532 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 765 1531 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 766 1530 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 775 (by simp))))))))

theorem spare907_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 907∉wires (square1590 L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 768 775 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 769 1539 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 1286 1538 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 1285 1537 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 770 1536 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 767 1532 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 765 1531 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 766 1530 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial907_free L hw hn))))))))

private theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 718 907 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 768 775 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 769 1539 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 1286 1538 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 1285 1537 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 770 1536 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 767 1532 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 765 1531 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1800) (L.core.poolWire 1800) (pool_swap_fix L hw hn 766 1530 1800 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1800 (by simp))))))))))

private theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 718 907 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 768 775 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 769 1539 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 1286 1538 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 1285 1537 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 770 1536 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 767 1532 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 766) (L.core.poolWire 766) (pool_swap_fix L hw hn 765 1531 766 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1530) (L.core.poolWire 766) (Equiv.swap_apply_right _ _)
    (initial_free L hw hn 1530 (by simp))))))))))

private theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 718 907 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 768 775 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 769 1539 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 1286 1538 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 1285 1537 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 770 1536 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 765) (L.core.poolWire 765) (pool_swap_fix L hw hn 767 1532 765 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1531) (L.core.poolWire 765) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1531) (L.core.poolWire 1531) (pool_swap_fix L hw hn 766 1530 1531 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1531 (by simp))))))))))

private theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 718 907 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 768 775 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 769 1539 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 1286 1538 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 1285 1537 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 767) (L.core.poolWire 767) (pool_swap_fix L hw hn 770 1536 767 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1532) (L.core.poolWire 767) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1532) (L.core.poolWire 1532) (pool_swap_fix L hw hn 765 1531 1532 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1532) (L.core.poolWire 1532) (pool_swap_fix L hw hn 766 1530 1532 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1532 (by simp))))))))))

private theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 770) (L.core.poolWire 770) (pool_swap_fix L hw hn 718 907 770 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 770) (L.core.poolWire 770) (pool_swap_fix L hw hn 768 775 770 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 770) (L.core.poolWire 770) (pool_swap_fix L hw hn 769 1539 770 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 770) (L.core.poolWire 770) (pool_swap_fix L hw hn 1286 1538 770 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 770) (L.core.poolWire 770) (pool_swap_fix L hw hn 1285 1537 770 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 1536) (L.core.poolWire 770) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1536) (L.core.poolWire 1536) (pool_swap_fix L hw hn 767 1532 1536 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1536) (L.core.poolWire 1536) (pool_swap_fix L hw hn 765 1531 1536 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1536) (L.core.poolWire 1536) (pool_swap_fix L hw hn 766 1530 1536 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1536 (by simp))))))))))

private theorem free1285 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 1285) (L.core.poolWire 1285) (pool_swap_fix L hw hn 718 907 1285 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 1285) (L.core.poolWire 1285) (pool_swap_fix L hw hn 768 775 1285 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 1285) (L.core.poolWire 1285) (pool_swap_fix L hw hn 769 1539 1285 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 1285) (L.core.poolWire 1285) (pool_swap_fix L hw hn 1286 1538 1285 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 1537) (L.core.poolWire 1285) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 1537) (L.core.poolWire 1537) (pool_swap_fix L hw hn 770 1536 1537 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1537) (L.core.poolWire 1537) (pool_swap_fix L hw hn 767 1532 1537 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1537) (L.core.poolWire 1537) (pool_swap_fix L hw hn 765 1531 1537 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1537) (L.core.poolWire 1537) (pool_swap_fix L hw hn 766 1530 1537 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1537 (by simp))))))))))

private theorem free1286 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1286∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 1286) (L.core.poolWire 1286) (pool_swap_fix L hw hn 718 907 1286 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 1286) (L.core.poolWire 1286) (pool_swap_fix L hw hn 768 775 1286 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 1286) (L.core.poolWire 1286) (pool_swap_fix L hw hn 769 1539 1286 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 1538) (L.core.poolWire 1286) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 1538) (L.core.poolWire 1538) (pool_swap_fix L hw hn 1285 1537 1538 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 1538) (L.core.poolWire 1538) (pool_swap_fix L hw hn 770 1536 1538 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1538) (L.core.poolWire 1538) (pool_swap_fix L hw hn 767 1532 1538 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1538) (L.core.poolWire 1538) (pool_swap_fix L hw hn 765 1531 1538 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1538) (L.core.poolWire 1538) (pool_swap_fix L hw hn 766 1530 1538 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1538 (by simp))))))))))

private theorem free769 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 769∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 769) (L.core.poolWire 769) (pool_swap_fix L hw hn 718 907 769 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 769) (L.core.poolWire 769) (pool_swap_fix L hw hn 768 775 769 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 1539) (L.core.poolWire 769) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 1286 1538 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 1285 1537 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 770 1536 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 767 1532 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 765 1531 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 1539) (L.core.poolWire 1539) (pool_swap_fix L hw hn 766 1530 1539 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 1539 (by simp))))))))))

private theorem free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 768) (L.core.poolWire 768) (pool_swap_fix L hw hn 718 907 768 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 775) (L.core.poolWire 768) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 769 1539 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 1286 1538 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 1285 1537 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 770 1536 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 767 1532 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 765 1531 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 775) (L.core.poolWire 775) (pool_swap_fix L hw hn 766 1530 775 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial_free L hw hn 775 (by simp))))))))))

private theorem free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := by
  exact rename_free (Equiv.swap (L.core.poolWire 718) (L.core.poolWire 907)) _ (L.core.poolWire 907) (L.core.poolWire 718) (Equiv.swap_apply_right _ _)
    (rename_free (Equiv.swap (L.core.poolWire 768) (L.core.poolWire 775)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 768 775 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 769) (L.core.poolWire 1539)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 769 1539 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 1286 1538 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 1285 1537 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 770) (L.core.poolWire 1536)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 770 1536 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 767) (L.core.poolWire 1532)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 767 1532 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 765) (L.core.poolWire 1531)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 765 1531 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (rename_free (Equiv.swap (L.core.poolWire 766) (L.core.poolWire 1530)) _ (L.core.poolWire 907) (L.core.poolWire 907) (pool_swap_fix L hw hn 766 1530 907 (by omega) (by omega) (by omega) (by omega) (by omega))
    (initial907_free L hw hn)))))))))

theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := free768 L hw hn

theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := free718 L hw hn

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718]) :
    L.core.poolWire k∉wires (program L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact free1800 L hw hn
  · exact free766 L hw hn
  · exact free765 L hw hn
  · exact free767 L hw hn
  · exact free770 L hw hn
  · exact free1285 L hw hn
  · exact free1286 L hw hn
  · exact free769 L hw hn
  · exact free768 L hw hn
  · exact free718 L hw hn

end ECDSAAdd.Entrant.ControlLoan1589BFSquare
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ControlLoan1589BFFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589SumCleanupFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589BFSquare

/-! BF point adapter. The point correction uses the BF square offset K.
The V142 field kernels, control loans and point wrapper remain unchanged.
The generic point proof follows the retained All12Generic proof with this
explicit offset. The BF arithmetic source credit is in BFFoldCore/BFFold.
-/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch

abbrev K : Nat := ControlLoan1589BFSquare.K

/-- The correction cancels the actual BF square offset. -/
def generic (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ D (-cy) ++
  S ++ fastConstAdd L L.point.x (3*cx-(K : Nat)) ++
  P ++ exitY L cy ++ fastConstNeg L cx

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
variable (D : Fp→Program) (S P : Program) (halfCorrect : HalfMultiplyCorrect L P)
variable (divisionCorrect : ∀(X Y k : Fp)(G : Bool)(origin : BasisState),X≠0 →
  Triple (PointDialogValues L X Y G origin) (D k)
    (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin))
variable (squareCorrect : ∀(X Y : Fp)(G : Bool)(origin : BasisState),
  Triple (PointDialogValues L X Y G origin) S
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K : Fp) else 0)) Y G origin))
include hw hn halfCorrect divisionCorrect squareCorrect
attribute [local irreducible] run arithS fastConstAdd fastConstNeg fastConstRefl exitY

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L D S P cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true origin (-cx)
  simp only [if_true,←sub_eq_add_neg] at h1
  have h2 := divisionCorrect
    (X-cx) Y (-cy) true origin (sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,←sub_eq_add_neg,ha] at h2
  have h3 := squareCorrect (X-cx) a true origin
  simp only [if_true] at h3
  have h4 := fastStep_addX L hw hn ((X-cx)-a*a+(K : Nat)) a true origin (3*cx-(K : Nat))
  simp only [if_true] at h4
  have hd4 : ((X-cx)-a*a+(K : Nat))+(3*cx-(K : Nat))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd4] at h4
  have h5 := fusedMultiply_step L hw hn P halfCorrect d a cy true origin hd
  simp only [if_true] at h5
  have h6 := fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at h6
  rw [show cx-d=genericX X Y cx cy by dsimp [d]; ring] at h6
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h5 h6
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [generic,fusedMultiply,List.append_assoc] using h

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L D S P cx cy)
      (PointDialogValues L X Y false origin) := by
  have h1 := fastStep_addX L hw hn X Y false origin (-cx)
  have h2 := divisionCorrect
    X Y (-cy) false origin hX
  have h3 := squareCorrect X (Y/X) false origin
  have h4 := fastStep_addX L hw hn X (Y/X) false origin (3*cx-(K : Nat))
  have h5 := fusedMultiply_step L hw hn P halfCorrect X (Y/X) cy false origin hX
  have h6 := fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y := div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,Nat.cast_zero,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6
  rw [back] at h5
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [generic,fusedMultiply,List.append_assoc] using h
end Correct
end ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset

namespace ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch
attribute [local irreducible] run wires generic
def mid (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  clrF L ++ renameProgram (swapF L) (generic L D S P cx cy) ++ clrF L

def gen (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  zrep L ++ mid L D S P cx cy ++ zrep L

section WrapCorrect
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
variable (D : Fp→Program) (S P : Program) (halfCorrect : HalfMultiplyCorrect L P)
variable (divisionCorrect : ∀(X Y k : Fp)(G : Bool)(origin : BasisState),X≠0 →
  Triple (PointDialogValues L X Y G origin) (D k)
    (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin))
variable (squareCorrect : ∀(X Y : Fp)(G : Bool)(origin : BasisState),
  Triple (PointDialogValues L X Y G origin) S
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K : Fp) else 0)) Y G origin))
include hw hn

theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L D S P cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L D S P cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L D S P cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


include halfCorrect divisionCorrect squareCorrect

theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L D S P cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn D S P cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn D S P halfCorrect divisionCorrect squareCorrect 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn D S P cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn D S P halfCorrect divisionCorrect squareCorrect x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn D S P cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn D S P halfCorrect divisionCorrect squareCorrect x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


end WrapCorrect
end ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset

namespace ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch
attribute [local irreducible] wires run generic gen mid fastConstAdd fastConstNeg exitY

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (D : Fp→Program) (S P : Program)
    (hD : ∀k,wires (D k)⊆(OB5Support.sites L).toFinset)
    (hS : wires S⊆(OB5Support.sites L).toFinset)
    (hP : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
    wires (generic L D S P cx cy)⊆(OB5Support.sites L).toFinset := by
  have ca : wires (fastConstAdd L L.point.x (-cx)) ⊆ (OB5Support.sites L).toFinset := (All12Generic.add_palette L hw (-cx)).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstAdd L L.point.x (3*cx-(K : Nat))) ⊆ (OB5Support.sites L).toFinset := (All12Generic.add_palette L hw (3*cx-(K : Nat))).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have cn : wires (fastConstNeg L cx) ⊆ (OB5Support.sites L).toFinset := (All12Generic.neg_palette L hw cx).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have ey := (exitY_support L hw cy).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  simp only [generic,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨ca,hD (-cy)⟩,hS⟩,cr⟩,hP⟩,ey⟩,cn⟩

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (hD : ∀k,GatePhysical (D k))
    (hS : GatePhysical S) (hP : GatePhysical P) (cx cy : Fp) :
    GatePhysical (generic L D S P cx cy) := by
  have ca := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c (-cx).val
  have cr := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c (3*cx-(K : Nat)).val
  have cn := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have ey := exitY_physical L hw hn cy
  simp only [generic,fastConstAdd,fastConstNeg,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ca,hD (-cy)⟩,hS⟩,cr⟩,hP⟩,ey⟩,cn⟩


theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (k : Nat) (hk : 515≤k ∧ k<2613)
    (hD : ∀c,L.core.poolWire k∉wires (D c))
    (hS : L.core.poolWire k∉wires S) (hP : L.core.poolWire k∉wires P)
    (cx cy : Fp) : L.core.poolWire k∉wires (generic L D S P cx cy) := by
  have x := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.x (Or.inl rfl)
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.y (Or.inr rfl)
  have ca := (All12Generic.add_palette L hw (-cx))
  have cr := (All12Generic.add_palette L hw (3*cx-(K : Nat)))
  have cn := (All12Generic.neg_palette L hw cx)
  have ey := exitY_support L hw cy
  simp only [generic,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨fun h=>x (ca h),hD (-cy)⟩,hS⟩,fun h=>x (cr h)⟩,hP⟩,
    fun h=>y (ey h)⟩,fun h=>x (cn h)⟩

theorem gen_shape (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) :
    gen L D S P cx cy=GenericQ5Geometry.wrapG L (generic L D S P cx cy) := by
  simp only [gen,mid,GenericQ5Geometry.wrapG]


theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (hD : ∀k,GatePhysical (D k))
    (hS : GatePhysical S) (hP : GatePhysical P) (cx cy : Fp) :
    GatePhysical (gen L D S P cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have r:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (generic_physical L hw hn D S P hD hS hP cx cy)
  simp only [gen,mid,gatePhysical_append]
  exact ⟨⟨z,⟨c,r⟩,c⟩,z⟩


end ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset

namespace ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] fastConstAdd fastConstNeg exitY

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp→Program) (S P : Program)
    (ds : ∀k,gateSlots (D k)≤20528830) (ss : gateSlots S≤8000000)
    (ps : gateSlots P≤20503830) (cx cy : Fp) :
    gateSlots (gen L D S P cx cy)≤49207648 := by
  have add (k : Fp) : gateSlots (fastConstAdd L L.point.x k)≤15368 := by
    simpa only [fastConstAdd] using FastConst.fastAdd_gateSlots_le
      (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have neg : gateSlots (fastConstNeg L cx)≤17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a:=add (-cx)
  have b:=add (3*cx-(K : Nat))
  have d:=ds (-cy)
  have e:=exitY_slots L hw cy
  have z:=zrep_gateSlots_le L hw
  have c:=clrF_gateSlots_le L hw
  simp only [gen,mid,generic,
    gateSlots_append,rename_gateSlots]
  omega

end ECDSAAdd.Entrant.ControlLoan1589BFFinal.Offset

namespace ECDSAAdd.Entrant.ControlLoan1589BFFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  Offset.gen L (division ControlLoan1589.entryKernel L)
    (ControlLoan1589BFSquare.program L) (exit ControlLoan1589.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+846=toffoliCount Q ∧ measurementCount P+849=measurementCount Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp→Program) (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy)
    (hG0 : G0=All12Generic.gen L D Old P cx cy) (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  have fresh:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(Offset.K : Nat))
  have old:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(2^163-1 : Nat))
  simp only [Metrics,Offset.gen,Offset.mid,Offset.generic,All12Generic.gen,
    All12Generic.mid,All12Generic.generic,toffoliCount_append,measurementCount_append,
    renameProgram_counts] at hs ⊢
  exact ⟨by omega,by omega⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Old : Program) (h : Metrics P Old) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Old) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,renameProgram_counts] at h ⊢
  exact ⟨by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (ControlLoan1589SumCleanupFinal.gen L cx cy) := by
  have fresh:=ControlLoan1589BFSquare.counts_diff L hw
  have old:=ControlLoan1589SumCleanupSquare.counts_eq_base L
  have square : Metrics (ControlLoan1589BFSquare.program L)
      (ControlLoan1589SumCleanupSquare.program L) := ⟨by omega,by omega⟩
  exact gen_metrics_of_shapes L hw (division ControlLoan1589.entryKernel L)
    (ControlLoan1589BFSquare.program L) (ControlLoan1589SumCleanupSquare.program L)
    (exit ControlLoan1589.exitKernel L) (gen L cx cy) (ControlLoan1589SumCleanupFinal.gen L cx cy)
    cx cy (by unfold gen; rfl) (by unfold ControlLoan1589SumCleanupFinal.gen; rfl) square

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+846=toffoliCount (ControlLoan1589SumCleanupFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+849=measurementCount (ControlLoan1589SumCleanupFinal.gen L cx cy) :=
  gen_metrics L hw cx cy

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact Offset.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct ControlLoan1589.exitKernel
      ControlLoan1589.exitKernel_support ControlLoan1589.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step ControlLoan1589.entryKernel
      ControlLoan1589.entryKernel_support ControlLoan1589.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (ControlLoan1589BFSquare.step L hw hn) hc

theorem generic_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (Offset.generic L (division ControlLoan1589.entryKernel L)
      (ControlLoan1589BFSquare.program L) (exit ControlLoan1589.exitKernel L) cx cy)⊆
      (OB5Support.sites L).toFinset :=
  Offset.generic_sites L hw _ _ _
    (division_support ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support L hw)
    (ControlLoan1589BFSquare.support L hw hn)
    (exit_support ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support L hw) cx cy

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  unfold gen
  rw [Offset.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_support L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Offset.gen_physical L hw hn _ _ _
    (division_physical ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_physical L hw hn)
    (ControlLoan1589BFSquare.physical L hw hn)
    (placed_physical ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_physical L hw hn) cx cy

private theorem division_slots_bound (K : Program) (ks : gateSlots K≤20503830)
    (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    gateSlots (division K L k)≤20528830 := by
  have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  simp only [division,FrontierEntry1591Callers.entry,EntryFuse.fusedY,
    gateSlots_append,rename_gateSlots]
  omega

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤49207648 :=
  Offset.gen_slots L hw _ _ _
    (division_slots_bound ControlLoan1589.entryKernel ControlLoan1589.entryKernel_slots L hw)
    (ControlLoan1589BFSquare.slots L hw)
    (by simpa only [exit,rename_gateSlots] using ControlLoan1589.exitKernel_slots) cx cy

private theorem logical718 : base 718∈OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨718,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  omega

private theorem placed718 (K : Program) (ks : wires K⊆OB5Support.logicalSites)
    (kf : base 718∉wires K) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (renameProgram (wireFn2 L) K) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,oldUsed,eq⟩:=Finset.mem_image.mp used
  have mapped : wireFn2 L old=wireFn2 L (base 718) := by
    simpa only [show wireFn2 L (base 718)=L.core.poolWire 718 from rfl] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (ks oldUsed)) (base 718)
    (ArithmeticOB5.logical_sub_old logical718) mapped
  exact kf (back ▸ oldUsed)

private theorem division718 (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (c : Fp) :
    L.core.poolWire 718∉wires (division ControlLoan1589.entryKernel L c) := by
  have constant:=ExitGenericQ5.constant_ports_avoid_large L hw hn 718 (by omega) L.point.y (Or.inr rfl)
  simp only [division,FrontierEntry1591Callers.entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun used=>constant (EntryFuse.fusedY_support L hw c used),
    placed718 ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_718_free L hw hn⟩

private theorem square_old_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈Q1591Resources.genericOmissions) :
    L.core.poolWire k∉wires (ControlLoan1589BFSquare.program L) := by
  apply ControlLoan1589BFSquare.square_free L hw hn k
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
  tauto

private theorem gen_with_qubits (D : Fp→Program) (S P : Program)
    (ds : ∀k,wires (D k)⊆(OB5Support.sites layout).toFinset)
    (ss : wires S⊆(OB5Support.sites layout).toFinset)
    (ps : wires P⊆(OB5Support.sites layout).toFinset)
    (df : ∀c k,k∈Q1591Resources.genericOmissions→layout.core.poolWire k∉wires (D c))
    (sf : ∀k,k∈Q1591Resources.genericOmissions→layout.core.poolWire k∉wires S)
    (pf : ∀k,k∈Q1591Resources.genericOmissions→layout.core.poolWire k∉wires P)
    (d768 : ∀c,layout.core.poolWire 768∉wires (D c))
    (s768 : layout.core.poolWire 768∉wires S) (p768 : layout.core.poolWire 768∉wires P)
    (d718 : ∀c,layout.core.poolWire 718∉wires (D c))
    (s718 : layout.core.poolWire 718∉wires S) (p718 : layout.core.poolWire 718∉wires P)
    (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (Offset.gen layout D S P cx cy))≤1589 := by
  rw [Offset.gen_shape]
  apply ControlLoan1589Inventory.edges_wrapG_qubits _
    (Offset.generic_sites layout layout_widths D S P ds ss ps cx cy) _
    (Offset.generic_free layout layout_widths layout_nodup D S P 768 (by omega)
      d768 s768 p768 cx cy)
    (Offset.generic_free layout layout_widths layout_nodup D S P 718 (by omega)
      d718 s718 p718 cx cy) C cy
  intro k hk
  have bounds : 515≤k ∧ k<2613 := by
    simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  exact Offset.generic_free layout layout_widths layout_nodup D S P k bounds
    (fun c=>df c k hk) (sf k hk) (pf k hk) cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1589 := by
  unfold gen
  exact gen_with_qubits
    (division ControlLoan1589.entryKernel layout) (ControlLoan1589BFSquare.program layout)
    (exit ControlLoan1589.exitKernel layout)
    (division_support ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support layout layout_widths)
    (ControlLoan1589BFSquare.support layout layout_widths layout_nodup)
    (exit_support ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support layout layout_widths)
    (division_free ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_free layout layout_widths layout_nodup)
    (square_old_free layout layout_widths layout_nodup)
    (placed_omissions ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_free layout layout_widths layout_nodup)
    (Prefix1590Point.division_768_free ControlLoan1589.entryKernel ControlLoan1589.entryKernel_support
      ControlLoan1589.entryKernel_768_free layout layout_widths layout_nodup)
    (ControlLoan1589BFSquare.retired_free768 layout layout_widths layout_nodup)
    (Prefix1590Point.placed_768_free ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_768_free layout layout_widths layout_nodup)
    (division718 layout layout_widths layout_nodup)
    (ControlLoan1589BFSquare.retired_free718 layout layout_widths layout_nodup)
    (placed718 ControlLoan1589.exitKernel ControlLoan1589.exitKernel_support
      ControlLoan1589.exitKernel_718_free layout layout_widths layout_nodup) C cx cy

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2153597 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=ControlLoan1589SumCleanupFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499723 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2
  have old:=ControlLoan1589SumCleanupFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50007652 := by
  have generic:=gen_slots layout layout_widths cx cy
  have outer:=Edges.wrapper_slots layout layout_widths C cy (gen layout cx cy)
  omega

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2153597,1499723,1589,50007652⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2153597 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499723 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1589 := by
  cases C with
  | zero => change qubits []≤1589;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50007652 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499723
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1589
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50007652
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.ControlLoan1589BFFinal
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Main =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ControlLoan1589BFFinal

namespace ECDSAAdd.Entrant

def program := ControlLoan1589BFFinal.program
def entry := ControlLoan1589BFFinal.entry
def bounds := ControlLoan1589BFFinal.bounds

theorem certificate : Challenge.Certificate entry bounds := ControlLoan1589BFFinal.certificate

end ECDSAAdd.Entrant
end -- original module boundary
