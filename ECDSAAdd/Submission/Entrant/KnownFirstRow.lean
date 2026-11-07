import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.SignedTriangularSquareProof

namespace ECDSAAdd.Entrant.KnownFirstRow
open Arithmetic

/-- The receiver needs only a specification of the ordinary adder's output. -/
theorem receive_of_output (bits sums : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (hn : (cin::(ys++carry)).Nodup)
    (ha : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hw : ∀q∈mappedWires sums,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false)
    (output : regValue ys (run (mappedAdd bits ys carry cin) [] s).basis =
      mappedValue sums s.basis) :
    run (KnownOutputAdder.program bits ys sums carry cin) m s =
      run (mappedAdd bits ys carry cin) m s := by
  have old := mappedAdd_correct bits ys carry cin hn ha hl hc s [] hclean
  have value : mappedValue sums s.basis =
      (mappedValue bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length :=
    output.symm.trans old.2.2
  exact KnownOutputAdder.program_eq_mappedAdd bits sums ys carry cin hn ha hw hl hs hc s m
    hclean (KnownOutputAdder.ready_of_value bits sums ys (s.basis cin) s.basis hl hs value)

/-- After a signed-row clear's adder, its low bits equal the original row control,
while its top bit is true. The first carry is handled outside this receiver. -/
def expected (control : Wire) (n : Nat) : List MappedBit :=
  List.replicate (n-1) ⟨some control,false⟩ ++ [⟨none,true⟩]

theorem expected_length (control : Wire) (n : Nat) (hn : 0<n) :
    (expected control n).length=n := by simp [expected]; omega

theorem expected_sources (control : Wire) (n : Nat) :
    ∀q∈mappedWires (expected control n),q=control := by
  intro q hq
  simp only [mappedWires,expected,List.flatMap_append,List.mem_append,List.flatMap_replicate,
    List.flatMap_cons,List.flatMap_nil,List.not_mem_nil,or_false] at hq
  simp_all

theorem expected_value (control top : Wire) (low : List Wire) (s : BasisState)
    (hlo : ∀q∈low,s q=s control) (ht : s top=true) :
    mappedValue (List.replicate low.length (⟨some control,false⟩ : MappedBit) ++ [⟨none,true⟩]) s =
      regValue (low++[top]) s := by
  induction low with
  | nil => simp [mappedValue,regValue,MappedBit.value,ht]
  | cons q low ih =>
    simp only [List.length_cons,List.replicate_succ,List.cons_append,mappedValue,regValue]
    rw [ih (fun q hq => hlo q (by simp [hq]))]
    cases hs : s control <;> simp [MappedBit.value,hlo q (by simp),hs,regValue,ht]

theorem post_recovers_bits (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : regValue (low++[top])
      (run (notRegister (low++[top]) ++ xorWhenFalse control low) [] s).basis=0) :
    (∀q∈low,s.basis q=s.basis control) ∧ s.basis top=true := by
  have hl : low.Nodup := (List.nodup_append.mp hn).1
  have ht : top∉low := by
    have h := (List.nodup_append.mp hn).2.2
    exact fun hq => h top hq top (by simp) rfl
  have hcl : control∉low := fun hq => hc (by simp [hq])
  simp only [run_append,List.take_nil,List.drop_nil] at hz
  rw [notRegister_correct _ hn, xorWhenFalse_correct control low hl hcl] at hz
  have bits := (regValue_zero _ _).mp hz
  constructor
  · intro q hq
    have e := bits q (by simp [hq])
    simp only [xorFalseBasis,if_pos hq,show q∈low++[top] from by simp [hq],if_pos,
      if_neg hc] at e
    have eq : ∀a b : Bool, (!a ^^ !b)=false → a=b := by decide
    exact eq _ _ e
  · have e := bits top (by simp)
    simp only [xorFalseBasis,if_neg ht,show top∈low++[top] from by simp,if_pos] at e
    simpa using e

theorem post_recovers_expected (control top : Wire) (low : List Wire) (s : State)
    (hn : (low++[top]).Nodup) (hc : control∉low++[top])
    (hz : regValue (low++[top])
      (run (notRegister (low++[top]) ++ xorWhenFalse control low) [] s).basis=0) :
    mappedValue (List.replicate low.length (⟨some control,false⟩ : MappedBit) ++ [⟨none,true⟩]) s.basis =
      regValue (low++[top]) s.basis := by
  have h := post_recovers_bits control top low s hn hc hz
  exact expected_value control top low s.basis h.1 h.2


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


theorem read_sources (xs : List Wire) : mappedWires (mappedRead xs false)=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [mappedRead,mappedWires] using congrArg (List.cons a) ih

def tailReceiver (xs ys carry : List Wire) (cin control : Wire) : Program :=
  KnownOutputAdder.program (mappedRead xs false) ys (expected control ys.length) carry cin

theorem tailReceiver_counts (xs ys carry : List Wire) (cin control : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (tailReceiver xs ys carry cin control)=0 ∧
    measurementCount (tailReceiver xs ys carry cin control)=ys.length-1 := by
  exact KnownOutputAdder.program_counts _ _ _ _ _ (by simpa [mappedRead] using hl)
    (expected_length _ _ (by omega)) hc

theorem tailReceiver_eq (xs ys carry : List Wire) (cin control : Wire)
    (hn : (cin::ys++carry).Nodup)
    (ha : ∀q∈xs,q∉cin::ys++carry)
    (hw : control∉cin::ys++carry)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (output : regValue ys (run (addInPlace xs ys carry cin) [] s).basis =
      mappedValue (expected control ys.length) s.basis) :
    run (tailReceiver xs ys carry cin control) m s = run (addInPlace xs ys carry cin) m s := by
  have source := read_sources xs
  have e := receive_of_output (mappedRead xs false) (expected control ys.length) ys carry cin hn
    (by simpa only [source] using ha)
    (fun q hq => (expected_sources control ys.length q hq) ▸ hw)
    (by simpa [mappedRead] using hl) (expected_length _ _ (by omega)) hc s m clean
    (by simpa only [read_add] using output)
  simpa only [tailReceiver,read_add] using e

def dropKnown (a b c control : Wire) (xs ys cs : List Wire) : Program :=
  [.CX a c] ++ tailReceiver xs ys cs c control ++ [.CX a c,.CX a b,.CX control b]

def dropOrdinary (a b c control : Wire) (xs ys cs : List Wire) : Program :=
  [.CX a c] ++ addInPlace xs ys cs c ++ [.CX a c,.CX a b,.CX control b]

theorem dropKnown_counts (a b c control : Wire) (xs ys cs : List Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    toffoliCount (dropKnown a b c control xs ys cs)=0 ∧
    measurementCount (dropKnown a b c control xs ys cs)=
      measurementCount (dropOrdinary a b c control xs ys cs) := by
  have kn := tailReceiver_counts xs ys cs c control hl hc
  have old := addInPlace_counts xs ys cs c hl hc
  simp only [dropKnown,dropOrdinary,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,kn.1,kn.2,old.2]
  trivial

theorem dropKnown_eq (a b c control : Wire) (xs ys cs : List Wire)
    (hn : (c::ys++cs).Nodup) (ha : ∀q∈xs,q∉c::ys++cs)
    (hw : control∉c::ys++cs) (hl : xs.length=ys.length) (hc : cs.length+1=ys.length)
    (s : State) (m : List Bool)
    (clean : ∀q∈cs,(run [.CX a c] [] s).basis q=false)
    (output : regValue ys (run (addInPlace xs ys cs c) [] (run [.CX a c] [] s)).basis =
      mappedValue (expected control ys.length) (run [.CX a c] [] s).basis) :
    run (dropKnown a b c control xs ys cs) m s =
      run (dropOrdinary a b c control xs ys cs) m s := by
  have e := tailReceiver_eq xs ys cs c control hn ha hw hl hc
    (run [.CX a c] [] s) (m.take (ys.length-1)) clean output
  have kn := (tailReceiver_counts xs ys cs c control hl hc).2
  have old := (addInPlace_counts xs ys cs c hl hc).2
  simp only [dropKnown,dropOrdinary,run_append,measurementCount_append,
    measurementCount,kn,old,List.take_zero,List.drop_zero,Nat.zero_add]
  rw [e]


def rowPost (control : Wire) (low : List Wire) (top : Wire) : Program :=
  notRegister (low++[top]) ++ xorWhenFalse control low

theorem dropKnown_post_eq (a b c control top : Wire) (xs low cs : List Wire)
    (hn : (c::(low++[top])++cs).Nodup)
    (ha : ∀q∈xs,q∉c::(low++[top])++cs)
    (hw : control∉c::(low++[top])++cs)
    (hb : b∉low++[top]) (hbc : control≠b)
    (hd : (b::low++[top]).Nodup)
    (hl : xs.length=(low++[top]).length) (hc : cs.length+1=(low++[top]).length)
    (s : State) (m : List Bool)
    (clean : ∀q∈cs,(run [.CX a c] [] s).basis q=false)
    (zero : regValue (b::low++[top])
      (run (dropOrdinary a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) [] s).basis=0) :
    run (dropKnown a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) m s =
    run (dropOrdinary a b c control xs (low++[top]) cs ++ rowPost control (b::low) top) m s := by
  let u := run [.CX a c] [] s
  let t := run (addInPlace xs (low++[top]) cs c) [] u
  let finish : Program := [.CX a c,.CX a b,.CX control b]
  let v := run finish [] t
  have cv : control≠c := fun e => hw (by simp [e])
  have used (q : Wire) (hq : q∈low++[top]) : q∈c::(low++[top])++cs :=
    List.mem_append_left cs (List.mem_cons_of_mem c hq)
  have out : ∀q∈low++[top],q≠c := by
    intro q hq eq
    subst q
    exact (List.nodup_cons.mp hn).1 (List.mem_append_left cs hq)
  have kept (q : Wire) (hq : q≠c ∧ q≠b) : v.basis q=t.basis q := by
    simp [v,finish,run,writeBit,hq.1,hq.2]
  have vctl : v.basis control=t.basis control := kept control ⟨cv,hbc⟩
  have z : regValue ((b::low)++[top]) (run (rowPost control (b::low) top) [] v).basis=0 := by
    rw [run_append] at zero
    simp only [List.take_nil,List.drop_nil] at zero
    unfold dropOrdinary at zero
    rw [run_append,run_append] at zero
    simpa only [List.take_nil,List.drop_nil,u,t,finish,v,List.cons_append] using zero
  have controlAway : control∉(b::low)++[top] := by
    intro hq
    rcases List.mem_cons.mp hq with eq | hq
    · exact hbc eq
    · exact hw (used control hq)
  have recov := post_recovers_bits control top (b::low) v hd controlAway z
  have lo : ∀q∈low,t.basis q=t.basis control := by
    intro q hq
    rw [←kept q ⟨out q (by simp [hq]),fun e => hb (by simp [←e,hq])⟩,←vctl]
    exact recov.1 q (by simp [hq])
  have topTrue : t.basis top=true := by
    rw [←kept top ⟨out top (by simp),fun e => hb (by simp [←e])⟩]
    exact recov.2
  have expectedOut := expected_value control top low t.basis lo topTrue
  have stable : t.basis control=u.basis control := by
    have keep := (mappedAdd_correct (mappedRead xs false) (low++[top]) cs c hn
      (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc u [] clean).2.1
      control (fun hq => hw (used control hq))
    simpa only [read_add] using keep
  have value : regValue (low++[top]) t.basis =
      mappedValue (expected control (low++[top]).length) u.basis := by
    calc
      _ = mappedValue (expected control (low++[top]).length) t.basis := by
        simpa only [expected,List.length_append,List.length_singleton,Nat.add_sub_cancel] using expectedOut.symm
      _ = _ := mappedValue_congr _ _ _ (fun q hq => by
        rw [expected_sources control _ q hq]; exact stable)
  have eq (r : List Bool) := dropKnown_eq a b c control xs (low++[top]) cs hn ha hw hl hc s r clean value
  have mc := (dropKnown_counts a b c control xs (low++[top]) cs hl hc).2
  simp only [run_append]
  rw [mc,eq]


theorem first_copy_of_known_output (a a' b b' cin : Wire) (xs ys carry : List Wire)
    (hn : (cin::(b::b'::ys)++carry).Nodup)
    (ha : ∀q∈a::a'::xs,q∉cin::(b::b'::ys)++carry)
    (hl : (a::a'::xs).length=(b::b'::ys).length)
    (hc : carry.length+1=(b::b'::ys).length)
    (s : State) (clean : ∀q∈carry,s.basis q=false)
    (output : regValue (b::b'::ys) (run (addInPlace (a::a'::xs) (b::b'::ys) carry cin) [] s).basis =
      mappedValue (expected cin (b::b'::ys).length) s.basis) :
    ((s.basis b ^^ s.basis a) && (s.basis cin ^^ s.basis a))=false := by
  have old := mappedAdd_correct (mappedRead (a::a'::xs) false) (b::b'::ys) carry cin hn
    (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc s [] clean
  have ready := KnownOutputAdder.ready_of_value (mappedRead (a::a'::xs) false)
    (expected cin (b::b'::ys).length) (b::b'::ys) (s.basis cin) s.basis
    (by simpa [mappedRead] using hl) (expected_length _ _ (by simp))
    ((by simpa only [read_add] using output.symm.trans (by simpa only [read_add] using old.2.2)))
  simp only [KnownOutputAdder.Ready,expected,List.length_cons,Nat.succ_sub_succ_eq_sub,
    Nat.sub_zero,List.replicate_succ,List.cons_append,List.map_cons,mappedRead,
    KnownOutputAdder.sumBits] at ready
  have head := (List.cons.inj ready).1
  simp only [MappedBit.value,Option.map_some,Option.getD_some,Bool.false_xor] at head
  have eq : ∀x y z : Bool,z=sumBit x y z → x=y := by decide
  have same := eq _ _ _ head
  rw [same]
  simp


theorem tailReceiver_physical (xs ys carry : List Wire) (cin control : Wire)
    (hn : (cin::ys++carry).Nodup)
    (ha : ∀q∈xs,q∉cin::ys++carry) (hw : control∉cin::ys++carry)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    GatePhysical (tailReceiver xs ys carry cin control) := by
  apply KnownOutputAdder.program_physical _ _ _ _ _
    (by simpa [mappedRead] using hl) (expected_length _ _ (by omega)) hc hn
  · intro b hb q hq
    apply ha q
    rw [←read_sources xs]
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,by simpa using hq⟩
  · intro b hb q hq
    have mem : q∈mappedWires (expected control ys.length) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [expected_sources control _ q mem]
    exact hw

theorem tailReceiver_support (xs ys carry : List Wire) (cin control : Wire) :
    wires (tailReceiver xs ys carry cin control) ⊆ (xs++[control]++ys++carry++[cin]).toFinset := by
  intro q hq
  have sup := KnownOutputAdder.program_support (mappedRead xs false) (expected control ys.length) ys
    carry cin hq
  by_contra away
  have neq : q≠control := fun eq => away (by simp [eq])
  have notWitness : q∉mappedWires (expected control ys.length) :=
    fun mem => neq (expected_sources control _ q mem)
  simp only [read_sources,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup away
  tauto


theorem adder_output_from_post_zero (xs low carry : List Wire) (top control : Wire)
    (hn : (control::(low++[top])++carry).Nodup)
    (ha : ∀q∈xs,q∉control::(low++[top])++carry)
    (hl : xs.length=(low++[top]).length) (hc : carry.length+1=(low++[top]).length)
    (s : State) (clean : ∀q∈carry,s.basis q=false)
    (zero : regValue (low++[top])
      (run (addInPlace xs (low++[top]) carry control ++ rowPost control low top) [] s).basis=0) :
    regValue (low++[top]) (run (addInPlace xs (low++[top]) carry control) [] s).basis =
      mappedValue (expected control (low++[top]).length) s.basis := by
  let t := run (addInPlace xs (low++[top]) carry control) [] s
  have hd : (low++[top]).Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  have away : control∉low++[top] := fun mem =>
    (List.nodup_cons.mp hn).1 (List.mem_append_left carry mem)
  rw [run_append] at zero
  simp only [List.take_nil,List.drop_nil] at zero
  have result := post_recovers_expected control top low t hd away zero
  have old := mappedAdd_correct (mappedRead xs false) (low++[top]) carry control hn
    (by simpa only [read_sources] using ha) (by simpa [mappedRead] using hl) hc s [] clean
  have stable : t.basis control=s.basis control := by
    simpa only [read_add] using old.2.1 control away
  calc
    _ = mappedValue (expected control (low++[top]).length) t.basis := by
      simpa only [expected,List.length_append,List.length_singleton,Nat.add_sub_cancel] using result.symm
    _ = _ := mappedValue_congr _ _ _ (fun q hq => by
      rw [expected_sources control _ q hq]; exact stable)


theorem tailReceiver_support_old (xs ys carry : List Wire) (cin control : Wire)
    (hl : xs.length=ys.length) (hc : carry.length+1=ys.length) :
    wires (tailReceiver xs ys carry cin control) ⊆ wires (addInPlace xs ys carry cin) ∪ {control} := by
  intro q hq
  have h := tailReceiver_support xs ys carry cin control hq
  rw [addInPlace_wires xs ys carry cin hl hc]
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_union,Finset.mem_singleton] at h ⊢
  tauto

theorem dropKnown_support (a b c control : Wire) (xs ys cs : List Wire)
    (hl : xs.length=ys.length) (hc : cs.length+1=ys.length) :
    wires (dropKnown a b c control xs ys cs) ⊆ wires (dropOrdinary a b c control xs ys cs) := by
  have ctl : control∈wires (dropOrdinary a b c control xs ys cs) := by
    simp [dropOrdinary,wires_append,wires,Instr.wires]
  intro q hq
  simp only [dropKnown,wires_append,Finset.mem_union] at hq
  simp only [dropOrdinary,wires_append]
  rcases hq with (pre | mid) | post
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ pre)
  · rcases Finset.mem_union.mp (tailReceiver_support_old xs ys cs c control hl hc mid) with old | eq
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ old)
    · have e := Finset.mem_singleton.mp eq
      rw [e]
      simpa only [dropOrdinary,wires_append] using ctl
  · exact Finset.mem_union_right _ post

theorem dropKnown_physical (a b c control : Wire) (xs ys cs : List Wire)
    (hn : (c::ys++cs).Nodup) (ha : ∀q∈xs,q∉c::ys++cs)
    (hw : control∉c::ys++cs) (hl : xs.length=ys.length) (hc : cs.length+1=ys.length)
    (old : GatePhysical (dropOrdinary a b c control xs ys cs)) :
    GatePhysical (dropKnown a b c control xs ys cs) := by
  simp only [dropOrdinary,gatePhysical_append] at old
  simp only [dropKnown,gatePhysical_append]
  exact ⟨⟨old.1.1,tailReceiver_physical xs ys cs c control hn ha hw hl hc⟩,old.2⟩

end ECDSAAdd.Entrant.KnownFirstRow

#print axioms ECDSAAdd.Entrant.KnownFirstRow.dropKnown_post_eq
#print axioms ECDSAAdd.Entrant.KnownFirstRow.tailReceiver_eq
#print axioms ECDSAAdd.Entrant.KnownFirstRow.first_copy_of_known_output
