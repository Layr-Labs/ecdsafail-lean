import ECDSAAdd.Arithmetic.RecordedRailDeferFinishPrefix
import ECDSAAdd.Arithmetic.RecordedRailDeferResources

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

/-- Decomposing a prefix is a list identity, independent of quantum data. -/
theorem take_add_wire (r : List Wire) (n k : Nat) :
    r.take (n+k)=r.take n++(r.drop n).take k := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    cases r with
    | nil => simp
    | cons q qs => simpa only [Nat.succ_add,List.take_succ_cons,List.drop_succ_cons,
        List.cons_append] using congrArg (List.cons q) (ih qs)

theorem count_take_bound (r : List Wire) (n : Nat) (q : Wire) :
    (r.take n).count q ≤ r.count q := by
  have split := congrArg (List.count q) (List.take_append_drop n r)
  simp only [List.count_append] at split
  omega

theorem prefix_chunk (r : List Wire) (j : Nat) :
    r.take (32*j)++chunk r j=r.take (32*(j+1)) := by
  rw [show 32*(j+1)=32*j+32 from by omega,take_add_wire]
  rfl

theorem prefix_length (r : List Wire) (width : r.length=256) (j : Nat) (hj : j≤8) :
    (r.take (32*j)).length=32*j := by
  simp only [List.length_take,width]
  omega

/-- The two header roles may alternate, while every listed site remains real. -/
theorem prefix_layout (a b bank : List Wire) (cin even odd old next : Wire)
    (j : Nat) (nd : ([cin]++a++b++bank++[even,odd]).Nodup)
    (roles : old=even ∧ next=odd ∨ old=odd ∧ next=even) :
    ([cin,old,next]++a.take (32*j)++b.take (32*j)++chunk a j++chunk b j++bank).Nodup := by
  rcases roles with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    have ac := count_take_bound a (32*(j+1)) q
    have bc := count_take_bound b (32*(j+1)) q
    rw [←prefix_chunk a j,List.count_append] at ac
    rw [←prefix_chunk b j,List.count_append] at bc
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega

/-- Prefix invariant after an actual stream: one boundary remains live, and
all other sites outside the computed prefix match the original snapshot. -/
def PrefixState (a b bank : List Wire) (cin current spare : Wire)
    (original : BasisState) (s : State) (j : Nat) : Prop :=
  regValue (b.take (32*j)++[current]) s.basis=
    regValue (a.take (32*j)) original+regValue (b.take (32*j)) original+(original cin).toNat ∧
    (∀q,q∉b.take (32*j)++[current] → s.basis q=original q) ∧
    (∀q∈bank,s.basis q=false) ∧ s.basis spare=false

theorem prepare_prefix (a b bank : List Wire) (cin even odd old next : Wire)
    (original : BasisState) (s : State) (j : Nat) (hj : j<8)
    (ready : Ready32 a b bank cin even odd original)
    (roles : old=even ∧ next=odd ∨ old=odd ∧ next=even)
    (pref : PrefixState a b bank cin old next original s j) :
    PrefixReady (a.take (32*j)) (b.take (32*j)) (chunk a j) (chunk b j)
      bank cin old next original s := by
  obtain ⟨aw,bw,bankWidth,nd,_,evenZero,oddZero⟩ := ready
  obtain ⟨wide,outside,clean,nextZero⟩ := pref
  have al : RecordedRailVented.Aligned (chunk a j) (chunk b j) bank := by
    simp [RecordedRailVented.Aligned,chunk_length32 a aw j hj,
      chunk_length32 b bw j hj,bankWidth]
  refine ⟨?_,al,prefix_layout a b bank cin even odd old next j nd roles,clean,nextZero,?_,wide,outside⟩
  · rw [prefix_length a aw j (by omega),prefix_length b bw j (by omega)]
  · rcases roles with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact evenZero
    · exact oddZero

theorem carry_prefix (a b : List Wire) (cin : Wire) (original : BasisState)
    (j : Nat) (bw : b.length=256) (hj : j≤8) :
    firstCarry (a.take (32*j)) (b.take (32*j)) cin original=
      prefixCarry a b cin original (32*j) := by
  simp only [firstCarry,prefixCarry,prefix_length b bw j hj]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.prepare_prefix
