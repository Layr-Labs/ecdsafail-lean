import ECDSAAdd.Arithmetic.RecordedRailApply258Program
import ECDSAAdd.Arithmetic.RecordedRailDeferPrefixStep

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer

theorem chunk_length (r : List Wire) (width : r.length=258) (j : Nat) (hj : j<7) :
    (chunk r j).length=32 := by
  simp only [chunk,List.length_take,List.length_drop,width]
  omega

theorem tail_length (r : List Wire) (width : r.length=258) : (r.drop 224).length=34 := by
  simp [width]

theorem pref_length (r : List Wire) (width : r.length=258) (j : Nat) (hj : j≤7) :
    (r.take (32*j)).length=32*j := by
  simp only [List.length_take,width]
  omega

theorem prefix_layout (a b bank : List Wire) (cin even odd old next : Wire)
    (j : Nat) (nd : ([cin]++a++b++bank++[even,odd]).Nodup)
    (roles : old=even ∧ next=odd ∨ old=odd ∧ next=even) :
    ([cin,old,next]++a.take (32*j)++b.take (32*j)++chunk a j++chunk b j++bank.take 31).Nodup := by
  rcases roles with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    have ac := count_take_bound a (32*(j+1)) q
    have bc := count_take_bound b (32*(j+1)) q
    have work := count_take_bound bank 31 q
    rw [←prefix_chunk a j,List.count_append] at ac
    rw [←prefix_chunk b j,List.count_append] at bc
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega

theorem prepare_middle (a b bank : List Wire) (cin even odd old next : Wire)
    (original : BasisState) (s : State) (j : Nat) (hj : j<7)
    (ready : Ready a b bank cin even odd original)
    (roles : old=even ∧ next=odd ∨ old=odd ∧ next=even)
    (pref : PrefixState a b (bank.take 31) cin old next original s j) :
    PrefixReady (a.take (32*j)) (b.take (32*j)) (chunk a j) (chunk b j)
      (bank.take 31) cin old next original s := by
  obtain ⟨aw,bw,bankWidth,nd,_,evenZero,oddZero⟩ := ready
  obtain ⟨wide,outside,clean,nextZero⟩ := pref
  have al : RecordedRailVented.Aligned (chunk a j) (chunk b j) (bank.take 31) := by
    simp [RecordedRailVented.Aligned,chunk_length a aw j hj,chunk_length b bw j hj,bankWidth]
  refine ⟨?_,al,prefix_layout a b bank cin even odd old next j nd roles,clean,nextZero,?_,wide,outside⟩
  · rw [pref_length a aw j (by omega),pref_length b bw j (by omega)]
  · rcases roles with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact evenZero
    · exact oddZero

theorem carry_pref (a b : List Wire) (cin : Wire) (original : BasisState)
    (j : Nat) (bw : b.length=258) (hj : j≤7) :
    firstCarry (a.take (32*j)) (b.take (32*j)) cin original=prefixCarry a b cin original (32*j) := by
  simp only [firstCarry,prefixCarry,pref_length b bw j hj]

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.prepare_middle
