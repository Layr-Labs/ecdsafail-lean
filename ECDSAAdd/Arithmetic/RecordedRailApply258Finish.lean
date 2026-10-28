import ECDSAAdd.Arithmetic.RecordedRailApply258FinishProof

set_option maxRecDepth 4096
set_option exponentiation.threshold 512
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer

/-- The complete original 258-bit arrays split into a 224-bit prefix and the
real 34-bit final word. No data or sign bit is discarded. -/
theorem final_ready (a b bank : List Wire) (cin even odd : Wire)
    (original : BasisState) (s : State) (ready : Ready a b bank cin even odd original)
    (state : PrefixState a b (bank.take 31) cin even odd original s 7) :
    PrefixWrappedReady (a.take 224) (b.take 224) (a.drop 224) (b.drop 224)
      bank cin even odd original s := by
  obtain ⟨aw,bw,bankWidth,nd,originalClean,evenZero,oddZero⟩ := ready
  obtain ⟨wide,outside,_,oddClean⟩ := state
  have reordered : (([cin]++a++b++[even,odd])++bank).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have dis := (List.nodup_append'.mp reordered).2.2
  have cleanAll : ∀q∈bank,s.basis q=false := by
    intro q hq
    have away : q∉b.take 224++[even] := by
      intro ht
      have member : q∈[cin]++a++b++[even,odd] := by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht ⊢
        rcases ht with hb | he
        · have hbin : q∈b := List.mem_of_mem_take hb
          tauto
        · subst q; simp
      exact List.disjoint_left.mp dis member hq
    rw [outside q (by simpa using away)]
    exact originalClean q hq
  have fullND : ([cin,even,odd]++a.take 224++b.take 224++a.drop 224++b.drop 224++bank).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    have ac := congrArg (List.count q) (List.take_append_drop 224 a)
    have bc := congrArg (List.count q) (List.take_append_drop 224 b)
    simp only [List.count_append] at ac bc
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have positive : 0<(a.drop 224).length := by rw [tail_length a aw]; decide
  have widths : (b.drop 224).length=(a.drop 224).length := by rw [tail_length a aw,tail_length b bw]
  have workWidth : bank.length=(a.drop 224).length-2 := by rw [bankWidth,tail_length a aw]
  refine ⟨?_,positive,widths,workWidth,fullND,cleanAll,evenZero,?_,?_⟩
  · rw [pref_length a aw 7 (by decide),pref_length b bw 7 (by decide)]
  · simpa using wide
  · simpa using outside

theorem odd_outside (a b bank : List Wire) (cin even odd : Wire)
    (nd : ([cin]++a++b++bank++[even,odd]).Nodup) : odd∉b := by
  intro hb
  have h := List.nodup_iff_count.mp nd odd
  have positive := List.count_pos_iff.mpr hb
  simp only [List.count_cons,List.count_append,List.count_nil] at h
  simp only [beq_self_eq_true,if_true] at h
  omega

theorem last_prefix (a b bank : List Wire) (cin even odd : Wire)
    (original : BasisState) (s : State) (m : List Bool) (cursor : Nat)
    (ready : Ready a b bank cin even odd original)
    (state : PrefixState a b (bank.take 31) cin even odd original s 7) :
    let out := runWithTape (finish (a.drop 224) (b.drop 224) bank even) m cursor s
    out.phase=(s.phase ^^ (m.getD (cursor+32) false && prefixCarry a b cin original 224)) ∧
    regValue b out.basis=(regValue a original+regValue b original+(original cin).toNat)%2^258 ∧
    (∀q,q∉b → out.basis q=original q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis even=false ∧ out.basis odd=false := by
  have prep := final_ready a b bank cin even odd original s ready state
  have result := finish_prefix (a.take 224) (b.take 224) (a.drop 224) (b.drop 224)
    bank cin even odd original s m cursor prep
  obtain ⟨hp,hvalue,houtside,hbank,heven⟩ := result
  have aw := ready.1
  have bw := ready.2.1
  rw [tail_length a aw] at hp
  have cp : firstCarry (a.take 224) (b.take 224) cin original=prefixCarry a b cin original 224 := by
    simpa using carry_pref a b cin original 7 bw (by decide)
  rw [cp] at hp
  rw [List.take_append_drop,List.take_append_drop] at hvalue
  rw [List.take_append_drop] at houtside
  have prefixLen : (b.take 224).length=224 := by simpa using pref_length b bw 7 (by decide)
  rw [prefixLen,tail_length b bw] at hvalue
  have hodd := houtside odd (odd_outside a b bank cin even odd ready.2.2.2.1)
  dsimp only
  refine ⟨hp,hvalue,houtside,hbank,heven,?_⟩
  exact hodd.trans ready.2.2.2.2.2.2

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.last_prefix
