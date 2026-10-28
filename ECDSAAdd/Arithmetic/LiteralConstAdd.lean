import ECDSAAdd.Arithmetic.LiteralConstAddCells

set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

/-- In-place literal addition with arbitrary quantum carry-in. Carries are
computed from updated low bits, then independently measured in reverse order.
One is a single clean flag, not a materialized constant register. -/
def literalConstAdd : List Wire → List Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,one,k =>
      literalConstStep (decide (k%2=1)) x cin c ++
        literalConstAdd (x'::xs) cs c one (k/2) ++
        literalConstErase (decide (k%2=1)) x cin c one
  | [x],_,cin,_,k => literalConstSum (decide (k%2=1)) x cin
  | _,_,_,_,_ => []

theorem literalConstAdd_counts (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hc : carry.length+1=xs.length) :
    toffoliCount (literalConstAdd xs carry cin one k)=xs.length-1 ∧
    measurementCount (literalConstAdd xs carry cin one k)=xs.length-1 := by
  induction xs generalizing carry cin k with
  | nil => simp at hc
  | cons x xs ih =>
    cases xs with
    | nil =>
      have h := literalConstCell_counts (decide (k%2=1)) x cin cin one
      simpa [literalConstAdd] using And.intro h.2.2.2.2.1 h.2.2.2.2.2
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := literalConstCell_counts (decide (k%2=1)) x cin c one
        have hh := ih cs c (k/2) (by simpa using hc)
        simp [literalConstAdd,toffoliCount_append,measurementCount_append,
          h.1,h.2.1,h.2.2.1,h.2.2.2.1,hh.1,hh.2,Nat.add_comm]

theorem literalConstAdd_wires (xs carry : List Wire) (cin one : Wire) (k : Nat) :
    wires (literalConstAdd xs carry cin one k)⊆(one::cin::(xs++carry)).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [literalConstAdd,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro q hq
      have h := (literalConstCell_wires (decide (k%2=1)) x cin cin one).2.2 hq
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      tauto
    | cons x' xs =>
      cases carry with
      | nil => simp [literalConstAdd,wires]
      | cons c cs =>
        intro q hq
        simp only [literalConstAdd,wires_append,Finset.mem_union] at hq
        have hh := literalConstCell_wires (decide (k%2=1)) x cin c one
        rcases hq with (hq|hq)|hq
        · have h := hh.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto
        · have h := ih cs c (k/2) hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
        · have h := hh.2.1 hq
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append]; tauto

theorem literalConstAdd_qubitCount (xs carry : List Wire) (cin one : Wire) (k : Nat)
    (hn : (one::cin::(xs++carry)).Nodup) (hc : carry.length+1=xs.length) :
    qubitCount (literalConstAdd xs carry cin one k)≤2*xs.length+1 := by
  have h := Finset.card_le_card (literalConstAdd_wires xs carry cin one k)
  rw [List.toFinset_card_of_nodup hn] at h
  simp only [List.length_cons,List.length_append] at h
  unfold qubitCount
  omega

end ECDSAAdd.Arithmetic
