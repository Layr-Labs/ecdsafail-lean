import ECDSAAdd.Arithmetic.MappedSubtract
import ECDSAAdd.Arithmetic.SignedSquareDiagonalProof

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def mappedDiagSub (xs dst carry : List Wire) (cin : Wire) : Program :=
  mappedSub (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

def mappedDiagAdd (xs dst carry : List Wire) (cin : Wire) : Program :=
  mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

theorem mappedDiagonal_wires (xs : List Wire) :
    mappedWires (mappedDiagonal xs)=xs++xs.take (xs.length-1) := by
  simp only [mappedDiagonal,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_none,List.nil_append,List.append_nil]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList) (mappedRead xs false)=xs from
    mappedRead_wires xs false]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList)
      (mappedRead (xs.take (xs.length-1)) true)=xs.take (xs.length-1) from
    mappedRead_wires _ true]

theorem mappedDiagonal_exact (xs : List Wire) (s : BasisState) (hx : 0<xs.length) :
    mappedValue (mappedDiagonal xs) s=signedDiagValue (regValue xs s) xs.length := by
  have takeValue : regValue (xs.take (xs.length-1)) s=regValue xs s%2^(xs.length-1) := by
    have eq := regValue_append (xs.take (xs.length-1)) (xs.drop (xs.length-1)) s
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (Nat.sub_le xs.length 1)] at eq
    rw [eq,Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt (by
      simpa only [List.length_take,Nat.min_eq_left (Nat.sub_le xs.length 1)] using regValue_lt (xs.take (xs.length-1)) s)).symm
  rw [mappedDiagonal_value,takeValue]
  simp [signedDiagValue,show xs.length≠0 by omega,Nat.mul_comm]

private theorem mapped_diag_views (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) :
    (cin::dst++carry.take (dst.length-1)).Nodup ∧
      (∀q∈mappedWires (mappedDiagonal xs),q∉cin::dst++carry.take (dst.length-1)) := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  · intro q hq bad
    rw [mappedDiagonal_wires] at hq
    have src : q∈xs := by
      rcases List.mem_append.mp hq with h|h
      · exact h
      · exact List.mem_of_mem_take h
    have h := List.nodup_iff_count.mp hn q
    have pos := List.count_pos_iff.mpr src
    have b := List.count_pos_iff.mpr bad
    have takeBound := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h b
    omega

theorem mappedDiagSub_correct (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (mappedDiagSub xs dst carry cin) m s).phase=s.phase ∧
    regValue dst (run (mappedDiagSub xs dst carry cin) m s).basis=
      (regValue dst s.basis+2^dst.length-signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
    ∀q,q∉dst → (run (mappedDiagSub xs dst carry cin) m s).basis q=s.basis q := by
  have views := mapped_diag_views cin xs dst carry hn
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  obtain ⟨phase,same,value⟩ := mappedSub_correct (mappedDiagonal xs) dst (carry.take (dst.length-1))
    cin views.1 views.2 len cl s m (fun q hq =>
      (regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq)) hi
  exact ⟨phase,by simpa only [mappedDiagonal_exact xs s.basis hx] using value,same⟩

theorem mappedDiagAdd_correct (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (mappedDiagAdd xs dst carry cin) m s).phase=s.phase ∧
    regValue dst (run (mappedDiagAdd xs dst carry cin) m s).basis=
      (regValue dst s.basis+signedDiagValue (regValue xs s.basis) xs.length)%2^dst.length ∧
    ∀q,q∉dst → (run (mappedDiagAdd xs dst carry cin) m s).basis q=s.basis q := by
  have views := mapped_diag_views cin xs dst carry hn
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  obtain ⟨phase,same,value⟩ := mappedAdd_correct (mappedDiagonal xs) dst (carry.take (dst.length-1))
    cin views.1 views.2 len cl s m (fun q hq =>
      (regValue_zero _ _).mp hclean q (List.mem_of_mem_take hq))
  exact ⟨phase,by simpa [hi,mappedDiagonal_exact xs s.basis hx,Nat.add_comm] using value,same⟩

theorem mappedDiag_counts (xs dst carry : List Wire) (cin : Wire)
    (hx : 0<xs.length) (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length) :
    (toffoliCount (mappedDiagSub xs dst carry cin)=dst.length-1 ∧
      measurementCount (mappedDiagSub xs dst carry cin)=dst.length-1) ∧
    (toffoliCount (mappedDiagAdd xs dst carry cin)=dst.length-1 ∧
      measurementCount (mappedDiagAdd xs dst carry cin)=dst.length-1) := by
  have len : (mappedDiagonal xs).length=dst.length := (mappedDiagonal_length xs hx).trans hd.symm
  have cl : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
  exact ⟨mappedSub_counts _ _ _ _ len cl,mappedAdd_counts _ _ _ _ len cl⟩

private theorem mappedDiag_cancel (A D N : Nat) (hN : 0<N) (hA : A<N) (hD : D<N) :
    (((A+N-D)%N)+D)%N=A := by
  by_cases less : D≤A
  · rw [show A+N-D=(A-D)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : A-D<N),Nat.sub_add_cancel less,Nat.mod_eq_of_lt hA]
  · rw [Nat.mod_eq_of_lt (by omega : A+N-D<N),
      show A+N-D+D=A+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hA]

theorem mappedDiag_roundtrip (cin : Wire) (xs dst carry : List Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (subRecords addRecords : List Bool)
    (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    run (mappedDiagAdd xs dst carry cin) addRecords
      (run (mappedDiagSub xs dst carry cin) subRecords s)=s := by
  let u := run (mappedDiagSub xs dst carry cin) subRecords s
  let out := run (mappedDiagAdd xs dst carry cin) addRecords u
  have sub := mappedDiagSub_correct cin xs dst carry hn hx hd hc s subRecords hclean hi
  have away (q : Wire) (hq : q∈cin::xs++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have source : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => sub.2.2 q (away q (by simp [hq])))
  have clean : regValue carry u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sub.2.2 q (away q (by simp [hq])))).trans hclean
  have ci : u.basis cin=false := (sub.2.2 cin (away cin (by simp))).trans hi
  have add := mappedDiagAdd_correct cin xs dst carry hn hx hd hc u addRecords clean ci
  have bound : signedDiagValue (regValue xs s.basis) xs.length<2^dst.length := by
    rw [←mappedDiagonal_exact xs s.basis hx]
    have h := mappedValue_lt (mappedDiagonal xs) s.basis
    simpa [mappedDiagonal_length xs hx,hd] using h
  have output : regValue dst out.basis=regValue dst s.basis := by
    rw [add.2.1,sub.2.1,source]
    exact mappedDiag_cancel _ _ _ (Nat.two_pow_pos _) (regValue_lt dst s.basis) bound
  have phase : out.phase=s.phase := add.1.trans sub.1
  have basis : out.basis=s.basis := by
    funext q
    by_cases inDst : q∈dst
    · exact (regValue_eq_iff dst out.basis s.basis).mp output q inDst
    · exact (add.2.2 q inDst).trans (sub.2.2 q inDst)
  change out=s
  calc
    out=⟨out.phase,out.basis⟩ := rfl
    _=⟨s.phase,s.basis⟩ := by rw [phase,basis]
    _=s := rfl

end ECDSAAdd.Arithmetic
