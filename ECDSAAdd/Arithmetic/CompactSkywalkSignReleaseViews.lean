import ECDSAAdd.Arithmetic.CompactSkywalkSignReleaseMath

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Physical take/drop allocation: the omitted tail is really cleared by CX. -/
def compactSkywalkSignWord (r : List Wire) (n : Nat) : CompactSkywalkSignReleaseLayout :=
  {low:=r.take (n-1),sign:=r.getD (n-1) 0,released:=r.drop n}

theorem compactSkywalkSignWord_retained (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) : (compactSkywalkSignWord r n).retained = r.take n := by
  have hidx : n-1 < r.length := by omega
  have he : n = (n-1)+1 := by omega
  change r.take (n-1)++[r.getD (n-1) 0] = r.take n
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

theorem compactSkywalkSignWord_expanded (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) : (compactSkywalkSignWord r n).expanded = r := by
  rw [CompactSkywalkSignReleaseLayout.expanded,compactSkywalkSignWord_retained r n hn hle]
  exact List.take_append_drop n r

theorem compactSkywalkSignWord_valid (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (hr : r.Nodup) : (compactSkywalkSignWord r n).Valid := by
  change (compactSkywalkSignWord r n).expanded.Nodup
  rw [compactSkywalkSignWord_expanded r n hn hle]
  exact hr

theorem compactSkywalkSignWord_lengths (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained.length = n ∧
    (compactSkywalkSignWord r n).released.length = r.length-n := by
  rw [compactSkywalkSignWord_retained r n hn hle]
  simp [compactSkywalkSignWord,Nat.min_eq_left hle]

/-- A strict signed fit proves the required redundant copies, without sampling. -/
theorem compactSkywalkSignWord_copies (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (s : BasisState) (A : Int)
    (ha : signedRegValue r s = A)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int)) :
    (compactSkywalkSignWord r n).Copies s := by
  apply compactSkywalkSignRelease_copies_of_fit (compactSkywalkSignWord r n) s A
  · simpa only [compactSkywalkSignWord_expanded r n hn hle] using ha
  · simpa only [(compactSkywalkSignWord_lengths r n hn hle).1] using ha0
  · simpa only [(compactSkywalkSignWord_lengths r n hn hle).1] using ha1

/-- Certified physical compaction: signed prefix, clean omitted sites,
and complete outsider frame, with arbitrary phase and record stream. -/
theorem compactSkywalkSignWord_release (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (hr : r.Nodup) (s : State) (m : List Bool) (A : Int)
    (ha : signedRegValue r s.basis = A)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int)) :
    (run (compactSkywalkSignRelease (compactSkywalkSignWord r n)) m s).phase = s.phase ∧
    signedRegValue (r.take n) (run (compactSkywalkSignRelease (compactSkywalkSignWord r n)) m s).basis = A ∧
    (∀q ∈ r.drop n,(run (compactSkywalkSignRelease (compactSkywalkSignWord r n)) m s).basis q = false) ∧
    (∀q,q ∉ r.drop n → (run (compactSkywalkSignRelease (compactSkywalkSignWord r n)) m s).basis q = s.basis q) := by
  have hv := compactSkywalkSignWord_valid r n hn hle hr
  have hc := compactSkywalkSignWord_copies r n hn hle s.basis A ha ha0 ha1
  have hp := compactSkywalkSignRelease_phase_frame (compactSkywalkSignWord r n) hv s m
  have hs := compactSkywalkSignRelease_signed (compactSkywalkSignWord r n) hv s m hc
  rw [compactSkywalkSignWord_retained r n hn hle,compactSkywalkSignWord_expanded r n hn hle,ha] at hs
  exact ⟨hp.1,hs,compactSkywalkSignRelease_clean _ hv s m hc,hp.2.1⟩

/-- Reconstruct after a loan is returned clean, using the current signed prefix. -/
theorem compactSkywalkSignWord_expand (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) (hr : r.Nodup) (s : State) (m : List Bool)
    (hc : ∀q ∈ r.drop n,s.basis q = false) :
    signedRegValue r (run (compactSkywalkSignExpand (compactSkywalkSignWord r n)) m s).basis = 
      signedRegValue (r.take n) s.basis := by
  have h := compactSkywalkSignExpand_signed (compactSkywalkSignWord r n)
    (compactSkywalkSignWord_valid r n hn hle hr) s m hc
  simpa only [compactSkywalkSignWord_expanded r n hn hle,
    compactSkywalkSignWord_retained r n hn hle] using h

/-- No carry or any other external allocation occurs in either actual program. -/
theorem compactSkywalkSignWord_support (r : List Wire) (n : Nat)
    (hn : 0 < n) (hle : n ≤ r.length) :
    wires (compactSkywalkSignRelease (compactSkywalkSignWord r n)) ⊆ r.toFinset ∧
    wires (compactSkywalkSignExpand (compactSkywalkSignWord r n)) ⊆ r.toFinset := by
  have hs := compactSkywalkSignRelease_support (compactSkywalkSignWord r n)
  have sub : ((compactSkywalkSignWord r n).sign::(compactSkywalkSignWord r n).released).toFinset⊆r.toFinset := by
    intro q hq
    apply List.mem_toFinset.mpr
    rw [←compactSkywalkSignWord_expanded r n hn hle]
    simp only [CompactSkywalkSignReleaseLayout.expanded]
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with he|he
    · exact List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained,he])
    · exact List.mem_append_right _ he
  exact ⟨hs.1.trans sub,hs.2.trans sub⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignWord_release
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignWord_expand
