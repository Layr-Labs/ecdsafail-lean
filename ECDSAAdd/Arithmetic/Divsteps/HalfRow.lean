import ECDSAAdd.Arithmetic.Divsteps.RowKernel

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Integer-row update: shared signed arithmetic followed by exact Clifford
halving. The result is read in the rotated view, not the old wire order. -/
def halfRow (q c cin low sign : Wire) (src mask mid carry : List Wire) : Program :=
  rowKernel q c cin src mask (low::(mid++[sign])) carry ++ skywalkSignedHalf sign low

theorem halfRow_correct (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hn : (q::c::cin::(src++mask++(low::(mid++[sign]))++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2)
    (hc : carry.length+1=mid.length+2) (Q C : Bool) (A B : Int)
    (hneglo : -((2^(mid.length+1):Nat):Int) ≤ (if Q then -B else B))
    (hneghi : (if Q then -B else B) < ((2^(mid.length+1):Nat):Int))
    (hlo : -((2^(mid.length+1):Nat):Int) ≤ (if Q then -B else B)+(if C then A else 0))
    (hhi : (if Q then -B else B)+(if C then A else 0) < ((2^(mid.length+1):Nat):Int))
    (heven : ((if Q then -B else B)+(if C then A else 0))%2=0)
    (s : State) (m : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=A)
    (hb : signedRegValue (low::(mid++[sign])) s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    (run (halfRow q c cin low sign src mask mid carry) m s).phase=s.phase ∧
    (∀ w, w∉low::(mid++[sign]) →
      (run (halfRow q c cin low sign src mask mid carry) m s).basis w=s.basis w) ∧
    signedRegValue (skywalkHalfView low (mid++[sign]))
      (run (halfRow q c cin low sign src mask mid carry) m s).basis=
      ((if Q then -B else B)+(if C then A else 0))/2 := by
  have htl : mask.length=(low::(mid++[sign])).length := by simpa using ht
  have hcl : carry.length+1=(low::(mid++[sign])).length := by simpa using hc
  have hynd : (low::(mid++[sign])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at this ⊢
    omega
  have hlow := (List.nodup_cons.mp hynd).1
  have hsl : sign≠low := by intro h; apply hlow; simp [←h]
  let t := run (rowKernel q c cin src mask (low::(mid++[sign])) carry) m s
  let rest := m.drop (measurementCount (rowKernel q c cin src mask (low::(mid++[sign])) carry))
  obtain ⟨hp,hframe,hval⟩ := rowKernel_correct q c cin src mask (low::(mid++[sign])) carry
    hn hs htl hcl Q C A B (by simpa using hneglo) (by simpa using hneghi)
    (by simpa using hlo) (by simpa using hhi) s m hq hcc hi ha hb hm hk
  have he : signedRegValue (low::(mid++[sign])) t.basis%2=0 := by rw [hval]; exact heven
  have hhalf := skywalkSignedHalf_int low sign mid hsl hlow t rest he
  rw [hval] at hhalf
  have hf := skywalkSignedHalf_frame sign low t rest
  rw [halfRow,run_append,run_take]
  refine ⟨hf.1.trans hp,?_,hhalf⟩
  intro w hw
  have hwl : w≠low := by intro h; subst w; exact hw (List.mem_cons_self)
  exact (hf.2 w hwl).trans (hframe w hw)

theorem halfRow_counts (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2)
    (hc : carry.length+1=mid.length+2) :
    toffoliCount (halfRow q c cin low sign src mask mid carry)=3*(mid.length+2)-2 ∧
    measurementCount (halfRow q c cin low sign src mask mid carry)=3*(mid.length+2)-2 := by
  have hr := rowKernel_counts q c cin src mask (low::(mid++[sign])) carry hs
    (by simpa using ht) (by simpa using hc)
  have hh := skywalkSignedHalf_counts sign low
  simpa [halfRow,toffoliCount_append,measurementCount_append,hh.1,hh.2] using hr

theorem halfRow_wires (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2)
    (hc : carry.length+1=mid.length+2) :
    wires (halfRow q c cin low sign src mask mid carry)=
      (q::c::cin::(src++mask++(low::(mid++[sign]))++carry)).toFinset := by
  rw [halfRow,wires_append,rowKernel_wires q c cin src mask (low::(mid++[sign])) carry
    hs (by simpa using ht) (by simpa using hc),skywalkSignedHalf_wires]
  apply Finset.union_eq_left.mpr
  intro w hw
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl <;> simp

end ECDSAAdd.Arithmetic.Divsteps
