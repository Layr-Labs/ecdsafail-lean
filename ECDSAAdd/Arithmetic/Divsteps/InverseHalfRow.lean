import ECDSAAdd.Arithmetic.Divsteps.InverseRowKernel
import ECDSAAdd.Arithmetic.Divsteps.HalfRow

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Undo the Clifford half in the old wire layout before inverting its row
kernel. No measurement instruction is reversed. -/
def inverseHalfRow (q c cin low sign : Wire) (src mask mid carry : List Wire) : Program :=
  skywalkSignedHalf sign low ++ inverseRowKernel q c cin src mask (low::(mid++[sign])) carry

theorem inverseHalfRow_after (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hn : (q::c::cin::(src++mask++(low::(mid++[sign]))++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=(low::(mid++[sign])).length)
    (hc : carry.length+1=(low::(mid++[sign])).length) (Q C : Bool) (A B : Int)
    (hBlo : -((2^((low::(mid++[sign])).length-1):Nat):Int)≤B) (hBhi : B<((2^((low::(mid++[sign])).length-1):Nat):Int))
    (hneglo : -((2^((low::(mid++[sign])).length-1):Nat):Int) ≤ (if Q then -B else B))
    (hneghi : (if Q then -B else B) < ((2^((low::(mid++[sign])).length-1):Nat):Int))
    (hlo : -((2^((low::(mid++[sign])).length-1):Nat):Int) ≤ (if Q then -B else B)+(if C then A else 0))
    (hhi : (if Q then -B else B)+(if C then A else 0) < ((2^((low::(mid++[sign])).length-1):Nat):Int))
    (s : State) (mf mi : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=A)
    (hb : signedRegValue (low::(mid++[sign])) s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    run (inverseHalfRow q c cin low sign src mask mid carry) mi
      (run (halfRow q c cin low sign src mask mid carry) mf s)=s := by
  have hsl : sign≠low := by
    intro he
    have hh := List.nodup_iff_count.mp hn low
    simp only [List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega
  have hhalf (t : State) (m n : List Bool) :
      run (skywalkSignedHalf sign low) m (run (skywalkSignedHalf sign low) n t)=t :=
    skywalkSignedHalf_twice sign low hsl t m
  simp only [inverseHalfRow,halfRow,run_append,run_take,
    (skywalkSignedHalf_counts sign low).2,List.drop_zero]
  rw [hhalf]
  exact inverseRowKernel_after q c cin src mask (low::(mid++[sign])) carry hn hs ht hc Q C A B
    hBlo hBhi hneglo hneghi hlo hhi s mf mi hq hcc hi ha hb hm hk

theorem inverseHalfRow_counts (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2) (hc : carry.length+1=mid.length+2) :
    toffoliCount (inverseHalfRow q c cin low sign src mask mid carry)=3*(mid.length+2)-2 ∧
    measurementCount (inverseHalfRow q c cin low sign src mask mid carry)=3*(mid.length+2)-2 := by
  have hh := inverseRowKernel_counts q c cin src mask (low::(mid++[sign])) carry hs
    (by simpa using ht) (by simpa using hc)
  simpa [inverseHalfRow,toffoliCount_append,measurementCount_append,
    (skywalkSignedHalf_counts sign low).1,(skywalkSignedHalf_counts sign low).2] using hh

theorem inverseHalfRow_wires_eq (q c cin low sign : Wire) (src mask mid carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=mid.length+2) (hc : carry.length+1=mid.length+2) :
    wires (inverseHalfRow q c cin low sign src mask mid carry)=wires (halfRow q c cin low sign src mask mid carry) := by
  rw [inverseHalfRow,halfRow,wires_append,wires_append,
    inverseRowKernel_wires_eq q c cin src mask (low::(mid++[sign])) carry hs
      (by simpa using ht) (by simpa using hc)]
  exact Finset.union_comm _ _

end ECDSAAdd.Arithmetic.Divsteps
