import ECDSAAdd.Arithmetic.Divsteps.InverseRowKernel
import ECDSAAdd.Arithmetic.Divsteps.CoefficientPair

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Restore the source coefficient before subtracting it from the target. -/
def inverseCoefficientPair (q c cin active low sign : Wire)
    (mid mask y carry : List Wire) : Program :=
  undoubleSigned active low sign mid ++ inverseRowKernel q c cin (low::(mid++[sign])) mask y carry

private theorem no_measurement_records (p : Program) (hp : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  rw [←run_take p m s,←run_take p n s,hp]
  rfl

theorem inverseCoefficientPair_after (q c cin active low sign : Wire) (mid mask y carry : List Wire)
    (hn : (q::c::cin::((low::(mid++[sign]))++mask++y++carry)).Nodup)
    (hdnd : (active::low::(mid++[sign])).Nodup)
    (hs : (low::(mid++[sign])).length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) (Q C : Bool) (A B : Int)
    (hBlo : -((2^(y.length-1):Nat):Int)≤B) (hBhi : B<((2^(y.length-1):Nat):Int))
    (hneglo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B))
    (hneghi : (if Q then -B else B) < ((2^(y.length-1):Nat):Int))
    (hlo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B)+(if C then A else 0))
    (hhi : (if Q then -B else B)+(if C then A else 0) < ((2^(y.length-1):Nat):Int))
    (s : State) (mf mi : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue (low::(mid++[sign])) s.basis=A)
    (hb : signedRegValue y s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    run (inverseCoefficientPair q c cin active low sign mid mask y carry) mi
      (run (coefficientPair q c cin active low sign mid mask y carry) mf s)=s := by
  have hdm : measurementCount (undoubleSigned active low sign mid)=0 := by
    simp [undoubleSigned,measurementCount,
      (shift_counts active (low::(mid++[sign]))).2.1]
  have hcancel (t : State) (m n : List Bool) :
      run (undoubleSigned active low sign mid) m (run (doubleSigned active low sign mid) n t)=t := by
    rw [no_measurement_records _ (doubleSigned_counts active low sign mid).2 t n m]
    exact undoubleSigned_doubleSigned active low sign mid hdnd t m
  simp only [inverseCoefficientPair,coefficientPair,run_append,run_take,hdm,List.drop_zero]
  rw [hcancel]
  exact inverseRowKernel_after q c cin (low::(mid++[sign])) mask y carry hn hs ht hc Q C A B
    hBlo hBhi hneglo hneghi hlo hhi s mf mi hq hcc hi ha hb hm hk

theorem inverseCoefficientPair_counts (q c cin active low sign : Wire)
    (mid mask y carry : List Wire)
    (hs : (low::(mid++[sign])).length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    toffoliCount (inverseCoefficientPair q c cin active low sign mid mask y carry)=
      (mid.length+2)+(3*y.length-2) ∧
    measurementCount (inverseCoefficientPair q c cin active low sign mid mask y carry)=3*y.length-2 := by
  obtain ⟨htf,hm⟩ := inverseRowKernel_counts q c cin (low::(mid++[sign])) mask y carry hs ht hc
  have hh := shift_counts active (low::(mid++[sign]))
  simp [inverseCoefficientPair,undoubleSigned,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,hh.1,hh.2.1,htf,hm]
  omega

theorem undoubleSigned_wires_eq (active low sign : Wire) (mid : List Wire) :
    wires (undoubleSigned active low sign mid)=wires (doubleSigned active low sign mid) := by
  rw [undoubleSigned,doubleSigned,wires_append,wires_append,
    (shift_wires active (low::(mid++[sign]))).1,(shift_wires active (low::(mid++[sign]))).2]
  exact Finset.union_comm _ _

theorem inverseCoefficientPair_wires_eq (q c cin active low sign : Wire) (mid mask y carry : List Wire)
    (hs : (low::(mid++[sign])).length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    wires (inverseCoefficientPair q c cin active low sign mid mask y carry)=
      wires (coefficientPair q c cin active low sign mid mask y carry) := by
  rw [inverseCoefficientPair,coefficientPair,wires_append,wires_append,undoubleSigned_wires_eq,
    inverseRowKernel_wires_eq q c cin (low::(mid++[sign])) mask y carry hs ht hc]
  exact Finset.union_comm _ _

end ECDSAAdd.Arithmetic.Divsteps
