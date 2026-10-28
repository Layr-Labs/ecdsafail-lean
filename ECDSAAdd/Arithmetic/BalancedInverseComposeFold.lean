import ECDSAAdd.Arithmetic.BalancedInverseComposeFlags

set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- The actual left rotation restores the cleared low bit and the upper
word, with phase and every outside wire preserved. -/
theorem rotate_unfold (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (s : State) (m : List Bool) (ho : s.basis L.one=false)
    (hR : regValue L.r s.basis=encodeWord 256 R) :
    (run (rotateLeft (rawTarget L)) m s).phase=s.phase ∧
    (run (rotateLeft (rawTarget L)) m s).basis L.r0=false ∧
    regValue (foldTarget L) (run (rotateLeft (rawTarget L)) m s).basis=encodeWord 256 R ∧
    ∀w,w∉rawTarget L →
      (run (rotateLeft (rawTarget L)) m s).basis w=s.basis w := by
  have w := BalancedCircuit.widths L hw
  have init : regValue (rawTarget L) s.basis=encodeWord 256 R := by
    rw [rawTarget,regValue_append,hR]
    simp [regValue,ho]
  have rot := rotateLeft_spec (rawTarget L) (rawTargetND L hn) (encodeWord 256 R)
    (by have h := encodeWord_bound 256 R; rw [w.2.1]; omega) s m init
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have value := rot.2
  change regValue (rawTarget L) (run (rotateLeft (rawTarget L)) m s).basis=
    2*encodeWord 256 R at value
  have frame := (rotate_frame (rawTarget L) s m).2.2.2
  generalize runEq : run (rotateLeft (rawTarget L)) m s=t at rot value frame ⊢
  rw [shape] at value
  change (if t.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) t.basis=
      2*encodeWord 256 R at value
  have low : t.basis L.r0=false := by
    cases h : t.basis L.r0 <;> simp [h] at value ⊢
    omega
  refine ⟨rot.1,low,?_,frame⟩
  simp only [low,Bool.false_eq_true,if_false,Nat.zero_add] at value
  omega

/-- Fresh measured mapped subtraction restores the preparation upper word
and cleans Cout by the proved bounded integer split. -/
theorem undoFold_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (undoFold L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (undoFold L) m s).basis=toggledWord T/2 ∧
    (run (undoFold L) m s).basis L.cout=false ∧
    ∀w,w∉foldTarget L → (run (undoFold L) m s).basis w=s.basis w := by
  let ys := foldTarget L++[L.cout]
  have nd : (L.plus::L.minus::L.parity::(ys++L.carry)).Nodup := by
    simpa only [ys,List.cons_append,List.nil_append,List.append_assoc] using foldND L hn
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have yND : ys.Nodup := (List.nodup_append'.mp n3.2).1
  have minusAway : L.minus∉ys := by
    intro h; exact n2.1 (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have coutAway : L.cout∉foldTarget L := by
    intro h
    exact List.disjoint_left.mp (List.nodup_append'.mp yND).2.2 h (by simp)
  have sourceAway : ∀w∈mappedWires (foldBits L),w∉L.parity::(ys++L.carry) := by
    intro w h
    rcases foldBits_sources L w h with rfl|rfl
    · intro h; exact n1.1 (List.mem_cons_of_mem _ h)
    · exact n2.1
  have widths := BalancedCircuit.widths L hw
  have ylen : ys.length=257 := widths.2.2.1
  have lowlen : (foldTarget L).length=256 := by
    have h := ylen
    simp only [ys,List.length_append,List.length_cons,List.length_nil] at h
    omega
  let u : State := ⟨s.phase,writeBit s.basis L.cout (minusController T)⟩
  have step : run [.CX L.minus L.cout] m s=u := by
    simp [run,u,hc,hv]
  have keep (a : Wire) (ha : a≠L.cout) : u.basis a=s.basis a := by
    simp [u,writeBit,ha]
  have pAway : L.parity≠L.cout := by
    intro e; exact n3.1 (List.mem_append_left _ (by simp [ys,←e]))
  have plusAway : L.plus≠L.cout := by
    intro e; exact n1.1 (by simp [ys,←e])
  have vAway : L.minus≠L.cout := fun e => minusAway (by simp [ys,←e])
  have source : mappedValue (foldBits L) u.basis=
      selectedSource (plusController T) (minusController T) := by
    have up : u.basis L.plus=plusController T := (keep _ plusAway).trans hu
    have um : u.basis L.minus=minusController T := (keep _ vAway).trans hv
    have hex : ¬(u.basis L.plus && u.basis L.minus)=true := by
      rw [up,um]; exact controllers_exclusive T
    simpa only [up,um] using foldBits_value L u.basis hex
  have init : regValue ys u.basis=foldedSum T := by
    rw [regValue_append]
    have low : regValue (foldTarget L) u.basis=encodeWord 256 (halfResult T) :=
      (regValue_congr _ _ _ (fun a ha => keep a (fun e => coutAway (e ▸ ha)))).trans hword
    rw [low,lowlen,foldedSum_value T ht]
    simp [u,writeBit,regValue,Bool.toNat,Bool.cond_eq_ite,modulusWord]
  have clean : ∀a∈L.carry,u.basis a=false := by
    intro a ha
    have away : a≠L.cout := by
      intro e
      exact List.disjoint_left.mp (List.nodup_append'.mp n3.2).2.2 (by simp [ys,←e]) ha
    exact (keep a away).trans ((regValue_zero _ _).mp hcarry a ha)
  have sub := mappedSub_any_correct (foldBits L) ys L.carry L.parity n2.2
    sourceAway (by omega) (by omega) u (m.drop 0) clean
  have value : regValue ys (run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u).basis=
      toggledWord T/2 := by
    have h := sub.2.2
    rw [init,source,keep L.parity pAway,hp,ylen] at h
    have eq := foldedSum_value T ht
    have b := prepared_upper_bound T ht
    have expression : (foldedSum T+2^257-selectedSource (plusController T) (minusController T)-
        (originalParity T).toNat)%2^257=toggledWord T/2 := by
      have fs : foldedSum T=toggledWord T/2+
          selectedSource (plusController T) (minusController T)+(originalParity T).toNat := rfl
      have power : (2^257 : Nat)=2*modulusWord := by decide
      rw [show foldedSum T+2^257-selectedSource (plusController T) (minusController T)-
        (originalParity T).toNat=toggledWord T/2+2^257 by omega,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    exact h.trans expression
  have actual : run (undoFold L) m s=
      run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u := by
    unfold undoFold
    rw [run_append,run_take]
    change run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0)
      (run [.CX L.minus L.cout] m s)=_
    rw [step]
  rw [actual]
  generalize hr : run (mappedSub (foldBits L) ys L.carry L.parity) (m.drop 0) u=r at sub value ⊢
  have split := regValue_append (foldTarget L) [L.cout] r.basis
  have one : regValue [L.cout] r.basis=(r.basis L.cout).toNat := by
    cases h : r.basis L.cout <;> simp [regValue,h]
  rw [one,lowlen] at split
  have eq : regValue (foldTarget L) r.basis+modulusWord*(r.basis L.cout).toNat=toggledWord T/2 :=
    split.symm.trans value
  have bound := prepared_upper_bound T ht
  have cout : r.basis L.cout=false := by
    cases h : r.basis L.cout <;> simp [h] at eq ⊢
    omega
  refine ⟨sub.1,?_,cout,?_⟩
  · simpa [cout] using eq
  · intro a ha
    by_cases he : a=L.cout
    · subst a; exact cout.trans hc.symm
    · exact (sub.2.1 a (by simp [ys,ha,he])).trans (keep a he)

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.rotate_unfold
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.undoFold_correct
