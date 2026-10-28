import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Arithmetic.BalancedFoldMathViews

set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

private theorem bit_split (M x E : Nat) (b v : Bool) (hx : x<M) (hE : E<M)
    (he : x+M*b.toNat=E+M*v.toNat) : x=E ∧ b=v := by
  cases b <;> cases v <;> simp at he ⊢ <;> omega

/-- The actual extended mapped adder and final Cout XOR. No arithmetic
oracle is substituted, and all measurement records have restored phase. -/
theorem fold_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hu : s.basis L.plus=plusController T) (hv : s.basis L.minus=minusController T)
    (hc : s.basis L.cout=false) (hcarry : regValue L.carry s.basis=0)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    (run (fold L) m s).phase=s.phase ∧
    regValue (foldTarget L) (run (fold L) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (fold L) m s).basis L.cout=false ∧
    ∀ w,w∉foldTarget L → (run (fold L) m s).basis w=s.basis w := by
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
  have sourceAway : ∀ w∈mappedWires (foldBits L),w∉L.parity::(ys++L.carry) := by
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
  have init : regValue ys s.basis=toggledWord T/2 := by
    rw [regValue_append,hword]
    simp [regValue,hc]
  have source : mappedValue (foldBits L) s.basis=
      selectedSource (plusController T) (minusController T) := by
    have hex : ¬(s.basis L.plus && s.basis L.minus)=true := by
      rw [hu,hv]; exact controllers_exclusive T
    simpa only [hu,hv] using foldBits_value L s.basis hex
  have hadd := mappedAdd_correct (foldBits L) ys L.carry L.parity n2.2 sourceAway
    (by omega) (by omega) s m ((regValue_zero _ _).mp hcarry)
  generalize hr : run (mappedAdd (foldBits L) ys L.carry L.parity) m s=r at hadd
  have value : regValue ys r.basis=foldedSum T := by
    have h := hadd.2.2
    rw [source,init,hp,ylen,Nat.add_comm (selectedSource _ _) (toggledWord T/2)] at h
    change regValue ys r.basis=foldedSum T%2^257 at h
    rw [Nat.mod_eq_of_lt (foldedSum_bound T ht)] at h
    exact h
  have split := regValue_append (foldTarget L) [L.cout] r.basis
  have one : regValue [L.cout] r.basis=(r.basis L.cout).toNat := by
    cases h : r.basis L.cout <;> simp [regValue,h]
  rw [one,lowlen] at split
  have eqvalue : regValue (foldTarget L) r.basis+
      modulusWord*(r.basis L.cout).toNat=
      encodeWord 256 (halfResult T)+modulusWord*(minusController T).toNat := by
    exact split.symm.trans (value.trans (foldedSum_value T ht))
  have decoded := bit_split modulusWord (regValue (foldTarget L) r.basis)
    (encodeWord 256 (halfResult T)) (r.basis L.cout) (minusController T)
    (by simpa only [lowlen,modulusWord] using regValue_lt (foldTarget L) r.basis)
    (encodeWord_bound 256 (halfResult T)) eqvalue
  have minusR : r.basis L.minus=minusController T := (hadd.2.1 L.minus minusAway).trans hv
  have actual : run (fold L) m s=
      ⟨r.phase,writeBit r.basis L.cout (r.basis L.cout ^^ r.basis L.minus)⟩ := by
    unfold fold
    rw [run_append,run_take,hr]
    rfl
  have lowKeep : regValue (foldTarget L)
      (writeBit r.basis L.cout (r.basis L.cout ^^ r.basis L.minus))=
      regValue (foldTarget L) r.basis := by
    apply regValue_congr
    intro w hw
    simp [writeBit,show w≠L.cout from fun he => coutAway (he ▸ hw)]
  rw [actual]
  refine ⟨hadd.1,lowKeep.trans decoded.1,?_,?_⟩
  · simp [writeBit,decoded.2,minusR]
  · intro w hw
    by_cases he : w=L.cout
    · subst w; simp [writeBit,decoded.2,minusR,hc]
    · simp only [writeBit,Function.update_of_ne he]
      apply hadd.2.1
      simp only [ys,List.mem_append,List.mem_singleton]
      exact not_or.mpr ⟨hw,he⟩

/-- The actual Clifford rotate divides the cleared-low-bit raw word by
two. Its old zero low bit becomes the clean One guard. -/
theorem rotate_folded (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (_ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hzero : s.basis L.r0=false)
    (hword : regValue (foldTarget L) s.basis=encodeWord 256 (halfResult T)) :
    (run (rotateRight (rawTarget L)) m s).phase=s.phase ∧
    regValue L.r (run (rotateRight (rawTarget L)) m s).basis=encodeWord 256 (halfResult T) ∧
    (run (rotateRight (rawTarget L)) m s).basis L.one=false ∧
    ∀ w,w∉rawTarget L → (run (rotateRight (rawTarget L)) m s).basis w=s.basis w := by
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have init : regValue (rawTarget L) s.basis=2*encodeWord 256 (halfResult T) := by
    rw [shape]
    change (if s.basis L.r0 then 1 else 0)+2*regValue (foldTarget L) s.basis=_
    simp [hzero,hword]
  have rr := rotateRight_spec (rawTarget L) (rawTargetND L hn)
    (2*encodeWord 256 (halfResult T)) (by omega) s m init
  have frame := (rotate_frame (rawTarget L) s m).2.1
  generalize hr : run (rotateRight (rawTarget L)) m s=r at rr frame ⊢
  have value : regValue (rawTarget L) r.basis=encodeWord 256 (halfResult T) := by
    have h := rr.2
    change regValue (rawTarget L) r.basis=(2*encodeWord 256 (halfResult T))/2 at h
    omega
  have rlen : L.r.length=256 := (BalancedCleanup.widths L.toLayout hw).2.1
  have split := regValue_append L.r [L.one] r.basis
  have one : regValue [L.one] r.basis=(r.basis L.one).toNat := by
    cases h : r.basis L.one <;> simp [regValue,h]
  rw [one,rlen] at split
  have eqvalue : regValue L.r r.basis+modulusWord*(r.basis L.one).toNat=
      encodeWord 256 (halfResult T)+modulusWord*false.toNat := by
    simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using split.symm.trans value
  have decoded := bit_split modulusWord (regValue L.r r.basis)
    (encodeWord 256 (halfResult T)) (r.basis L.one) false
    (by simpa only [rlen,modulusWord] using regValue_lt L.r r.basis)
    (encodeWord_bound 256 (halfResult T)) eqvalue
  exact ⟨rr.1,decoded.1,decoded.2,frame⟩

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.fold_correct
#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.rotate_folded
