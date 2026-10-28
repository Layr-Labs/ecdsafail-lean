import ECDSAAdd.Arithmetic.NativeFirstDirectAddProof
import ECDSAAdd.Framework.GateInverse
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd run hAdd kAdd kTail

private theorem state_of_value_frame (r : List Wire) (s t : State)
    (hp : t.phase=s.phase) (hv : regValue r t.basis=regValue r s.basis)
    (he : ∀q,q∉r → t.basis q=s.basis q) : t=s := by
  apply congrArg₂ State.mk hp
  funext q
  by_cases hq : q∈r
  · exact (regValue_eq_iff r _ _).mp hv q hq
  · exact he q hq

private theorem mod_add_cancel (a b x M : Nat) (_hM : 0<M)
    (hab : (a+b)%M=0) (hx : x<M) : (b+(a+x)%M)%M=x := by
  have normalize : (b+(a+x)%M)%M=(b+(a+x))%M := by
    simp only [Nat.add_mod,Nat.mod_mod]
  rw [normalize]
  have rearrange : b+(a+x)=a+b+x := by omega
  rw [rearrange,Nat.add_mod,hab,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hx]

private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]
private theorem low_one_mod (C T : Nat) (b : Bool) (hc : C%2=1) :
    (!b).toNat+2*((C/2+T+b.toNat)%2^257)=(b.toNat+2*T+C)%2^258 := by
  have split := Nat.mod_add_div C 2
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_false,
    Bool.not_true,Nat.add_zero] <;> omega
private theorem toggle_head_value (h : Wire) (r : List Wire) (s : BasisState)
    (ha : h∉r) :
    regValue (h::r) (writeBit s h (!(s h)))=(!s h).toNat+2*regValue r s := by
  have head : (writeBit s h (!(s h))) h=!(s h) := by simp [writeBit]
  have tail : regValue r (writeBit s h (!(s h)))=regValue r s := by
    apply regValue_congr
    intro q hq
    have ne : q≠h := by intro e; subst q; exact ha hq
    simp [writeBit,ne]
  rw [cons_value,head,tail]

theorem hAdd_cancel (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hn : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hs : ∀i q,q∈mappedWires (hBits w i) →
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (flag : w 1028∉wireBlock w 4 253)
    (hc : ∀q∈wireBlock w 1540 252,s.basis q=false)
    (cin : s.basis (w 1797)=false) :
    run (hAdd w true) mI (run (hAdd w false) mF s)=s := by
  let t := run (hAdd w false) mF s
  have f := hAdd_spec w false s mF hn (hs false) hc
  have away (q : Wire) (hq : q∈wireBlock w 1540 252) : q∉wireBlock w 4 253 := by
    exact List.disjoint_right.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2 hq
  have caway := (List.nodup_cons.mp hn).1
  have tclean : ∀q∈wireBlock w 1540 252,t.basis q=false := by
    intro q hq; exact (f.2.1 q (away q hq)).trans (hc q hq)
  have i := hAdd_spec w true t mI hn (hs true) tclean
  have tf : t.basis (w 1028)=s.basis (w 1028) := f.2.1 _ flag
  have tc : t.basis (w 1797)=false :=
    (f.2.1 _ (fun h => caway (List.mem_append_left _ h))).trans cin
  have sum : ((if s.basis (w 1028) then (2^256-hConstant)/8 else 0)+
      (if s.basis (w 1028) then hConstant/8 else 0))%2^253=0 := by
    cases s.basis (w 1028) <;> decide
  apply state_of_value_frame (wireBlock w 4 253) s _ (i.1.trans f.1)
  · rw [i.2.2,tf,tc,f.2.2,cin]
    simp only [Bool.toNat_false,Nat.add_zero,if_false]
    apply mod_add_cancel _ _ _ _ (by positivity)
      (by simpa [Nat.add_comm] using sum)
    simpa only [wireBlock_length] using regValue_lt (wireBlock w 4 253) s.basis
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

/-- Full K word, including the delayed low-bit flip. -/
theorem kAdd_spec (w : Nat → Wire) (inv : Bool) (s : State) (m : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀q∈mappedWires (kBits w inv),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    (run (kAdd w inv) m s).phase=s.phase ∧
    (∀q,q∉w 770::wireBlock w 771 257 →
      (run (kAdd w inv) m s).basis q=s.basis q) ∧
    regValue (w 770::wireBlock w 771 257) (run (kAdd w inv) m s).basis=
      (kConstant inv (s.basis (w 1028))+
        regValue (w 770::wireBlock w 771 257) s.basis)%2^258 := by
  have a := kTail_spec w inv s (m.take (measurementCount (kTail w inv))) hn hs hc
  generalize ht : run (kTail w inv) (m.take (measurementCount (kTail w inv))) s=t at a
  have hRun : run (kAdd w inv) m s=
      (⟨t.phase,writeBit t.basis (w 770) (!(t.basis (w 770)))⟩ : State) := by
    rw [kAdd_run,ht]
  have headAway : w 770∉wireBlock w 771 257 := by
    intro h; exact (List.nodup_cons.mp hn).1 (List.mem_append_left _ h)
  have head : t.basis (w 770)=s.basis (w 770) := a.2.1 _ headAway
  rw [hRun]
  dsimp only
  refine ⟨a.1,?_,?_⟩
  · intro q hq
    have parts : q≠w 770 ∧ q∉wireBlock w 771 257 := by
      simpa only [List.mem_cons,not_or] using hq
    have ne := parts.1
    have nt := parts.2
    simpa [writeBit,ne] using a.2.1 q nt
  · rw [toggle_head_value (w 770) (wireBlock w 771 257) t.basis headAway,head,
      a.2.2,cons_value]
    have parity := kConstant_low_one inv (s.basis (w 1028))
    exact (low_one_mod (kConstant inv (s.basis (w 1028)))
      (regValue (wireBlock w 771 257) s.basis) (s.basis (w 770)) parity).trans
        (congrArg (fun z : Nat => z%2^258) (Nat.add_comm _ _))

theorem kAdd_cancel (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hn : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hs : ∀i q,q∈mappedWires (kBits w i) →
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (flag : w 1028∉w 770::wireBlock w 771 257)
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false) :
    run (kAdd w true) mI (run (kAdd w false) mF s)=s := by
  let t := run (kAdd w false) mF s
  have f := kAdd_spec w false s mF hn (hs false) hc
  have away (q : Wire) (hq : q∈wireBlock w 1540 256) :
      q∉w 770::wireBlock w 771 257 := by
    have ne : q≠w 770 := by
      intro h; exact (List.nodup_cons.mp hn).1 (List.mem_append_right _ (h ▸ hq))
    have nt := List.disjoint_right.mp
      (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2 hq
    simp [ne,nt]
  have tclean : ∀q∈wireBlock w 1540 256,t.basis q=false := by
    intro q hq; exact (f.2.1 q (away q hq)).trans (hc q hq)
  have i := kAdd_spec w true t mI hn (hs true) tclean
  have tf : t.basis (w 1028)=s.basis (w 1028) := f.2.1 _ flag
  have sum : (kConstant false (s.basis (w 1028))+
      kConstant true (s.basis (w 1028)))%2^258=0 := by
    cases s.basis (w 1028) <;> decide
  apply state_of_value_frame (w 770::wireBlock w 771 257) s _ (i.1.trans f.1)
  · rw [i.2.2,tf,f.2.2]
    apply mod_add_cancel _ _ _ _ (by positivity) sum
    have bound := regValue_lt (w 770::wireBlock w 771 257) s.basis
    simpa only [List.length_cons,wireBlock_length] using bound
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)
private theorem copy_cancel (src dst : List Wire) (hl : src.length=dst.length)
    (hn : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst) n (run (copyRegister none src dst) m s)=s := by
  have f := copyRegister_correct none src dst hl hn (by simp) s m
  have i := copyRegister_correct none src dst hl hn (by simp)
    (run (copyRegister none src dst) m s) n
  have srcKeep := regValue_congr src (run (copyRegister none src dst) m s).basis s.basis
    (fun q hq => f.2.1 q (List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hq))
  apply state_of_value_frame dst s _ (i.1.trans f.1)
  · rw [i.2.2,f.2.2]
    simp only [copyValue]
    rw [srcKeep,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

private theorem rotate_reverse (r : List Wire) :
    (rotateRight r).reverse=rotateLeft r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      rw [rotateRight,rotateLeft,List.reverse_append,ih]
      rfl
private theorem rotate_proper (r : List Wire) (hn : r.Nodup) :
    ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd := List.nodup_cons.mp hn
      have ne : a≠b := fun h => nd.1 (by simp [h])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩
private theorem rotate_cancel (r : List Wire) (hn : r.Nodup) (s : State) (m n : List Bool) :
    run (rotateLeft r) n (run (rotateRight r) m s)=s := by
  rw [←rotate_reverse]
  exact run_reverse_proper _ (rotate_proper r hn) s m n

def inverseFront (w : Nat → Wire) : Program :=
  [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]++lowCopy w
def inverseBack (w : Nat → Wire) : Program :=
  lowCopy w++[.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)]
def inverseMiddle (w : Nat → Wire) : Program :=
  [.CX (w 1028) (w 770)]++rotateRight (wireBlock w 770 258)
def inverseUnmiddle (w : Nat → Wire) : Program :=
  rotateLeft (wireBlock w 770 258)++[.CX (w 1028) (w 770)]

private theorem front_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (h0 : w 770≠w 1028) (h1 : w 1028≠w 0) :
    run (inverseBack w) n (run (inverseFront w) m s)=s := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  have hp : ProperProgram P := by simp [P,ProperProgram,ProperGate,h0,h1]
  have c := copy_cancel (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) hn (run P m s) m n
  have hm : measurementCount P=0 := properProgram_measurementCount P hp
  have cm := (lowCopy_counts w).2
  change run (lowCopy w++P.reverse) n (run (P++lowCopy w) m s)=s
  rw [run_append,run_take,run_append,run_take,hm,cm,List.drop_zero]
  simp only [List.drop_zero]
  rw [show run (lowCopy w) n (run (lowCopy w) m (run P m s))=run P m s from c]
  exact run_reverse_proper P hp s m n

private theorem middle_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 770 258).Nodup) (hne : w 1028≠w 770) :
    run (inverseUnmiddle w) n (run (inverseMiddle w) m s)=s := by
  rw [inverseUnmiddle,inverseMiddle,run_append,run_take,run_append,run_take,
    (rotate_counts (wireBlock w 770 258)).2.2.2,
    show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero]
  rw [rotate_cancel _ hn]
  exact properGate_involution (.CX (w 1028) (w 770)) hne s m n

/-- The layout conditions concern only physical roles. No forward result or
measurement outcome is assumed in this inverse theorem. -/
theorem inverse_forward (w : Nat → Wire) (s : State) (mF mI : List Bool)
    (hnH : (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup)
    (hnK : (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup)
    (hsH : ∀i q,q∈mappedWires (hBits w i) →
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252))
    (hsK : ∀i q,q∈mappedWires (kBits w i) →
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256))
    (hflag : w 1028∉wireBlock w 4 253)
    (kflag : w 1028∉w 770::wireBlock w 771 257)
    (copyND : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (rotateND : (wireBlock w 770 258).Nodup)
    (ne0 : w 770≠w 1028) (ne1 : w 1028≠w 0)
    (carryAway : ∀q∈wireBlock w 1540 256,
      q∉wires (inverseFront w) ∧ q∉wireBlock w 4 253 ∧ q∉wires (inverseMiddle w))
    (carrySubset : ∀q∈wireBlock w 1540 252,q∈wireBlock w 1540 256)
    (cinAway : w 1797∉wires (inverseFront w))
    (hc : ∀q∈wireBlock w 1540 256,s.basis q=false)
    (cin : s.basis (w 1797)=false) :
    run (inverse w) mI (run (forward w) mF s)=s := by
  let u := run (inverseFront w) mF s
  let v := run (hAdd w false) mF u
  let z := run (inverseMiddle w) (mF.drop 252) v
  have uc : ∀q∈wireBlock w 1540 256,u.basis q=false := by
    intro q hq; exact (run_preserves_outside _ mF s q (carryAway q hq).1).trans (hc q hq)
  have ui : u.basis (w 1797)=false :=
    (run_preserves_outside _ mF s _ cinAway).trans cin
  have ha := hAdd_spec w false u mF hnH (hsH false)
    (fun q hq => uc q (carrySubset q hq))
  have vc : ∀q∈wireBlock w 1540 256,v.basis q=false := by
    intro q hq; exact (ha.2.1 q (carryAway q hq).2.1).trans (uc q hq)
  have zc : ∀q∈wireBlock w 1540 256,z.basis q=false := by
    intro q hq; exact (run_preserves_outside _ _ v q (carryAway q hq).2.2).trans (vc q hq)
  have kc := kAdd_cancel w z (mF.drop 252) mI hnK hsK kflag zc
  have hh := hAdd_cancel w u mF (mI.drop 256) hnH hsH hflag
    (fun q hq => uc q (carrySubset q hq)) ui
  have fm : measurementCount (inverseFront w)=0 := by
    simp [inverseFront,measurementCount_append,measurementCount,(lowCopy_counts w).2]
  have mm : measurementCount (inverseMiddle w)=0 := by
    simp [inverseMiddle,measurementCount_append,measurementCount,(rotate_counts _).2.1]
  have um : measurementCount (inverseUnmiddle w)=0 := by
    simp [inverseUnmiddle,measurementCount_append,measurementCount,(rotate_counts _).2.2.2]
  have fr : forward w=inverseFront w++(hAdd w false++(inverseMiddle w++kAdd w false)) := by
    simp only [forward,inverseFront,inverseMiddle,List.append_assoc]
  have ir : inverse w=kAdd w true++(inverseUnmiddle w++(hAdd w true++inverseBack w)) := by
    simp only [inverse,inverseBack,inverseUnmiddle,List.append_assoc]
  have fRun : run (forward w) mF s=run (kAdd w false) (mF.drop 252) z := by
    rw [fr,run_append,run_take,fm,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w false).2]
    rw [run_append,run_take,mm,List.drop_zero]
  have iRun (t : State) : run (inverse w) mI t=
      run (inverseBack w) ((mI.drop 256).drop 252)
        (run (hAdd w true) (mI.drop 256)
          (run (inverseUnmiddle w) (mI.drop 256) (run (kAdd w true) mI t))) := by
    rw [ir,run_append,run_take,(kAdd_counts w true).2]
    rw [run_append,run_take,um,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w true).2]
  rw [iRun,fRun,kc,middle_cancel w v _ _ rotateND (Ne.symm ne0),hh]
  exact front_cancel w s _ _ copyND ne0 ne1
end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hAdd_cancel
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_spec
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kAdd_cancel
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.inverse_forward
