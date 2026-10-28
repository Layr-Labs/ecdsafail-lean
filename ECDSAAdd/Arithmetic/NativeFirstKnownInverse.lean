import ECDSAAdd.Arithmetic.NativeFirstKnownFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect
attribute [local irreducible] run mappedAdd hAdd kAdd kTail NativeFirstDirect.forward NativeFirstDirect.inverse inverse hReceiver

private theorem copy_away (w : Nat → Wire) (q : Wire)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (lowCopy w) := by
  rw [lowCopy,copyRegister_wires none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length])]
  split_ifs
  · simp
  · simpa only [Option.toList_none,List.nil_append,List.mem_toFinset,
      List.mem_append,not_or] using And.intro hs hd

private theorem front_away (w : Nat → Wire) (q : Wire)
    (h0 : q≠w 0) (hb : q≠w 770) (he : q≠w 1028)
    (hs : q∉wireBlock w 771 255) (hd : q∉wireBlock w 1 255) :
    q∉wires (inverseFront w) := by
  have flags : q∉wires [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [wires,Instr.wires,h0,hb,he]
  rw [inverseFront,wires_append,Finset.mem_union,not_or]
  exact ⟨flags,copy_away w q hs hd⟩

private theorem middle_away (w : Nat → Wire) (q : Wire)
    (hb : q≠w 770) (he : q≠w 1028) (hr : q∉wireBlock w 770 258) :
    q∉wires (inverseMiddle w) := by
  have first : q∉wires [.CX (w 1028) (w 770)] := by
    simp [wires,Instr.wires,hb,he]
  have rot : q∉wires (rotateRight (wireBlock w 770 258)) := by
    rw [(rotate_wires (wireBlock w 770 258)).1]
    split_ifs
    · simp
    · simpa only [List.mem_toFinset] using hr
  rw [inverseMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨first,rot⟩

private theorem state_of_value_frame (r : List Wire) (s t : State)
    (hp : t.phase=s.phase) (hv : regValue r t.basis=regValue r s.basis)
    (he : ∀q,q∉r → t.basis q=s.basis q) : t=s := by
  apply congrArg₂ State.mk hp
  funext q
  by_cases hq : q∈r
  · exact (regValue_eq_iff r _ _).mp hv q hq
  · exact he q hq

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


theorem inverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (NativeFirstKnown.inverse w) mI (run (NativeFirstDirect.forward w) mF s)=s := by
  let u := run (inverseFront w) mF s
  let v := run (hAdd w false) mF u
  let z := run (inverseMiddle w) (mF.drop 252) v
  have initialCarry : regValue (wireBlock w 1540 257) s.basis=0 := ready.carry
  have clean : ∀q∈wireBlock w 1540 256,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp initialCarry q
      (block_subset w 1540 256 257 (by omega) q hq)
  have aClean : regValue (wireBlock w 1 256) s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    have initialA : regValue (wireBlock w 0 258) s.basis=0 := ready.a
    exact (regValue_zero _ _).mp initialA _
      (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
  have frontCarryAway : ∀q∈wireBlock w 1540 256,q∉wires (inverseFront w) := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact front_away w (w j)
      (index_ne w hn j 0 (by omega) (by omega) (by omega))
      (index_ne w hn j 770 (by omega) (by omega) (by omega))
      (index_ne w hn j 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 1 255 (by omega) (by omega) (by omega))
  have uc : ∀q∈wireBlock w 1540 256,u.basis q=false := by
    intro q hq
    exact (run_preserves_outside _ mF s q (frontCarryAway q hq)).trans (clean q hq)
  have ui : u.basis (w 1797)=false := by
    apply Eq.trans (run_preserves_outside _ mF s _ ?_) ready.cin
    exact front_away w (w 1797)
      (index_ne w hn 1797 0 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 770 (by omega) (by omega) (by omega))
      (index_ne w hn 1797 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 771 255 (by omega) (by omega) (by omega))
      (block_not_mem w hn 1797 1 255 (by omega) (by omega) (by omega))
  have ha := hAdd_spec w false u mF (h_inputs_nd w hn)
    (h_sources_fresh w hn false)
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq))
  have vc : ∀q∈wireBlock w 1540 256,v.basis q=false := by
    intro q hq
    have away : q∉wireBlock w 4 253 :=
      List.disjoint_right.mp
        (block_disjoint w hn 4 253 1540 256 (by omega) (by omega) (by omega)) hq
    exact (ha.2.1 q away).trans (uc q hq)
  have zc : ∀q∈wireBlock w 1540 256,z.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have away := middle_away w (w j)
      (index_ne w hn j 770 (by omega) (by omega) (by omega))
      (index_ne w hn j 1028 (by omega) (by omega) (by omega))
      (block_not_mem w hn j 770 258 (by omega) (by omega) (by omega))
    exact (run_preserves_outside _ _ v _ away).trans (vc _
      (List.mem_map.mpr ⟨j,by simpa only [List.mem_range'_1] using hj,rfl⟩))
  have kflag : w 1028∉w 770::wireBlock w 771 257 := by
    simp only [List.mem_cons,not_or]
    exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
      block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega)⟩
  have kc := kAdd_cancel w z (mF.drop 252) mI (k_inputs_nd w hn)
    (fun i => k_sources_fresh w hn i) kflag zc
  have mc := middle_cancel w v (mF.drop 252) (mI.drop 256)
    (block_nodup w hn 770 258 (by omega))
    (index_ne w hn 1028 770 (by omega) (by omega) (by omega))
  have hh := hReceiver_after_forward w hn u mF (mI.drop 256)
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq)) ui
    (front_known_sum w hn s mF aClean)
  have fm : measurementCount (inverseFront w)=0 := by
    simp [inverseFront,measurementCount_append,measurementCount,(lowCopy_counts w).2]
  have mm : measurementCount (inverseMiddle w)=0 := by
    simp [inverseMiddle,measurementCount_append,measurementCount,(rotate_counts _).2.1]
  have um : measurementCount (inverseUnmiddle w)=0 := by
    simp [inverseUnmiddle,measurementCount_append,measurementCount,(rotate_counts _).2.2.2]
  have fr : NativeFirstDirect.forward w=
      inverseFront w++(hAdd w false++(inverseMiddle w++kAdd w false)) := by
    simp only [NativeFirstDirect.forward,inverseFront,inverseMiddle,List.append_assoc]
  have ir : NativeFirstKnown.inverse w=
      kAdd w true++(inverseUnmiddle w++(hReceiver w++inverseBack w)) := by
    simp only [NativeFirstKnown.inverse,List.append_assoc]
  have fRun : run (NativeFirstDirect.forward w) mF s=
      run (kAdd w false) (mF.drop 252) z := by
    rw [fr,run_append,run_take,fm,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w false).2]
    rw [run_append,run_take,mm,List.drop_zero]
  have iRun (t : State) : run (NativeFirstKnown.inverse w) mI t=
      run (inverseBack w) ((mI.drop 256).drop 252)
        (run (hReceiver w) (mI.drop 256)
          (run (inverseUnmiddle w) (mI.drop 256) (run (kAdd w true) mI t))) := by
    rw [ir,run_append,run_take,(kAdd_counts w true).2]
    rw [run_append,run_take,um,List.drop_zero]
    rw [run_append,run_take,(hReceiver_counts w).2]
  rw [iRun,fRun,kc,mc,hh]
  exact front_cancel w s _ _ (copy_inputs_nd w hn)
    (index_ne w hn 770 1028 (by omega) (by omega) (by omega))
    (index_ne w hn 1028 0 (by omega) (by omega) (by omega))

/-- Convenient replacement equality only on the clean forward image. -/
theorem inverse_eq_old_on_forward (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x : Nat) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (NativeFirstKnown.inverse w) mI (run (NativeFirstDirect.forward w) mF s)=
      run (NativeFirstDirect.inverse w) mI (run (NativeFirstDirect.forward w) mF s) := by
  rw [inverse_roundtrip w hn x s mF mI ready,
    NativeFirstDirect.inverse_forward_ready w hn x s mF mI ready]

theorem inverse_restore_after_outside (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x : Nat)
    (initial field : State) (mF mI : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x initial.basis)
    (hphase : field.phase=(run (NativeFirstDirect.forward w) mF initial).phase)
    (hpool : ∀q∈skywalkPoolWires w,
      field.basis q=(run (NativeFirstDirect.forward w) mF initial).basis q) :
    (run (NativeFirstKnown.inverse w) mI field).phase=initial.phase ∧
    (∀q∈skywalkPoolWires w,
      (run (NativeFirstKnown.inverse w) mI field).basis q=initial.basis q) ∧
    (∀q,q∉skywalkPoolWires w →
      (run (NativeFirstKnown.inverse w) mI field).basis q=field.basis q) := by
  have support : wires (NativeFirstKnown.inverse w)⊆(skywalkPoolWires w).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (prefix_pool_subset w
      (List.mem_toFinset.mp (NativeFirstKnown.inverse_support w hq)))
  have restored := inverse_roundtrip w hn x initial mF mI hin
  have agrees := pool_run_agrees (NativeFirstKnown.inverse w)
    (skywalkPoolWires w).toFinset support mI
    field (run (NativeFirstDirect.forward w) mF initial) hphase
    (fun q hq => hpool q (List.mem_toFinset.mp hq))
  rw [restored] at agrees
  refine ⟨agrees.1,?_,?_⟩
  · intro q hq
    exact agrees.2 q (List.mem_toFinset.mpr hq)
  · intro q hq
    exact run_preserves_outside (NativeFirstKnown.inverse w) mI field q
      (fun h => hq (List.mem_toFinset.mp (support h)))

end ECDSAAdd.Arithmetic.NativeFirstKnown
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.inverse_roundtrip
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.inverse_eq_old_on_forward
#print axioms ECDSAAdd.Arithmetic.NativeFirstKnown.inverse_restore_after_outside
