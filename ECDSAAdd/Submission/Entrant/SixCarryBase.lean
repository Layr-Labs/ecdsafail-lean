import ECDSAAdd.Submission.Entrant.LowAccMiddleLiteral
namespace ECDSAAdd.Entrant
open ECDSAAdd Arithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace SixCarryTrace
def basisStep : Instr → BasisState → BasisState
 | .X t, b => writeBit b t (!b t)
 | .CX a t, b => writeBit b t (b t ^^ b a)
 | .CCX a c t, b => writeBit b t (b t ^^ (b a && b c))
 | .measureX t _ _, b => writeBit b t false

def basisRun : Program → BasisState → BasisState
 | [], b => b
 | i::p,b => basisRun p (basisStep i b)

theorem run_basis (p : Program) (m : List Bool) (s : State) :
 (run p m s).basis = basisRun p s.basis := by
 induction p generalizing m s with
 | nil => rfl
 | cons i p ih => cases i <;> simp [run,basisRun,basisStep,ih,measureAndCorrect]

theorem basisRun_append (p q : Program) (b : BasisState) :
 basisRun (p++q) b = basisRun q (basisRun p b) := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih => simp [basisRun,ih]

def stripPhase : Instr → Instr
 | .measureX q _ _ => .measureX q [] []
 | i => i

theorem basisRun_stripPhase (p : Program) (b : BasisState) :
 basisRun (p.map stripPhase) b = basisRun p b := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih => cases i <;> simp [basisRun,stripPhase,ih,basisStep]


end SixCarryTrace
namespace SixCarryFrame
open SixCarryTrace
def target : Instr → Wire
 | .X q => q
 | .CX _ q => q
 | .CCX _ _ q => q
 | .measureX q _ _ => q

theorem basisStep_preserves (i : Instr) (b : BasisState) (q : Wire) (h : target i ≠ q) :
 basisStep i b q = b q := by
 have hrev := Ne.symm h
 cases i <;> simp_all [target,basisStep,writeBit]

theorem basisRun_preserves (p : Program) (b : BasisState) (q : Wire)
 (h : ∀ i ∈ p, target i ≠ q) : basisRun p b q = b q := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih =>
  change basisRun p (basisStep i b) q = b q
  rw [ih _ (fun j hj => h j (by simp [hj]))]
  exact basisStep_preserves i b q (h i (by simp))

def prefixState (p : Program) (i : Nat) (b : BasisState) : BasisState := basisRun (p.take i) b

theorem at_succ (p : Program) (i : Nat) (hi : i < p.length) (b : BasisState) :
 prefixState p (i+1) b = basisStep p[i] (prefixState p i b) := by
 simp only [prefixState,List.take_succ_eq_append_getElem hi,basisRun_append,basisRun]

def noWriteBetween (p : Program) (i j : Nat) (q : Wire) : Bool :=
 ((p.drop i).take (j-i)).all (fun ins => decide (target ins ≠ q))

theorem at_between (p : Program) (i j : Nat) (q : Wire) (hij : i ≤ j)
 (hn : noWriteBetween p i j q = true) (b : BasisState) :
 prefixState p j b q = prefixState p i b q := by
 unfold prefixState
 rw [show j = i+(j-i) from by omega,List.take_add,basisRun_append]
 apply basisRun_preserves
 intro ins hins
 exact of_decide_eq_true (List.all_eq_true.mp hn ins hins)

theorem at_full (p : Program) (b : BasisState) : prefixState p p.length b = basisRun p b := by
 simp only [prefixState,List.take_length]


end SixCarryFrame
namespace SixCarryReplace
theorem old_shape_of_lookup (p : Program) (i : Nat) (g : Instr)
 (h : p[i]? = some g) : p = p.take i ++ ([g] ++ p.drop (i+1)) := by
 obtain ⟨hi,hg⟩ := List.getElem?_eq_some_iff.mp h
 have hd := List.drop_eq_getElem_cons hi
 rw [hg] at hd
 exact (List.take_append_drop i p).symm.trans (congrArg (fun q => p.take i ++ q) hd)

end SixCarryReplace
namespace SixCarryReplacement
theorem state_ext {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
 cases s
 cases t
 cases hp
 cases hb
 rfl

end SixCarryReplacement
namespace SixCarrySupport
theorem replacement_support (pre old new post : Program)
 (hs : wires new ⊆ wires (pre ++ (old ++ post))) :
 wires (pre ++ (new ++ post)) ⊆ wires (pre ++ (old ++ post)) := by
 intro w hw
 simp only [wires_append,Finset.mem_union] at hw ⊢
 rcases hw with h | h | h
 · exact Or.inl h
 · have hh:=hs h; simpa only [wires_append,Finset.mem_union] using hh
 · exact Or.inr (Or.inr h)

theorem replacement_physical (pre old new post : Program)
 (hp : GatePhysical (pre ++ (old ++ post))) (hn : GatePhysical new) :
 GatePhysical (pre ++ (new ++ post)) := by
 simp only [gatePhysical_append] at hp ⊢
 exact ⟨hp.1,hn,hp.2.2⟩

end SixCarrySupport
namespace SixCarryResource
theorem slots_append (p q : Program) : Challenge.gateSlots (p++q)=Challenge.gateSlots p+Challenge.gateSlots q := by
 simp [Challenge.gateSlots,List.map_append,List.sum_append]
end SixCarryResource
end ECDSAAdd.Entrant
