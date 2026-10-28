import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- Clifford-only sign workspace update, used both to seed the signed
arithmetic control and to turn it into the reversible sign-flip history. -/
def skywalkSignToggle (a b t : Wire) : Program := [.X t,.CX a t,.CX b t]

theorem skywalkSignToggle_correct (a b t : Wire) (ha : a≠t) (hb : b≠t)
    (s : State) (m : List Bool) :
    run (skywalkSignToggle a b t) m s=
      ⟨s.phase,writeBit s.basis t ((!s.basis t) ^^ s.basis a ^^ s.basis b)⟩ := by
  simp only [skywalkSignToggle,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=t
  · subst w
    simp only [writeBit,Function.update_self,Function.update_of_ne ha,
      Function.update_of_ne hb]
  · simp [writeBit,Function.update,hw]

theorem skywalkSignToggle_spec (a b t : Wire) (ha : a≠t) (hb : b≠t)
    (A B T : Bool) :
    {{ a=A,b=B,t=T }} skywalkSignToggle a b t
    {{ a=A,b=B,t=((!T) ^^ A ^^ B) }} := by
  intro s m h
  simp only [Holds.holds] at h
  rw [skywalkSignToggle_correct a b t ha hb]
  refine ⟨rfl,⟨?_,?_⟩,?_⟩
  · simpa [Holds.holds,writeBit,ha] using h.1.1
  · simpa [Holds.holds,writeBit,hb] using h.1.2
  · simp [Holds.holds,writeBit,h.2,h.1.1,h.1.2]

theorem skywalkSignToggle_counts (a b t : Wire) :
    toffoliCount (skywalkSignToggle a b t)=0 ∧
    measurementCount (skywalkSignToggle a b t)=0 := by
  simp [skywalkSignToggle,toffoliCount,measurementCount]

theorem skywalkSignToggle_wires (a b t : Wire) :
    wires (skywalkSignToggle a b t)=[a,b,t].toFinset := by
  ext q
  simp [skywalkSignToggle,wires,Instr.wires]
  tauto

/-- Equality/zero signs require no exceptional correction: these identities
hold for every Boolean combination of source, old target and new target signs. -/
theorem skywalkSignToggle_seed (H O : Bool) :
    ((!false) ^^ H ^^ O)=(!(H ^^ O)) := by cases H <;> cases O <;> rfl

theorem skywalkSignToggle_finish (H O N : Bool) :
    ((!(!(H ^^ O))) ^^ H ^^ N)=(O ^^ N) := by
  cases H <;> cases O <;> cases N <;> rfl

theorem skywalkSignToggle_recover (H O N : Bool) :
    ((!(O ^^ N)) ^^ H ^^ N)=(!(H ^^ O)) := by
  cases H <;> cases O <;> cases N <;> rfl

theorem skywalkSignToggle_clear (H O : Bool) :
    ((!(!(H ^^ O))) ^^ H ^^ O)=false := by cases H <;> cases O <;> rfl

end ECDSAAdd.Arithmetic
