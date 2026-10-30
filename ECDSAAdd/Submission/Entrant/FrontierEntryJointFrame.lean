import ECDSAAdd.Submission.Entrant.FrontierEntryJointProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField

private theorem outside_layout (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem joint_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (joint L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layout L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (EntryRetained5.program L J G)
    (m.take (measurementCount (EntryRetained5.program L J G))) a=t
  have result := EntryRetained5.program_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (EntryRetained5.program L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (joint L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [joint,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]

end ECDSAAdd.Entrant.FrontierEntry
