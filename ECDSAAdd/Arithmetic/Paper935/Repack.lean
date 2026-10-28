import ECDSAAdd.Arithmetic.Paper935.Borrow
import ECDSAAdd.Arithmetic.Rotate

namespace ECDSAAdd.Arithmetic.Paper935

/-- Move a row's occupied physical site into a clean home-band slot, using
exactly the three-CX swap emitted by the author's repacker. -/
def rehome (old fresh : Wire) : Program := swapBits old fresh

theorem rehome_run (old fresh : Wire) (hn : old≠fresh) (s : State) (m : List Bool) :
    let t := run (rehome old fresh) m s
    t.phase=s.phase ∧ ∀ q,t.basis (Equiv.swap old fresh q)=s.basis q := by
  constructor
  · rfl
  · intro q
    by_cases ho : q=old
    · subst q
      cases ha : s.basis old <;> cases hb : s.basis fresh <;>
        simp [rehome,swapBits,run,writeBit,hn,Ne.symm hn,ha,hb]
    · by_cases hf : q=fresh
      · subst q
        cases ha : s.basis old <;> cases hb : s.basis fresh <;>
          simp [rehome,swapBits,run,writeBit,hn,Ne.symm hn,ha,hb]
      · simp [rehome,swapBits,run,writeBit,Equiv.swap_apply_def,ho,hf]

theorem rehome_row (old fresh : Wire) (hn : old≠fresh) (row : List Wire)
    (s : State) (m : List Bool) :
    signedRegValue (row.map (Equiv.swap old fresh)) (run (rehome old fresh) m s).basis=
      signedRegValue row s.basis := by
  have h := (rehome_run old fresh hn s m).2
  have hv : regValue (row.map (Equiv.swap old fresh)) (run (rehome old fresh) m s).basis=
      regValue row s.basis := by
    induction row with
    | nil => rfl
    | cons q qs ih =>
      simp only [regValue] at ih
      simp only [List.map_cons,regValue,List.foldr_cons,h,ih]
  unfold signedRegValue
  rw [List.length_map,hv]

theorem rehome_roundtrip (old fresh : Wire) (hn : old≠fresh) (s : State) (m n : List Bool) :
    run (rehome old fresh) n (run (rehome old fresh) m s)=s := by
  have h1 := rehome_run old fresh hn s m
  have h2 := rehome_run old fresh hn (run (rehome old fresh) m s) n
  apply congrArg₂ State.mk
  · exact h2.1.trans h1.1
  · funext q
    have hh := h2.2 (Equiv.swap old fresh q)
    simpa only [Equiv.swap_apply_self] using hh.trans (h1.2 q)

theorem rehome_distinct (old fresh : Wire) (rows : List Wire) (hn : rows.Nodup) :
    (rows.map (Equiv.swap old fresh)).Nodup := hn.map (Equiv.swap old fresh).injective

theorem rehome_clean (old fresh : Wire) (hn : old≠fresh) (s : State) (m : List Bool)
    (hz : s.basis fresh=false) : (run (rehome old fresh) m s).basis old=false := by
  simpa using ((rehome_run old fresh hn s m).2 fresh).trans hz

theorem rehome_support (old fresh : Wire) : wires (rehome old fresh)={old,fresh} := by
  ext q
  simp [rehome,swapBits,wires,Instr.wires]
  tauto

theorem rehome_cost (old fresh : Wire) :
    toffoliCount (rehome old fresh)=0 ∧ measurementCount (rehome old fresh)=0 := ⟨rfl,rfl⟩

/-- The source and destination coexist in `during`; the transient peak is
therefore charged before the old site is released. -/
theorem rehome_allocated (A during : Arena) (old fresh : Wire) (s : State) (m : List Bool)
    (ho : old∈A.live) (hr : A.Ready s.basis) (hres : A.reserve {fresh}=some during) :
    ∃ B, during.release {old} (run (rehome old fresh) m s).basis=some B ∧
      B.Ready (run (rehome old fresh) m s).basis ∧
      wires (rehome old fresh)⊆during.live ∧ during.live.card≤935 := by
  have hv := (A.reserve_success {fresh}).mp ⟨during,hres⟩
  have hnew : fresh∉A.live := fun h => Finset.disjoint_left.mp hv.2 h (by simp)
  have hn : old≠fresh := fun h => hnew (h ▸ ho)
  have hb := A.reserve_ready during {fresh} s.basis hr hres
  have hz := hb.2 fresh (by simp)
  have hd : during.live=A.live∪{fresh} := by
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at hres
    cases hres
    rfl
  have hold : old∈during.live := by rw [hd]; exact Finset.mem_union_left _ ho
  have hfresh : fresh∈during.live := by simp [hd]
  have hclean : during.Ready (run (rehome old fresh) m s).basis := by
    intro q hq hnot
    have hqo : q≠old := fun h => hnot (h ▸ hold)
    have hqf : q≠fresh := fun h => hnot (h ▸ hfresh)
    have hf := (rehome_run old fresh hn s m).2 q
    simp only [Equiv.swap_apply_def,hqo,hqf,if_false] at hf
    rw [hf]
    exact hb.1 q hq hnot
  obtain ⟨B,hB⟩ := (during.release_success {old} _).mpr
    ⟨by simpa using hold,by simpa using rehome_clean old fresh hn s m hz⟩
  refine ⟨B,hB,during.release_ready B {old} _ hclean hB,?_,during.peak_bound⟩
  rw [rehome_support]
  intro q hq
  simp only [Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl <;> assumption

/-- Connect the executable band-priority chooser to the physical move. -/
theorem rehome_selected (A during : Arena) (pools : List (Finset Wire))
    (old fresh : Wire) (s : State) (m : List Bool)
    (ho : old∈A.live) (hr : A.Ready s.basis)
    (hsel : A.borrowFirst pools=some (during,fresh)) :
    ∃ B, during.release {old} (run (rehome old fresh) m s).basis=some B ∧
      B.Ready (run (rehome old fresh) m s).basis ∧
      wires (rehome old fresh)⊆during.live ∧ during.live.card≤935 := by
  exact rehome_allocated A during old fresh s m ho hr
    (A.borrowFirst_ready during pools fresh s.basis hr hsel).2.2

/-- Replay a fixed, public relocation journal; choices do not branch on
quantum data. Allocation/cleanliness must be certified separately. -/
def repack : List (Wire × Wire) → Program
  | [] => []
  | (old,fresh)::moves => rehome old fresh ++ repack moves

def repackView : List (Wire × Wire) → List Wire → List Wire
  | [],row => row
  | (old,fresh)::moves,row => repackView moves (row.map (Equiv.swap old fresh))

def unpack : List (Wire × Wire) → Program
  | [] => []
  | (old,fresh)::moves => unpack moves ++ rehome old fresh

theorem repack_measurements (moves : List (Wire × Wire)) : measurementCount (repack moves)=0 := by
  induction moves with
  | nil => rfl
  | cons p ps ih => simp [repack,measurementCount_append,rehome_cost,ih]

theorem unpack_measurements (moves : List (Wire × Wire)) : measurementCount (unpack moves)=0 := by
  induction moves with
  | nil => rfl
  | cons p ps ih => simp [unpack,measurementCount_append,rehome_cost,ih]

theorem repack_rows (moves : List (Wire × Wire))
    (hn : ∀ p∈moves,p.1≠p.2) (row : List Wire) (s : State) (m : List Bool) :
    signedRegValue (repackView moves row) (run (repack moves) m s).basis=signedRegValue row s.basis := by
  induction moves generalizing row s with
  | nil => rfl
  | cons p ps ih =>
    have hp := hn p (by simp)
    have ht : ∀ q∈ps,q.1≠q.2 := fun q hq => hn q (by simp [hq])
    simp only [repack,repackView,run_append,(rehome_cost p.1 p.2).2,List.take_zero,List.drop_zero]
    exact (ih ht _ _).trans (rehome_row p.1 p.2 hp row s [])

theorem repack_roundtrip (moves : List (Wire × Wire))
    (hn : ∀ p∈moves,p.1≠p.2) (s : State) (m n : List Bool) :
    run (unpack moves) n (run (repack moves) m s)=s := by
  induction moves generalizing s m n with
  | nil => rfl
  | cons p ps ih =>
    have hp := hn p (by simp)
    have ht : ∀ q∈ps,q.1≠q.2 := fun q hq => hn q (by simp [hq])
    simp only [repack,unpack,run_append,(rehome_cost p.1 p.2).2,
      unpack_measurements,List.take_zero,List.drop_zero]
    rw [ih ht]
    exact rehome_roundtrip p.1 p.2 hp s [] n

theorem repack_toffolis (moves : List (Wire × Wire)) : toffoliCount (repack moves)=0 := by
  induction moves with
  | nil => rfl
  | cons p ps ih => simp [repack,toffoliCount_append,rehome_cost,ih]

theorem repackView_distinct (moves : List (Wire × Wire)) (row : List Wire) (hn : row.Nodup) :
    (repackView moves row).Nodup := by
  induction moves generalizing row with
  | nil => exact hn
  | cons p ps ih => exact ih _ (rehome_distinct p.1 p.2 row hn)

theorem repack_in_arena (moves : List (Wire × Wire))
    (h : ∀ p∈moves,p.1∈arenaWires ∧ p.2∈arenaWires) : wires (repack moves)⊆arenaWires := by
  induction moves with
  | nil => simp [repack,wires]
  | cons p ps ih =>
    rw [repack,wires_append]
    apply Finset.union_subset
    · rw [rehome_support]
      have hp := h p (by simp)
      intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hp.1
      · exact hp.2
    · exact ih (fun q hq => h q (by simp [hq]))

end ECDSAAdd.Arithmetic.Paper935
