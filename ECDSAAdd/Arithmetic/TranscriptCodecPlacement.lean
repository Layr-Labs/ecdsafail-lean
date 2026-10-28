import ECDSAAdd.Arithmetic.TranscriptCodec3

namespace ECDSAAdd.Arithmetic.TranscriptCodec3

/-- A six-site placement is extended to a permutation of all wire labels.
The caller's history sites lie above the six local template labels. -/
def placement (w : Fin 6 → Wire) : Equiv.Perm Wire :=
  (Equiv.swap 0 (w 0)).trans ((Equiv.swap 1 (w 1)).trans
    ((Equiv.swap 2 (w 2)).trans ((Equiv.swap 3 (w 3)).trans
      ((Equiv.swap 4 (w 4)).trans (Equiv.swap 5 (w 5))))))

theorem placement_apply (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (i : Fin 6) : placement w i=w i := by
  have small (i : Fin 6) (j : Nat) (hj : j<6) : w i≠j := by
    exact Ne.symm (ne_of_lt (lt_of_lt_of_le hj (hlo i)))
  have revSmall (j : Nat) (hj : j<6) (i : Fin 6) : j≠w i :=
    Ne.symm (small i j hj)
  fin_cases i <;> simp [placement,Equiv.swap_apply_def,hn.eq_iff,small,revSmall]

def encode (w : Fin 6 → Wire) : Program := renameProgram (placement w) pack
def decode (w : Fin 6 → Wire) : Program := renameProgram (placement w) unpack

theorem placement_counts (w : Fin 6 → Wire) :
    toffoliCount (encode w)=3 ∧ measurementCount (encode w)=1 ∧
    toffoliCount (decode w)=4 ∧ measurementCount (decode w)=0 := by
  have hp := renameProgram_counts (placement w) pack
  have hu := renameProgram_counts (placement w) unpack
  exact ⟨hp.1.trans counts.1,hp.2.trans counts.2.1,
    hu.1.trans counts.2.2.1,hu.2.trans counts.2.2.2⟩

theorem placement_sites (w : Fin 6 → Wire) :
    qubitCount (encode w)=6 ∧ qubitCount (decode w)=6 := by
  simp only [qubitCount,encode,decode,renameProgram_support,support.1,support.2,
    Finset.card_image_of_injective _ (placement w).injective,Finset.card_range]
  exact ⟨True.intro,True.intro⟩

/-- Exact compressed-history interface on six distinct caller sites. The
fourth site is clean after encode, and decode restores the whole caller state. -/
theorem placement_correct (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (s : State) (m : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    (run (encode w) m s).phase=s.phase ∧
    (run (encode w) m s).basis (w 3)=false ∧
    run (encode w++decode w) m s=s := by
  have hi : legal (pullState (placement w) s).basis := by
    unfold legal pullState
    dsimp only
    have h0 := placement_apply w hn hlo 0
    have h1 := placement_apply w hn hlo 1
    have h2 := placement_apply w hn hlo 2
    have h3 := placement_apply w hn hlo 3
    have h4 := placement_apply w hn hlo 4
    have h5 := placement_apply w hn hlo 5
    change placement w (0 : Wire)=w 0 at h0
    change placement w (1 : Wire)=w 1 at h1
    change placement w (2 : Wire)=w 2 at h2
    change placement w (3 : Wire)=w 3 at h3
    change placement w (4 : Wire)=w 4 at h4
    change placement w (5 : Wire)=w 5 at h5
    rw [h0,h1,h2,h3,h4,h5]
    exact hraw
  have c := placed_roundtrip (placement w) (placement w).injective s m hi
  have state := placed_state (placement w) (placement w).injective s m hi
  have h3 : placement w 3=w 3 := placement_apply w hn hlo 3
  refine ⟨c.1,?_,?_⟩
  · change (run (renameProgram (placement w) pack) m s).basis (w 3)=false
    rw [← h3]
    exact c.2.1
  · simpa only [encode,decode,kernel,renameProgram,List.map_append] using state

private theorem decode_records (w : Fin 6 → Wire) (s : State) (m : List Bool) :
    run (decode w) m s=run (decode w) [] s := by
  rw [← run_take (decode w) m s,(placement_counts w).2.2.2]
  rfl

/-- The decoder uses no measurements. Its record is independent of the
encoder's record, including when either supplied list is empty. -/
theorem decode_encode (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (s : State) (mE mD : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    run (decode w) mD (run (encode w) mE s)=s := by
  have h := (placement_correct w hn hlo s mE hraw).2.2
  rw [run_append] at h
  rw [run_take] at h
  rw [decode_records] at h
  rw [decode_records]
  exact h

def window (w : Fin 6 → Wire) (body : Program) : Program :=
  decode w ++ body ++ encode w

theorem window_counts (w : Fin 6 → Wire) (body : Program) :
    toffoliCount (window w body)=toffoliCount body+7 ∧
    measurementCount (window w body)=measurementCount body+1 := by
  have hc := placement_counts w
  simp only [window,toffoliCount_append,measurementCount_append,hc.1,hc.2.1,
    hc.2.2.1,hc.2.2.2]
  constructor <;> omega

/-- A decoded field window executes the original body on the original caller
state, then re-encodes its output. No arithmetic oracle is introduced. -/
theorem window_states (w : Fin 6 → Wire) (hn : Function.Injective w)
    (hlo : ∀ i,6≤w i) (body : Program) (s : State) (m0 m1 m2 m3 : List Bool)
    (hraw : (s.basis (w 0) && s.basis (w 1))=false ∧
      (s.basis (w 2) && s.basis (w 3))=false ∧
      (s.basis (w 4) && s.basis (w 5))=false) :
    run (encode w) m3 (run body m2 (run (decode w) m1 (run (encode w) m0 s)))=
      run (encode w) m3 (run body m2 s) := by
  rw [decode_encode w hn hlo s m0 m1 hraw]

end ECDSAAdd.Arithmetic.TranscriptCodec3
