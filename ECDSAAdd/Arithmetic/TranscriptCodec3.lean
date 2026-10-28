import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Arithmetic.TranscriptCodec3

-- Pinned incumbent codec, including its measurement phase correction.
def pack : Program := [
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 2,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 0 5,
  .CX 0 4,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 0 4,
  .CX 0 5,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 3 5,
  .CX 4 0,
  .CX 4 2,
  .CX 4 5,
  .CX 4 2,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 2 1,
  .CX 1 4,
  .CX 1 2,
  .CX 0 3,
  .CX 0 1,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 0 1,
  .CX 0 3,
  .CX 1 2,
  .CX 1 4,
  .CX 2 1,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 4 2,
  .CX 3 1,
  .CX 3 2,
  .measureX 3 [] [.CZ 1 0]
]

def unpack : Program := [
  .CX 3 2,
  .CX 3 1,
  .CX 3 2,
  .CX 2 3,
  .CX 3 2,
  .CX 1 3,
  .CX 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 1 2,
  .CX 1 3,
  .CX 3 2,
  .CX 2 3,
  .CX 3 2,
  .CX 3 1,
  .CX 3 2,
  .CX 4 2,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 2 1,
  .CX 1 4,
  .CX 1 2,
  .CX 0 3,
  .CX 0 1,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 0 1,
  .CX 0 3,
  .CX 1 2,
  .CX 1 4,
  .CX 2 1,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 4 2,
  .CX 4 5,
  .CX 4 2,
  .CX 4 0,
  .CX 3 5,
  .CX 3 4,
  .CX 3 2,
  .CX 3 0,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 0 5,
  .CX 0 4,
  .CX 0 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CCX 0 1 2,
  .CX 1 0,
  .CX 0 1,
  .CX 1 0,
  .CX 0 2,
  .CX 0 4,
  .CX 0 5,
  .CX 3 1,
  .CX 1 3,
  .CX 3 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 0,
  .CX 3 2,
  .CX 3 4,
  .CX 3 5,
  .CX 4 0,
  .CX 4 2,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 3 4,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .X 0,
  .X 1,
  .CCX 0 1 2,
  .X 1,
  .X 0,
  .CX 3 0,
  .CX 0 3,
  .CX 3 0,
  .CX 4 1,
  .CX 1 4,
  .CX 4 1,
  .CX 4 2,
  .CX 2 4,
  .CX 4 2,
  .CX 3 4,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4
]

def raw (a b c d e f : Bool) : BasisState := fun q =>
  if q=0 then a else if q=1 then b else if q=2 then c else
    if q=3 then d else if q=4 then e else if q=5 then f else false

def legal (s : BasisState) : Prop :=
  (s 0 && s 1)=false ∧ (s 2 && s 3)=false ∧ (s 4 && s 5)=false

def kernel : Program := pack ++ unpack

theorem counts : toffoliCount pack=3 ∧ measurementCount pack=1 ∧
    toffoliCount unpack=4 ∧ measurementCount unpack=0 := by decide

theorem support : wires pack=Finset.range 6 ∧ wires unpack=Finset.range 6 := by decide

-- Finite kernel theorem, covering all legal words, measurement outcomes,
-- missing/default measurement records, and both incoming phases.
theorem finite_interface : ∀ (a b c d e f ph : Bool) (record : Option Bool),
    legal (raw a b c d e f) →
    (run pack record.toList ⟨ph,raw a b c d e f⟩).phase=ph ∧
    (run pack record.toList ⟨ph,raw a b c d e f⟩).basis 3=false ∧
    (run kernel record.toList ⟨ph,raw a b c d e f⟩).phase=ph ∧
    ∀ q : Fin 6, (run kernel record.toList ⟨ph,raw a b c d e f⟩).basis q=
      raw a b c d e f q := by unfold legal; decide

attribute [local irreducible] run pack unpack kernel

private theorem records (p : Program) (hm : measurementCount p=1)
    (m : List Bool) (s : State) : run p m s=run p m.head?.toList s := by
  rw [← run_take p m s,hm]
  cases m <;> rfl

theorem fixed_correct (s : State) (m : List Bool) (h : legal s.basis) :
    (run pack m s).phase=s.phase ∧ (run pack m s).basis 3=false ∧
    run kernel m s=s := by
  let t : State := ⟨s.phase,raw (s.basis 0) (s.basis 1) (s.basis 2)
    (s.basis 3) (s.basis 4) (s.basis 5)⟩
  have hb : ∀ q∈Finset.range 6,s.basis q=t.basis q := by
    intro q hq
    have hq6 := Finset.mem_range.mp hq
    interval_cases q <;> simp [t,raw]
  have ht : legal t.basis := by simpa [t,legal,raw] using h
  have finite := finite_interface (s.basis 0) (s.basis 1) (s.basis 2)
    (s.basis 3) (s.basis 4) (s.basis 5) s.phase m.head? ht
  have hs : wires kernel=Finset.range 6 := by
    simp only [kernel,wires_append,support.1,support.2,Finset.union_self]
  have hc : measurementCount kernel=1 := by
    simp only [kernel,measurementCount_append,counts.2.1,counts.2.2.2,Nat.add_zero]
  have pp := pool_run_agrees pack (Finset.range 6) (by rw [support.1]) m s t rfl hb
  have kk := pool_run_agrees kernel (Finset.range 6) (by rw [hs]) m s t rfl hb
  have pk : run pack m t=run pack m.head?.toList t := records pack counts.2.1 m t
  have rk : run kernel m t=run kernel m.head?.toList t := records kernel hc m t
  refine ⟨pp.1.trans ?_,(pp.2 3 (by decide)).trans ?_,?_⟩
  · rw [pk]; exact finite.1
  · rw [pk]; exact finite.2.1
  · have ph : (run kernel m s).phase=s.phase := by
      rw [kk.1,rk]; exact finite.2.2.1
    have bits : (run kernel m s).basis=s.basis := by
      funext q
      by_cases hq : q<6
      · have kq := kk.2 q (Finset.mem_range.mpr hq)
        rw [rk] at kq
        exact kq.trans ((finite.2.2.2 ⟨q,hq⟩).trans (hb q (Finset.mem_range.mpr hq)).symm)
      · apply run_preserves_outside
        rw [hs]; simpa using hq
    exact State.extensionality _ _ ph bits

/-- Relabeling this six-site component also preserves the caller's phase.
An injective map forbids silent aliases between raw transcript sites. -/
theorem placed_roundtrip (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legal (pullState f s).basis) :
    (run (renameProgram f pack) m s).phase=s.phase ∧
    (run (renameProgram f pack) m s).basis (f 3)=false ∧
    pullState f (run (renameProgram f kernel) m s)=pullState f s := by
  have hc := fixed_correct (pullState f s) m h
  have hp := run_rename f hf pack m s
  have hk := run_rename f hf kernel m s
  refine ⟨?_,?_,hk.trans hc.2.2⟩
  · exact (congrArg State.phase hp).trans hc.1
  · exact (congrArg (fun st : State => st.basis 3) hp).trans hc.2.1

/-- Full caller state, including every unrelated register, is restored.
This is stronger than equality of only the six transcript bits. -/
theorem placed_state (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (h : legal (pullState f s).basis) :
    run (renameProgram f kernel) m s=s := by
  have hc := (placed_roundtrip f hf s m h).2.2
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase hc
  · funext q
    by_cases hq : q∈wires (renameProgram f kernel)
    · rw [renameProgram_support] at hq
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      simpa only [pullState] using congrArg (fun st : State => st.basis j) hc
    · exact run_preserves_outside _ _ _ q hq

end ECDSAAdd.Arithmetic.TranscriptCodec3
