import ECDSAAdd.Math.Divsteps.Recovery
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Divsteps

/-- Route both row pairs first, then share one signed add/halve kernel.
The swap case negates the second routed row before adding the first. -/
def routedStep (s : ZState) : ZState :=
  let swap := decide (0 ≤ s.z ∧ s.g % 2 = 1)
  let f := if swap then s.g else s.f
  let g := if swap then s.f else s.g
  let fv := if swap then s.gv else s.fv
  let gv := if swap then s.fv else s.gv
  let b := s.g % 2
  ⟨if swap then -s.z else s.z + 1,
    f, ((if swap then -g else g) + b * f) / 2,
    2 * fv, (if swap then -gv else gv) + b * fv⟩

theorem routedStep_eq (s : ZState) : routedStep s = zStep s := by
  by_cases h : 0 ≤ s.z ∧ s.g % 2 = 1
  · simp [routedStep, zStep, h, sub_eq_add_neg, add_comm]
  · simp [routedStep, zStep, h]

end ECDSAAdd.Divsteps

namespace ECDSAAdd.Arithmetic.Divsteps

/-- One controlled swap of concatenated rows shares the swap control and
uses no scratch register. Equal pair widths keep the field boundaries aligned. -/
def routeRows (c : Wire) (f g fv gv : List Wire) : Program :=
  swapRegisters c (f ++ fv) (g ++ gv)

private theorem split_word_eq (a b c d : List Wire) (s t : BasisState)
    (hlen : a.length = c.length)
    (h : regValue (a ++ b) s = regValue (c ++ d) t) :
    regValue a s = regValue c t ∧ regValue b s = regValue d t := by
  rw [regValue_append, regValue_append, ← hlen] at h
  have hl := congrArg (fun n => n % 2^a.length) h
  have ha := regValue_lt a s
  have hc := regValue_lt c t
  rw [← hlen] at hc
  simp [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at hl
  refine ⟨hl, ?_⟩
  have hm : 2^a.length * regValue b s = 2^a.length * regValue d t := by omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hm

theorem routeRows_correct (c : Wire) (f g fv gv : List Wire)
    (hfg : f.length = g.length) (hv : fv.length = gv.length)
    (hnd : (c :: ((f ++ fv) ++ (g ++ gv))).Nodup)
    (s : State) (m : List Bool) :
    (run (routeRows c f g fv gv) m s).phase = s.phase ∧
    (∀ i, i ∉ f ++ fv → i ∉ g ++ gv →
      (run (routeRows c f g fv gv) m s).basis i = s.basis i) ∧
    regValue f (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then regValue g s.basis else regValue f s.basis) ∧
    regValue g (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then regValue f s.basis else regValue g s.basis) ∧
    regValue fv (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then regValue gv s.basis else regValue fv s.basis) ∧
    regValue gv (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then regValue fv s.basis else regValue gv s.basis) := by
  have hlen : (f ++ fv).length = (g ++ gv).length := by simp [hfg, hv]
  obtain ⟨hp, he, hf, hg⟩ := swapRegisters_correct c (f ++ fv) (g ++ gv) hlen hnd s m
  refine ⟨hp, he, ?_⟩
  cases hb : s.basis c <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at *
  · obtain ⟨hff, hvf⟩ := split_word_eq f fv f fv _ _ rfl hf
    obtain ⟨hgg, hvg⟩ := split_word_eq g gv g gv _ _ rfl hg
    exact ⟨hff, hgg, hvf, hvg⟩
  · obtain ⟨hff, hvf⟩ := split_word_eq f fv g gv _ _ hfg hf
    obtain ⟨hgg, hvg⟩ := split_word_eq g gv f fv _ _ hfg.symm hg
    exact ⟨hff, hgg, hvf, hvg⟩

theorem routeRows_counts (c : Wire) (f g fv gv : List Wire)
    (hfg : f.length = g.length) (hv : fv.length = gv.length)
    (hnd : (c :: ((f ++ fv) ++ (g ++ gv))).Nodup) :
    toffoliCount (routeRows c f g fv gv) = f.length + fv.length ∧
    measurementCount (routeRows c f g fv gv) = 0 := by
  have h := swapRegisters_resources c (f ++ fv) (g ++ gv) (by simp [hfg, hv]) hnd
  simpa [routeRows] using And.intro h.1 h.2.1

/-- Routing is also exact for signed rows because corresponding widths agree. -/
theorem routeRows_signed (c : Wire) (f g fv gv : List Wire)
    (hfg : f.length = g.length) (hv : fv.length = gv.length)
    (hnd : (c :: ((f ++ fv) ++ (g ++ gv))).Nodup)
    (s : State) (m : List Bool) :
    signedRegValue f (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then signedRegValue g s.basis else signedRegValue f s.basis) ∧
    signedRegValue g (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then signedRegValue f s.basis else signedRegValue g s.basis) ∧
    signedRegValue fv (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then signedRegValue gv s.basis else signedRegValue fv s.basis) ∧
    signedRegValue gv (run (routeRows c f g fv gv) m s).basis =
      (if s.basis c then signedRegValue fv s.basis else signedRegValue gv s.basis) := by
  obtain ⟨_, _, hf, hg, hfv, hgv⟩ := routeRows_correct c f g fv gv hfg hv hnd s m
  simp only [signedRegValue, hf, hg, hfv, hgv]
  cases hb : s.basis c <;> simp [hfg, hv]

theorem routeRows_qubits (c : Wire) (f g fv gv : List Wire)
    (hfg : f.length = g.length) (hv : fv.length = gv.length)
    (hnd : (c :: ((f ++ fv) ++ (g ++ gv))).Nodup) :
    qubitCount (routeRows c f g fv gv) =
      (if (f ++ fv).isEmpty then 0 else 2*(f.length + fv.length)+1) := by
  simpa [routeRows] using
    (swapRegisters_resources c (f ++ fv) (g ++ gv) (by simp [hfg, hv]) hnd).2.2

end ECDSAAdd.Arithmetic.Divsteps
