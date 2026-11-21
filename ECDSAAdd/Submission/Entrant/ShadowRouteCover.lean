import ECDSAAdd.Submission.Entrant.ShadowRoute

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

def MayTouch (j : Fin 23) (w : Wire) : Prop :=
  (start j + 15 ≤ w ∧ w ≤ start j + 14 + 16 + (Shadow7.shape j).mid + 2) ∨
  (786 ≤ w ∧ w ≤ 787 + (Shadow7.shape j).mid) ∨
  (1556 ≤ w ∧ w ≤ 1556 + (Shadow7.shape j).mid) ∨
  (1044 + start j ≤ w ∧ w < 1044 + start j + 15)

instance (j : Fin 23) (w : Wire) : Decidable (Shadow7.MayTouch j w) := by
  unfold Shadow7.MayTouch
  infer_instance

theorem named_range (j : Fin 23) (a n q : Nat) (lim : a + n ≤ 15)
    (outside : ¬Shadow7.MayTouch j (windowNet j q)) : q ∉ Shadow7.spanSites j a n := by
  intro mem
  obtain ⟨r, hr, inside⟩ := List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp inside
  have undo : windowNet j (windowNet j w) = w := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]
    omega
  rw [undo] at outside
  apply outside
  simp only [ports, SkywalkIntegerLayout.wires, SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh,
    List.mem_cons, List.mem_append, List.mem_range'_1, List.not_mem_nil, or_false,
    Shadow7.shape, Shadow7.smallBits, start] at hw
  simp only [Shadow7.MayTouch, Shadow7.shape, Shadow7.smallBits, start]
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega

theorem through_body (j : Fin 23) (P : Program) (s : State) (m : List Bool) (q : Nat)
    (free : ¬Shadow7.MayTouch j (windowNet j q))
    (admin : let a := run (Shadow7.routed j 0 1) m s
      (run P (m.drop (measurementCount (Shadow7.routed j 0 1))) a).basis q = a.basis q) :
    (run (Shadow7.body j P) m s).basis q = s.basis q := by
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) q (Shadow7.named_range j 1 14 q (by decide) free) _ _).trans
    (admin.trans (Shadow7.route_outside j 0 1 (by decide) q (Shadow7.named_range j 0 1 q (by decide) free) s m))

theorem body_cover (j : Fin 23) (P : Program) (controls effects : List Wire)
    (clean : ∀ q ∈ controls, ¬Shadow7.MayTouch j (windowNet j q))
    (apart : ∀ q ∈ controls, q ∉ effects) (cover : wires P ⊆ effects.toFinset)
    (s : State) (m : List Bool) (q : Wire) (hit : q ∈ controls) :
    (run (Shadow7.body j P) m s).basis q = s.basis q :=
  Shadow7.through_body j P s m q (clean q hit) (run_preserves_outside P _ _ q
    (fun used => apart q hit (List.mem_toFinset.mp (cover used))))

theorem ext_head (P : Program) (j : Fin 23) (Q : Program) (effects : List Wire)
    (s : State) (m n : List Bool) (q : Wire) (native : ¬Shadow7.MayTouch j (windowNet j q))
    (enter : q ∉ wires P) (admin : q ∉ effects) (cover : wires Q ⊆ effects.toFinset) :
    (run (Shadow7.body j Q) n (run P m s)).basis q = s.basis q :=
  (Shadow7.through_body j Q _ n q native (run_preserves_outside Q _ _ q
    (fun used => admin (List.mem_toFinset.mp (cover used))))).trans (run_preserves_outside P _ _ q enter)

theorem sig_tail (j : Fin 23) (h21 : j.val ≤ 21) (q : Wire)
    (lo : Shadow7.e0P (start j) + 6 ≤ q) (hi : q + start j ≤ 2054)
    (i : Nat) (ile : i ≤ start j + 14) : OB5.sig i q = q := by
  have top : start j ≤ 390 := by simp only [start]; omega
  apply WideReference.sig_fixed
  · intro band
    simp only [Shadow7.e0P] at lo
    simp only [Wire] at band
    omega
  · intro mirror
    simp only [Wire] at hi mirror
    omega

section
open MappedCompressed
attribute [local irreducible] run SkywalkIntegerLayout.wires

def firstUnchanged (j : Fin 23) (q : Wire) : Prop :=
  let r := windowNet j q
  r = (ports (Shadow7.shape j) 0).previous ∨ r ∉ (ports (Shadow7.shape j) 0).wires

instance (j : Fin 23) (q : Wire) : Decidable (Shadow7.firstUnchanged j q) := by
  unfold Shadow7.firstUnchanged
  infer_instance

theorem first_preserves (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a + z.b) % 2 = 1)
    (s : State) (m : List Bool) (ready : Shadow7.onRails j 0 z s.basis)
    (q : Wire) (free : Shadow7.firstUnchanged j q) : (run (Shadow7.routed j 0 1) m s).basis q = s.basis q := by
  let p := Shadow7.shape j
  let L := ports p 0
  let virt := pullState (windowNet j) s
  let v := windowNet j q
  have first : 0 < p.length := by
    change 0 < 15
    decide
  have inv : windowNet j v = q := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]
    omega
  have step := Shadow7.pull_routed j 0 1 (by decide) m s
  simp only [seq, List.append_nil] at step
  have at_q := congrArg (fun x : State => x.basis v) step
  change (run (Shadow7.routed j 0 1) m s).basis (windowNet j v) =
    (run (skywalkIntegerTick L) m virt).basis v at at_q
  rw [inv] at at_q
  refine at_q.trans (Eq.trans ?_ (show virt.basis v = s.basis q from congrArg s.basis inv))
  rcases free with e | e
  · change v = L.previous at e
    rw [e]
    obtain ⟨ha, hb, hg, hc, hnew⟩ := ready
    obtain ⟨he, hh⟩ := hnew 0 (by decide) first
    obtain ⟨_, _, _, _, _, prev, _⟩ :=
      executed p ⟨0, first⟩ _ _ _ odd virt m ⟨ha, hb, hg, he, hh, hc⟩
    exact prev.trans hg.symm
  · apply run_preserves_outside
    exact fun used => e (List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok p ⟨0, first⟩)).1 used))

end

section
open ArchivePortAction
attribute [local irreducible] run measurementCount

theorem body_keeps (j : Fin 23) (P : Program) (ps : Ports) (d : Bool) (row : Nat)
    (s : State) (m : List Bool) (off : ∀ i : Fin 16, ps ⟨i.val, by omega⟩ ∉ Shadow7.spanSites j 1 14)
    (hold : Frame ps (code d) row (run P (m.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) m s))) : Kept ps d row (run (Shadow7.body j P) m s) := by
  intro i
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) _ (off i) _ _).trans (hold ⟨i.val, by omega⟩)

theorem after_encoded (j : Fin 23) (P : Program) (outPorts : Ports) (d : Bool) (row : Nat)
    (src : State) (m : List Bool)
    (final : Frame outPorts (code d) row (run P (m.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) m src)))
    (i : Fin 157) (hi : 16 ≤ i.val) (q : Wire) (slot : outPorts i = q)
    (free : ¬Shadow7.MayTouch j (windowNet j q)) : (run (Shadow7.body j P) m src).basis q = false := by
  simp only [Shadow7.body, run_append, run_take]
  apply (Shadow7.route_outside j 1 14 (by decide) q (Shadow7.named_range j 1 14 q (by decide) free) _ _).trans
  rw [←slot, final, archive_blank _ _ hi, Nat.zero_testBit]

end

end ECDSAAdd.Entrant.StairPacket.Shadow7
