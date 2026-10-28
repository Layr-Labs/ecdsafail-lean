import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd

/-- Two proved-zero logical sites may exchange their physical names without
emitting a gate. This is a public allocation decision, never an input branch. -/
theorem pullState_zero_swap (a b : Wire) (s : State)
    (ha : s.basis a=false) (hb : s.basis b=false) :
    pullState (Equiv.swap a b) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases hqa : q=a
    · subst q
      simp [pullState,Equiv.swap_apply_def,ha,hb]
    · by_cases hqb : q=b
      · subst q
        simp [pullState,Equiv.swap_apply_def,hqa,ha,hb]
      · simp [pullState,Equiv.swap_apply_def,hqa,hqb]

/-- Rebinding composes the old placement with a swap of clean virtual sites.
Every live value and the incoming phase keep their logical interpretation. -/
theorem cleanWireRebind (f : Wire → Wire) (actual logical : State) (a b : Wire)
    (h : pullState f actual=logical)
    (ha : logical.basis a=false) (hb : logical.basis b=false) :
    pullState (f ∘ Equiv.swap a b) actual=logical := by
  change pullState (Equiv.swap a b) (pullState f actual)=logical
  rw [h,pullState_zero_swap a b logical ha hb]

/-- The next actual instruction block uses the new placement, including all
measurement corrections. Independent records are transported unchanged. -/
theorem run_after_cleanWireRebind (f : Wire → Wire) (hf : Function.Injective f)
    (actual logical : State) (a b : Wire) (p : Program) (m : List Bool)
    (h : pullState f actual=logical)
    (ha : logical.basis a=false) (hb : logical.basis b=false) :
    pullState (f ∘ Equiv.swap a b)
      (run (renameProgram (f ∘ Equiv.swap a b) p) m actual)=run p m logical := by
  have injective : Function.Injective (f ∘ Equiv.swap a b) :=
    hf.comp (Equiv.swap a b).injective
  rw [run_rename _ injective,cleanWireRebind f actual logical a b h ha hb]

/-- The two compiler blocks compose only when their shared boundary proves
both sites clean. No sampled zero or unchecked alias is accepted. -/
theorem twoBlocks_cleanWireRebind (f : Wire → Wire) (hf : Function.Injective f)
    (p q : Program) (mP mQ : List Bool) (actual logical : State) (a b : Wire)
    (h : pullState f actual=logical)
    (ha : (run p mP logical).basis a=false)
    (hb : (run p mP logical).basis b=false) :
    pullState (f ∘ Equiv.swap a b)
      (run (renameProgram (f ∘ Equiv.swap a b) q) mQ
        (run (renameProgram f p) mP actual))=run q mQ (run p mP logical) := by
  have first : pullState f (run (renameProgram f p) mP actual)=run p mP logical := by
    rw [run_rename f hf,h]
  exact run_after_cleanWireRebind f hf _ _ a b q mQ first ha hb

/-- Rebinding changes the placement, not any Toffoli or measurement count. -/
theorem cleanWireRebind_counts (f : Wire → Wire) (a b : Wire) (p : Program) :
    toffoliCount (renameProgram (f ∘ Equiv.swap a b) p)=toffoliCount p ∧
    measurementCount (renameProgram (f ∘ Equiv.swap a b) p)=measurementCount p :=
  renameProgram_counts _ p

end ECDSAAdd
#print axioms ECDSAAdd.pullState_zero_swap
#print axioms ECDSAAdd.cleanWireRebind
#print axioms ECDSAAdd.twoBlocks_cleanWireRebind
#print axioms ECDSAAdd.cleanWireRebind_counts
