import ECDSAAdd.Arithmetic.Divsteps.DeferredSwapWalk

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Controls retained between steps when swap is measured and reused. -/
def StepHistory.retained (h : StepHistory) : List Wire := [h.active,h.parity]

/-- Static allocation for one shared swap and distinct activity/parity histories.
Old past histories are excluded: the schedule starts at this layout. -/
def StepLayout.sharedUsed (L : StepLayout) : List Wire :=
  (L.data++L.work) ++ (L.history.swap ::
    (L.history::L.future).flatMap StepHistory.retained)

/-- A local step view. Empty past/future fields are intentional: those controls
are framed by the schedule rather than included in local uniqueness. -/
def StepLayout.sharedAt (L : StepLayout) (i : Nat) : StepLayout :=
  { L.at i with
    history := { (L.at i).history with swap := L.history.swap }
    past := []
    future := [] }

theorem StepLayout.at_base_perm (L : StepLayout) (i : Nat) :
    ((L.at i).data++(L.at i).work).Perm (L.data++L.work) := by
  induction i with
  | zero => exact List.Perm.refl _
  | succ i ih =>
    have hr := (L.at i).g.halfView_perm
    have hh : ((L.at i).halfView.data++(L.at i).halfView.work).Perm
        ((L.at i).data++(L.at i).work) := by
      unfold data work halfView
      dsimp only
      exact (((((List.Perm.refl _).append hr).append_right _).append_right _).append_right _).append
        (((List.Perm.refl _).append (hr.map (L.at i).detect)).append_right _)
    rw [StepLayout.at]
    unfold next nextHistory
    split <;> exact hh.trans ih

/-- Selection never invents a history record, including after exhaustion. -/
theorem StepLayout.at_history_mem (L : StepLayout) (i : Nat) :
    (L.at i).history∈L.history::L.future ∧ (L.at i).future⊆L.future := by
  induction i with
  | zero => simp [StepLayout.at]
  | succ i ih =>
    rw [StepLayout.at]
    unfold next nextHistory halfView
    dsimp only
    split
    · exact ih
    · rename_i h rest he
      constructor
      · exact List.mem_cons_of_mem _ (ih.2 (by simp [he]))
      · intro a ha
        exact ih.2 (by simp [he,ha])

private theorem retained_sublist (h : StepHistory) : h.retained.Sublist h.wires := by
  simp [StepHistory.retained,StepHistory.wires]

private theorem retained_flat_sublist (hs : List StepHistory) :
    (hs.flatMap StepHistory.retained).Sublist (hs.flatMap StepHistory.wires) := by
  induction hs with
  | nil => exact List.Sublist.refl _
  | cons h hs ih => exact (retained_sublist h).append ih

theorem StepLayout.sharedUsed_nodup (L : StepLayout) (h : L.Valid) : L.sharedUsed.Nodup := by
  have hs : ((L.data++L.work)++L.history.wires++L.future.flatMap StepHistory.retained).Sublist
      L.used := by
    unfold used histories
    simp only [List.append_assoc]
    exact (List.Sublist.refl _).append ((List.Sublist.refl _).append
      ((List.Sublist.refl _).append
        ((retained_flat_sublist L.future).trans (List.sublist_append_right _ _))))
  have hp : L.sharedUsed.Perm
      ((L.data++L.work)++L.history.wires++L.future.flatMap StepHistory.retained) := by
    apply List.perm_iff_count.mpr
    intro w
    simp [sharedUsed,StepHistory.retained,StepHistory.wires,List.count_append,List.count_cons]
    omega
  exact hp.nodup_iff.mpr (h.unique.sublist hs)

theorem StepLayout.sharedAt_valid (L : StepLayout) (h : L.Valid) (i : Nat) :
    (L.sharedAt i).Valid := by
  have hi := L.at_valid h i
  have hn := L.sharedUsed_nodup h
  have hm := (L.at_history_mem i).1
  have hsub : (L.at i).history.retained.Sublist
      ((L.history::L.future).flatMap StepHistory.retained) := by
    obtain ⟨a,b,he⟩ := List.mem_iff_append.mp hm
    rw [he]
    simp only [List.flatMap_append,List.flatMap_cons]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  have hp := (L.at_base_perm i).append (List.Perm.refl
    (L.history.swap :: (L.history::L.future).flatMap StepHistory.retained))
  have hn' := hp.nodup_iff.mpr hn
  have hs : (((L.at i).data++(L.at i).work) ++
      (L.history.swap::(L.at i).history.retained)).Nodup :=
    hn'.sublist ((List.Sublist.refl _).append (hsub.cons₂ _))
  have hu : (L.sharedAt i).used.Perm
      (((L.at i).data++(L.at i).work) ++
       (L.history.swap::(L.at i).history.retained)) := by
    apply List.perm_iff_count.mpr
    intro w
    simp [sharedAt,used,data,work,histories,StepHistory.wires,StepHistory.retained,
      List.count_append,List.count_cons]
    omega
  exact ⟨hu.nodup_iff.mpr hs,hi.integers,hi.coefficients,hi.mask_g,hi.mask_v,hi.mask_z,
    hi.carry_g,hi.carry_v,hi.carry_z⟩


theorem StepLayout.sharedAt_support (L : StepLayout) (i : Nat) :
    (L.sharedAt i).used.toFinset ⊆ L.sharedUsed.toFinset := by
  intro w hw
  have hm := (L.at_history_mem i).1
  have hr : ∀ u∈(L.at i).history.retained,
      u∈(L.history::L.future).flatMap StepHistory.retained := by
    intro u hu
    exact List.mem_flatMap.mpr ⟨_,hm,hu⟩
  simp only [List.mem_toFinset,sharedAt,used,data,work,histories,
    List.flatMap_nil,List.append_nil,StepHistory.wires,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hw
  have hb := (L.at_base_perm i).mem_iff (a := w)
  simp only [data,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  simp only [List.mem_toFinset,sharedUsed,List.mem_append,List.mem_cons]
  rcases hw with hw | hw
  · apply Or.inl
    simpa only [data,work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using hb.mp hw
  · rcases hw with ha | hp | hq
    · exact Or.inr (Or.inr (hr w (by simp [StepHistory.retained,ha])))
    · exact Or.inr (Or.inr (hr w (by simp [StepHistory.retained,hp])))
    · exact Or.inr (Or.inl hq)

theorem StepLayout.sharedAt_sized (L : StepLayout) (n v k : Nat) (hw : L.Sized n v k)
    (i : Nat) : (L.sharedAt i).Sized n v k := L.at_sized n v k hw i

theorem StepLayout.sharedUsed_length (L : StepLayout) :
    L.sharedUsed.length=L.data.length+L.work.length+1+2*(1+L.future.length) := by
  have hh (hs : List StepHistory) : (hs.flatMap StepHistory.retained).length=2*hs.length := by
    induction hs with
    | nil => rfl
    | cons a as ih => simp [StepHistory.retained,ih]; omega
  simp [sharedUsed,hh,StepHistory.retained]
  omega


theorem StepLayout.sharedUsed_sized_length (L : StepLayout) (h : L.Valid)
    (n v k : Nat) (hw : L.Sized n v k) :
    L.sharedUsed.length=3*n+2*v+k+L.mask.length+L.carry.length+5+2*L.future.length := by
  rw [sharedUsed_length]
  simp only [data,work,List.length_append,List.length_map,List.length_cons,List.length_nil,
    h.integers,h.coefficients,hw.1,hw.2.1,hw.2.2]
  omega

/-- Compare allocation bounds, not exact touched-wire cardinalities. Past
storage is omitted and each future triple loses its separate swap address. -/
theorem StepLayout.sharedUsed_saving (L : StepLayout) (h : L.Valid) :
    L.sharedUsed.length+3*L.past.length+L.future.length=L.used.length := by
  rw [L.used_length h,L.sharedUsed_sized_length h _ _ _ ⟨rfl,rfl,rfl⟩]
  omega

/-- A concrete schedule with two fresh transitions and one shared swap wire. -/
def sharedSwapExample : StepLayout :=
  { stepLayoutExample with future := [⟨24,25,26⟩,⟨27,28,29⟩] }

theorem sharedSwapExample_valid : sharedSwapExample.Valid := by
  constructor <;> decide

theorem sharedSwapExample_layout :
    (sharedSwapExample.sharedAt 0).history.swap=23 ∧
    (sharedSwapExample.sharedAt 1).history.swap=23 ∧
    (sharedSwapExample.sharedAt 2).history.swap=23 ∧
    sharedSwapExample.sharedUsed.length=28 ∧ sharedSwapExample.used.length=30 := by decide

end ECDSAAdd.Arithmetic.Divsteps
