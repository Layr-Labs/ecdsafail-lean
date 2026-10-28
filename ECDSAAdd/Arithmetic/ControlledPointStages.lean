import ECDSAAdd.Arithmetic.ControlledPointOutput

namespace ECDSAAdd.Arithmetic
open Secp256k1

def PointControl (L : ControlledPointLayout) (b : Bool) (s : BasisState) : Prop :=
  s L.control=b ∧ s L.genericSelect=false ∧ s L.doubleSelect=false ∧ s L.infinitySelect=false

theorem pointControl_frame (L : ControlledPointLayout) (hn : L.wires.Nodup) (b : Bool)
    {P Q : BasisState → Prop} {c : Program} (hc : Triple P c Q)
    (hw : wires c⊆L.core.wires.toFinset) :
    Triple (fun s => P s ∧ PointControl L b s) c (fun s => Q s ∧ PointControl L b s) := by
  apply hc.frame
  intro s t he hb
  have hh (w : Wire) (hm : w∈L.extras) : t w=s w :=
    (he w (fun hm' => L.extra_not_core hn w hm (List.mem_toFinset.mp (hw hm')))).symm
  simpa only [PointControl,hh L.control (by simp [ControlledPointLayout.extras]),
    hh L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    hh L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    hh L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])] using hb

theorem ControlledPointLayout.candidate_subset (L : ControlledPointLayout) (h : L.Widths) :
    L.core.candidateUsed.toFinset⊆L.core.wires.toFinset := by
  intro w hw
  have hp : w∈candidatePool L.core.poolWire → w∈L.core.pool := fun hh => (L.core.candidatePool_sublist h).subset hh
  simp only [List.mem_toFinset,PointAddLayout.candidateUsed,PointAddLayout.extendedX,
    PointAddLayout.extendedY,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [List.mem_toFinset,PointAddLayout.wires,PointAddLayout.pointWires,
    PointAddLayout.work,PointAddLayout.words,PointAddLayout.flags,List.flatten_cons,List.flatten_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with (((((((((((((((hx|hxh)|(hy|hyh))|hdx)|hdy)|hs)|hsq)|ho)|hcx)|hd)|hp)|hcy)|hk)|hdv)|hi)|hg)|hw
  all_goals try { subst w; simp }
  all_goals try { have hh := List.mem_of_mem_take hdx; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hcy; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hdy; simp_all only [true_or,or_true] }
  all_goals try { have hh := List.mem_of_mem_take hd; simp_all only [true_or,or_true] }
  all_goals simp_all only [true_or,or_true]

theorem ControlledPointLayout.flags_subset (L : ControlledPointLayout) :
    (L.core.input.finite::L.core.input.x++L.core.input.y++L.core.flags++L.core.pool.take 256).toFinset⊆L.core.wires.toFinset := by
  intro w hw
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at hw
  have hp : w∈L.core.pool.take 256 → w∈L.core.pool := List.mem_of_mem_take
  rcases hw with (((hf|hx)|hy)|hflags)|hpool
  all_goals simp_all [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work]

theorem controlledPointStage_output (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (b : Bool) (R : Point) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy)
    (OF : Bool) (OX OY : Nat) :
    let C : Point := .some hc
    let V := candidateResult (pointGeneric R cx) (pointX R) (pointY R) cx.val cy.val
    Triple (fun s => PointStage L.core R cx cy OF OX OY V s ∧ PointControl L b s)
      (controlledPointOutput L C)
      (fun s => PointStage L.core R cx cy (OF^^(b&&pointFinite (R+C)))
        (OX^^^(if b then pointX (R+C) else 0)) (OY^^^(if b then pointY (R+C) else 0)) V s ∧ PointControl L b s) := by
  dsimp only
  intro s m hs
  obtain ⟨⟨hv,hb⟩,hctrl⟩ := hs
  have hh := controlledPointOutput_correct L h hn (.some hc) s m hctrl.2
  have hx := h.words L.core.candidateX (by simp [PointAddLayout.words])
  have hy := h.words L.core.candidateY (by simp [PointAddLayout.words])
  have hbnd := candidateResult_xy_lt (pointGeneric R cx) (pointX R) (pointY R) cx cy
    (point_coordinates_lt R).1 (point_coordinates_lt R).2
  have hlow (r : List Wire) (hr : r.length=257) (V : Nat) (hV : V<p)
      (hv : regValue r s.basis=V) : regValue (r.take 256) s.basis=V := by
    have ht := regValue_low_iff (r.take 256) (r.drop 256) s.basis V
      (by simp only [List.length_take,hr]; exact lt_trans hV (by norm_num [p]))
    rw [List.take_append_drop] at ht
    exact (ht.mp hv).1
  have hX := hlow L.core.candidateX hx _ hbnd.1 (hv.1 .x)
  have hY := hlow L.core.candidateY hy _ hbnd.2 (hv.1 .y)
  rw [hX,hY,hv.2.2,hb.finite,hb.double,hctrl.1] at hh
  have he := point_classification_xor R cx cy hc
  dsimp only at he
  have heF := congrArg Prod.fst he
  have heX := congrArg (fun t => t.2.1) he
  have heY := congrArg (fun t => t.2.2) he
  dsimp only at heF heX heY
  rw [heF,heX,heY] at hh
  have ep (w : Wire) (hw : w∈L.extras) := hh.outside w (L.extra_not_output hn w hw)
  refine ⟨hh.phase,⟨hv.pointOutput (L.core_nodup hn) hh,hb.pointOutput (L.core_nodup hn) hh⟩,?_⟩
  simpa only [PointControl,ep L.control (by simp [ControlledPointLayout.extras]),
    ep L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    ep L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors]),
    ep L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])] using hctrl

end ECDSAAdd.Arithmetic
