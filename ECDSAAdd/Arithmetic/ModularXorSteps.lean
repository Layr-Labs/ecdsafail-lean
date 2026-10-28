import ECDSAAdd.Arithmetic.ExternalMod

namespace ECDSAAdd.Arithmetic.ExternalMod

theorem mod_add (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (X O q : Nat) (v : ModField → Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (hxy : v .x + v .y < 2*q)
    (hc : ∀ f, f ≠ .x → f ≠ .y → f ≠ .out → v f = 0) :
    Triple (Values L src dst X O v) (modAdd L q)
      (Values L src dst X O (Function.update v .out (v .out ^^^ ((v .x+v .y)%q)))) := by
  intro s m hv
  obtain ⟨hs, hd⟩ := external_disjoint src dst L hnd
  have hl : L.wires.Nodup := (List.nodup_append'.mp hnd).2.1
  obtain ⟨hp, he, hz⟩ := modAdd_bounded_correct L hl q hq0 hq s m
    (by simpa only [show regValue L.x s.basis = v .x from hv.2.2.1 .x,
      show regValue L.y s.basis = v .y from hv.2.2.1 .y] using hxy)
    (work_zero L v s.basis hv.2.2 hc)
  refine ⟨hp, ?_, ?_, ModValues.update L hl v .out _ s.basis _ hv.2.2 he ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w (fun h => List.disjoint_left.mp hs hw
      (field_subset L .out h)))).trans hv.1
  · exact (regValue_congr _ _ _ (fun w hw => he w (fun h => List.disjoint_left.mp hd hw
      (field_subset L .out h)))).trans hv.2.1
  · simpa only [show regValue L.x s.basis = v .x from hv.2.2.1 .x,
      show regValue L.y s.basis = v .y from hv.2.2.1 .y,
      show regValue L.out s.basis = v .out from hv.2.2.1 .out] using hz

theorem mod_sub (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (X O q : Nat) (v : ModField → Nat)
    (hq0 : 0 < q) (hq : q < 2^L.width) (hx : v .x < q) (hy : v .y < q)
    (hc : ∀ f, f ≠ .x → f ≠ .y → f ≠ .out → v f = 0) :
    Triple (Values L src dst X O v) (modSub L q)
      (Values L src dst X O (Function.update v .out (v .out ^^^ ((v .x+q-v .y)%q)))) := by
  intro s m hv
  obtain ⟨hs, hd⟩ := external_disjoint src dst L hnd
  have hl : L.wires.Nodup := (List.nodup_append'.mp hnd).2.1
  obtain ⟨hp, he, hz⟩ := modSub_correct L hl q hq0 hq s m
    (by simpa only [show regValue L.x s.basis = v .x from hv.2.2.1 .x] using hx)
    (by simpa only [show regValue L.y s.basis = v .y from hv.2.2.1 .y] using hy)
    (work_zero L v s.basis hv.2.2 hc)
  refine ⟨hp, ?_, ?_, ModValues.update L hl v .out _ s.basis _ hv.2.2 he ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w (fun h => List.disjoint_left.mp hs hw
      (field_subset L .out h)))).trans hv.1
  · exact (regValue_congr _ _ _ (fun w hw => he w (fun h => List.disjoint_left.mp hd hw
      (field_subset L .out h)))).trans hv.2.1
  · simpa only [show regValue L.x s.basis = v .x from hv.2.2.1 .x,
      show regValue L.y s.basis = v .y from hv.2.2.1 .y,
      show regValue L.out s.basis = v .out from hv.2.2.1 .out] using hz

end ECDSAAdd.Arithmetic.ExternalMod
