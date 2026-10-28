import ECDSAAdd.Arithmetic.PointCopyProof

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem negativePointConstant_correct (c : Wire) (r : PointReg) (C : Point)
    (hn : (PointAddLayout.pointWires r).Nodup) (hc : c∉PointAddLayout.pointWires r)
    (hx : r.x.length=256) (hy : r.y.length=256) (s : State) (m : List Bool) :
    PointEffect r ((!s.basis c) && pointFinite C)
      (if !s.basis c then pointX C else 0) (if !s.basis c then pointY C else 0) s
      (run (negativePointConstant c r C) m s) := by
  let u : State := ⟨s.phase,writeBit s.basis c (!s.basis c)⟩
  let v := run (maskedPointConstant c r C) m u
  have he := maskedPointConstant_correct c r C hn hc hx hy u m
  have hcF : r.finite≠c := fun h => hc (by simp [PointAddLayout.pointWires,← h])
  have hcX : ∀ w∈r.x,w≠c := fun w hw h => hc (by simp [PointAddLayout.pointWires,← h,hw])
  have hcY : ∀ w∈r.y,w≠c := fun w hw h => hc (by simp [PointAddLayout.pointWires,← h,hw])
  have hu (w : Wire) (hw : w≠c) : u.basis w=s.basis w := by simp [u,writeBit,hw]
  have hux : regValue r.x u.basis=regValue r.x s.basis := regValue_congr _ _ _ (fun w hw => hu w (hcX w hw))
  have huy : regValue r.y u.basis=regValue r.y s.basis := regValue_congr _ _ _ (fun w hw => hu w (hcY w hw))
  have huc : u.basis c= !s.basis c := by simp [u,writeBit]
  rw [negativePointConstant,run_append,run_take,run_append,run_take]
  simp only [measurementCount,List.drop_zero]
  change PointEffect r _ _ _ s (run [.X c] _ v)
  simp only [run]
  refine ⟨he.phase,?_,?_,?_,?_⟩
  · intro w hw
    by_cases hwc : w=c
    · subst w; simp [writeBit,show v.basis c=u.basis c from he.outside c hc,huc]
    · simp only [writeBit,Function.update_of_ne hwc]
      exact (he.outside w hw).trans (hu w hwc)
  · simp only [writeBit,Function.update_of_ne hcF]
    rw [he.finite,huc,hu _ hcF]
  · have hvx : regValue r.x (writeBit v.basis c (!v.basis c))=regValue r.x v.basis := by
      apply regValue_congr; intro w hw; simp [writeBit,hcX w hw]
    rw [hvx,he.x,hux,huc]
  · have hvy : regValue r.y (writeBit v.basis c (!v.basis c))=regValue r.y v.basis := by
      apply regValue_congr; intro w hw; simp [writeBit,hcY w hw]
    rw [hvy,he.y,huy,huc]

theorem pointOutput_correct (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.output
      (s.basis L.generic ^^ (s.basis L.double && pointFinite (C+C)) ^^ (!s.basis L.input.finite && pointFinite C))
      ((if s.basis L.generic then regValue (L.candidateX.take 256) s.basis else 0) ^^^
        (if s.basis L.double then pointX (C+C) else 0) ^^^ (if !s.basis L.input.finite then pointX C else 0))
      ((if s.basis L.generic then regValue (L.candidateY.take 256) s.basis else 0) ^^^
        (if s.basis L.double then pointY (C+C) else 0) ^^^ (if !s.basis L.input.finite then pointY C else 0)) s
      (run (pointOutput L C) m s) := by
  have ha := (L.output_interfaces hn).2.2
  have hr := (List.nodup_cons.mp (List.nodup_cons.mp ha).2).2
  have hd : L.double∉PointAddLayout.pointWires L.output := (List.nodup_cons.mp (List.nodup_cons.mp ha).2).1
  have hf : L.input.finite∉PointAddLayout.pointWires L.output :=
    fun hw => (List.nodup_cons.mp ha).1 (List.mem_cons_of_mem _ hw)
  let u := run (pointGenericOutput L) m s
  have e0 := pointGenericOutput_correct L h hn s m
  have ud : u.basis L.double=s.basis L.double := e0.outside _ hd
  let v := run (maskedPointConstant L.double L.output (C+C)) m u
  have e1 := maskedPointConstant_correct L.double L.output (C+C) hr hd h.outputX h.outputY u m
  have vf : v.basis L.input.finite=s.basis L.input.finite := (e0.trans e1).outside _ hf
  have e2 := negativePointConstant_correct L.input.finite L.output C hr hf h.outputX h.outputY v m
  have hh := (e0.trans e1).trans e2
  rw [pointOutput,run_append,run_take,run_append,run_take]
  -- 输出段没有测量，测量记录的切片不改变运行结果。
  have cm : measurementCount (maskedPointConstant L.double L.output (C+C))=0 := by
    simp [maskedPointConstant,measurementCount_append,maskedConstant_counts]
  have gm : measurementCount (pointGenericOutput L)=0 := by
    have hx : (L.candidateX.take 256).length=L.output.x.length := by
      have hh := h.words L.candidateX (by simp [PointAddLayout.words]); simp [hh,h.outputX]
    have hy : (L.candidateY.take 256).length=L.output.y.length := by
      have hh := h.words L.candidateY (by simp [PointAddLayout.words]); simp [hh,h.outputY]
    simp [pointGenericOutput,measurementCount_append,measurementCount,
      (copyRegister_counts _ _ _ hx).2,(copyRegister_counts _ _ _ hy).2]
  simp only [measurementCount_append,gm,cm,Nat.zero_add,List.drop_zero]
  simpa only [ud,vf] using hh

end ECDSAAdd.Arithmetic
