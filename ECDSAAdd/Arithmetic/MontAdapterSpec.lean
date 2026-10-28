import ECDSAAdd.Arithmetic.MontAdapterLayout

namespace ECDSAAdd.Arithmetic

private theorem pow256_lt_pow257 : (2:Nat)^256<2^257 := by
  rw [show (257:Nat)=256+1 from rfl,Nat.pow_succ]
  have h := Nat.two_pow_pos 256
  omega

private theorem prepared_preserved (M : MontLayout) (p X Y : Nat) (hnd : M.wires.Nodup)
    (s t : BasisState) (h : MontPrepared M p X Y s)
    (he : ∀w, w∉M.out → t w=s w) : MontPrepared M p X Y t := by
  have keep (r : List Wire) (hr : r⊆M.x++M.y++M.work) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp (M.out_disjoint hnd) (hr hw)))
  have hwA : M.a⊆M.x++M.y++M.work := by intro w hw; simp [MontLayout.work,MontLayout.activeA,hw]
  have hwZ : M.z⊆M.x++M.y++M.work := by intro w hw; simp [MontLayout.work,MontLayout.activeZ,hw]
  have hhA : M.hA⊆M.x++M.y++M.work := by intro w hw; simp [MontLayout.work,MontLayout.activeA,hw]
  have hhZ : M.hZ⊆M.x++M.y++M.work := by intro w hw; simp [MontLayout.work,MontLayout.activeZ,hw]
  refine ⟨(keep M.x (by intro w hw; simp [hw])).trans h.x,
    (keep M.y (by intro w hw; simp [hw])).trans h.y,
    (keep M.a hwA).trans h.a,(keep M.z hwZ).trans h.z,
    (keep M.hA hhA).trans h.hA,(keep M.hZ hhZ).trans h.hZ,?_,?_,
    (keep M.shared (by intro w hw; simp [MontLayout.work,hw])).trans h.shared⟩
  · exact (he M.fA (List.disjoint_left.mp (M.out_disjoint hnd)
      (by simp [MontLayout.work,MontLayout.activeA]))).trans h.fA
  · exact (he M.fZ (List.disjoint_left.mp (M.out_disjoint hnd)
      (by simp [MontLayout.work,MontLayout.activeZ]))).trans h.fZ

/-- 中段只更新输出即可复用完整P/Q；此组合引理不增加程序或状态抽象。 -/
private theorem montSandwich_spec (M : MontLayout) (p X Y O V : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (middle : Program)
    (hmid : ∀s m, MontPrepared M p X Y s.basis → regValue M.out s.basis=O →
      (run middle m s).phase=s.phase ∧
      (∀w, w∉M.out → (run middle m s).basis w=s.basis w) ∧
      regValue M.out (run middle m s).basis=V) :
    {{ M.x=X,M.y=Y,M.out=O,M.work=0 }} montP M p ++ middle ++ montQ M p
    {{ M.x=X,M.y=Y,M.out=V,M.work=0 }} := by
  have hpSpec : Triple (fun s => ((regValue M.x s=X ∧ regValue M.y s=Y) ∧ regValue M.out s=O) ∧ regValue M.work s=0)
      (montP M p) (fun s => MontPrepared M p X Y s ∧ regValue M.out s=O) := by
    intro s m h
    have hh := montP_correct M p X Y hw hnd hp hp16 hX hY s m h.1.1.1 h.1.1.2 h.2
    have hout : regValue M.out (run (montP M p) m s).basis=O := by
      apply Eq.trans (regValue_congr _ _ _ ?_) h.1.2
      intro w ho
      exact hh.2.1 w (fun hw' => List.disjoint_left.mp (M.out_disjoint hnd) (by simp [hw']) ho)
    exact ⟨hh.1,hh.2.2,hout⟩
  have hmSpec : Triple (fun s => MontPrepared M p X Y s ∧ regValue M.out s=O) middle
      (fun s => MontPrepared M p X Y s ∧ regValue M.out s=V) := by
    intro s m h
    have hh := hmid s m h.1 h.2
    exact ⟨hh.1,prepared_preserved M p X Y hnd s.basis _ h.1 hh.2.1,hh.2.2⟩
  have hqSpec : Triple (fun s => MontPrepared M p X Y s ∧ regValue M.out s=V) (montQ M p)
      (fun s => ((regValue M.x s=X ∧ regValue M.y s=Y) ∧ regValue M.out s=V) ∧ regValue M.work s=0) := by
    intro s m h
    have hh := montQ_correct M p X Y hw hnd hp hp16 hX hY s m h.1
    have hout : regValue M.out (run (montQ M p) m s).basis=V := by
      apply Eq.trans (regValue_congr _ _ _ ?_) h.2
      intro w ho
      exact hh.2.1 w (fun hw' => List.disjoint_left.mp (M.out_disjoint hnd) (by simp [hw']) ho)
    exact ⟨hh.1,⟨⟨hh.2.2.1,hh.2.2.2.1⟩,hout⟩,hh.2.2.2.2⟩
  exact (hpSpec.seq hmSpec).seq hqSpec

/-- 任意257位输出的标准模积XOR，全部历史由Q清空。 -/
theorem montMulXor_spec (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) :
    {{ M.x=X,M.y=Y,M.out=O,M.work=0 }} montMulXor M p
    {{ M.x=X,M.y=Y,M.out=(O ^^^ ((X*Y)%p)),M.work=0 }} := by
  apply montSandwich_spec M p X Y O _ hw hnd hp hp16 hX hY
  intro s m h ho
  have hn : (M.product++M.out).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hnd w
    have ht := (List.take_sublist 257 M.z).count_le w
    simp only [MontLayout.wires,MontLayout.work,MontLayout.activeZ,MontLayout.product,List.count_append] at hh ht ⊢
    omega
  have hh := copyRegister_correct none M.product M.out (by simp [MontLayout.product,hw.z,hw.out]) hn (by simp) s m
  have hv := M.product_value hw s.basis ((X*Y)%p) h.z
    (lt_trans (Nat.mod_lt _ (Fact.out : p.Prime).pos) (lt_trans hp pow256_lt_pow257))
  exact ⟨hh.1,hh.2.1,by simpa only [copyValue,ho,hv] using hh.2.2⟩



theorem montMulAdd_spec (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) :
    {{ M.x=X,M.y=Y,M.out=O,M.work=0 }} montMulAdd M p
    {{ M.x=X,M.y=Y,M.out=(O+(X*Y)%p)%p,M.work=0 }} := by
  apply montSandwich_spec M p X Y O _ hw hnd hp hp16 hX hY
  intro s m h ho
  have hp0 := (Fact.out : p.Prime).pos
  have hv : regValue M.addView.a s.basis=(X*Y)%p := M.product_value hw s.basis _ h.z
    (lt_trans (Nat.mod_lt _ hp0) (lt_trans hp pow256_lt_pow257))
  have hz : regValue M.addView.z s.basis=O := by rw [(M.add_ports hw).2]; exact ho
  have hc : regValue M.addView.work s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw' => (regValue_zero _ _).mp h.shared w (M.add_work_subset hw hw'))
  have hh := modAddInPlace_spec M.addView 256 p ((X*Y)%p) O (M.add_widths hw) (M.add_nodup hw hnd)
    hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m ⟨⟨hv,hz⟩,hc⟩
  refine ⟨hh.1,?_,?_⟩
  · intro w hn
    exact modAddInPlace_frame M.addView 256 p ((X*Y)%p) O (M.add_widths hw) (M.add_nodup hw hnd)
      hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m hv hz hc w (by rw [(M.add_ports hw).2]; exact hn)
  · simpa only [(M.add_ports hw).2] using hh.2.1.2


theorem montMulSub_spec (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) :
    {{ M.x=X,M.y=Y,M.out=O,M.work=0 }} montMulSub M p
    {{ M.x=X,M.y=Y,M.out=(O+p-(X*Y)%p)%p,M.work=0 }} := by
  apply montSandwich_spec M p X Y O _ hw hnd hp hp16 hX hY
  intro s m h ho
  have hp0 := (Fact.out : p.Prime).pos
  have hv : regValue M.addView.a s.basis=(X*Y)%p := M.product_value hw s.basis _ h.z
    (lt_trans (Nat.mod_lt _ hp0) (lt_trans hp pow256_lt_pow257))
  have hz : regValue M.addView.z s.basis=O := by rw [(M.add_ports hw).2]; exact ho
  have hc : regValue M.addView.work s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw' => (regValue_zero _ _).mp h.shared w (M.add_work_subset hw hw'))
  have hh := modSubInPlace_spec M.addView 256 p ((X*Y)%p) O (M.add_widths hw) (M.add_nodup hw hnd)
    hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m ⟨⟨hv,hz⟩,hc⟩
  refine ⟨hh.1,?_,?_⟩
  · intro w hn
    exact modSubInPlace_frame M.addView 256 p ((X*Y)%p) O (M.add_widths hw) (M.add_nodup hw hnd)
      hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m hv hz hc w (by rw [(M.add_ports hw).2]; exact hn)
  · simpa only [(M.add_ports hw).2] using hh.2.1.2



private theorem montControlledSandwich_spec (c : Wire) (B : Bool) (M : MontLayout) (p X Y O V : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (middle : Program)
    (hmid : ∀s m, s.basis c=B → MontPrepared M p X Y s.basis → regValue M.out s.basis=O →
      (run middle m s).phase=s.phase ∧
      (∀w, w∉M.out → (run middle m s).basis w=s.basis w) ∧
      regValue M.out (run middle m s).basis=V) :
    {{ c=B,M.x=X,M.y=Y,M.out=O,M.work=0 }} montP M p ++ middle ++ montQ M p
    {{ c=B,M.x=X,M.y=Y,M.out=V,M.work=0 }} := by
  have hn := hnd.tail
  have hcnot : c∉M.work := fun h => (List.nodup_cons.mp hnd).1 (by simp [MontLayout.wires,h])
  have hcout : c∉M.out := fun h => (List.nodup_cons.mp hnd).1 (by simp [MontLayout.wires,h])
  have hpSpec : Triple (fun s => (((s c=B ∧ regValue M.x s=X) ∧ regValue M.y s=Y) ∧ regValue M.out s=O) ∧ regValue M.work s=0)
      (montP M p) (fun s => s c=B ∧ MontPrepared M p X Y s ∧ regValue M.out s=O) := by
    intro s m h
    have hh := montP_correct M p X Y hw hn hp hp16 hX hY s m h.1.1.1.2 h.1.1.2 h.2
    have hout : regValue M.out (run (montP M p) m s).basis=O := by
      apply Eq.trans (regValue_congr _ _ _ ?_) h.1.2
      intro w ho
      exact hh.2.1 w (fun hw' => List.disjoint_left.mp (M.out_disjoint hn) (by simp [hw']) ho)
    exact ⟨hh.1,(hh.2.1 c hcnot).trans h.1.1.1.1,hh.2.2,hout⟩
  have hmSpec : Triple (fun s => s c=B ∧ MontPrepared M p X Y s ∧ regValue M.out s=O) middle
      (fun s => s c=B ∧ MontPrepared M p X Y s ∧ regValue M.out s=V) := by
    intro s m h
    have hh := hmid s m h.1 h.2.1 h.2.2
    exact ⟨hh.1,(hh.2.1 c hcout).trans h.1,prepared_preserved M p X Y hn s.basis _ h.2.1 hh.2.1,hh.2.2⟩
  have hqSpec : Triple (fun s => s c=B ∧ MontPrepared M p X Y s ∧ regValue M.out s=V) (montQ M p)
      (fun s => (((s c=B ∧ regValue M.x s=X) ∧ regValue M.y s=Y) ∧ regValue M.out s=V) ∧ regValue M.work s=0) := by
    intro s m h
    have hh := montQ_correct M p X Y hw hn hp hp16 hX hY s m h.2.1
    have hout : regValue M.out (run (montQ M p) m s).basis=V := by
      apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2
      intro w ho
      exact hh.2.1 w (fun hw' => List.disjoint_left.mp (M.out_disjoint hn) (by simp [hw']) ho)
    exact ⟨hh.1,⟨⟨⟨(hh.2.1 c hcnot).trans h.1,hh.2.2.1⟩,hh.2.2.2.1⟩,hout⟩,hh.2.2.2.2⟩
  exact (hpSpec.seq hmSpec).seq hqSpec


theorem montMulControlledAdd_spec (c : Wire) (B : Bool) (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) :
    {{ c=B,M.x=X,M.y=Y,M.out=O,M.work=0 }} montMulControlledAdd c M p
    {{ c=B,M.x=X,M.y=Y,M.out=(if B then (O+(X*Y)%p)%p else O),M.work=0 }} := by
  apply montControlledSandwich_spec c B M p X Y O _ hw hnd hp hp16 hX hY
  intro s m hb h ho
  have hp0 := (Fact.out : p.Prime).pos
  have hn := MontLayout.controlled_add_nodup c M hw hnd
  have hv : regValue M.addView.a s.basis=(X*Y)%p := M.product_value hw s.basis _ h.z
    (lt_trans (Nat.mod_lt _ hp0) (lt_trans hp pow256_lt_pow257))
  have hz : regValue M.addView.z s.basis=O := by rw [(M.add_ports hw).2]; exact ho
  have hc : regValue M.addView.work s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw' => (regValue_zero _ _).mp h.shared w (M.add_work_subset hw hw'))
  have hh := controlledModAdd_spec c M.addView 256 p ((X*Y)%p) O B (M.add_widths hw) hn
    hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m ⟨⟨⟨hb,hv⟩,hz⟩,hc⟩
  refine ⟨hh.1,?_,?_⟩
  · intro w hn'
    exact controlledModAdd_frame c M.addView 256 p ((X*Y)%p) O B (M.add_widths hw) hn
      hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m hb hv hz hc w (by rw [(M.add_ports hw).2]; exact hn')
  · simpa only [(M.add_ports hw).2] using hh.2.1.2


theorem montMulControlledSub_spec (c : Wire) (B : Bool) (M : MontLayout) (p X Y O : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : (c::M.wires).Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (hO : O<p) :
    {{ c=B,M.x=X,M.y=Y,M.out=O,M.work=0 }} montMulControlledSub c M p
    {{ c=B,M.x=X,M.y=Y,M.out=(if B then (O+p-(X*Y)%p)%p else O),M.work=0 }} := by
  apply montControlledSandwich_spec c B M p X Y O _ hw hnd hp hp16 hX hY
  intro s m hb h ho
  have hp0 := (Fact.out : p.Prime).pos
  have hn := MontLayout.controlled_add_nodup c M hw hnd
  have hv : regValue M.addView.a s.basis=(X*Y)%p := M.product_value hw s.basis _ h.z
    (lt_trans (Nat.mod_lt _ hp0) (lt_trans hp pow256_lt_pow257))
  have hz : regValue M.addView.z s.basis=O := by rw [(M.add_ports hw).2]; exact ho
  have hc : regValue M.addView.work s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw' => (regValue_zero _ _).mp h.shared w (M.add_work_subset hw hw'))
  have hh := controlledModSub_spec c M.addView 256 p ((X*Y)%p) O B (M.add_widths hw) hn
    hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m ⟨⟨⟨hb,hv⟩,hz⟩,hc⟩
  refine ⟨hh.1,?_,?_⟩
  · intro w hn'
    exact controlledModSub_frame c M.addView 256 p ((X*Y)%p) O B (M.add_widths hw) hn
      hp0 hp (Nat.le_of_lt (Nat.mod_lt _ hp0)) hO s m hb hv hz hc w (by rw [(M.add_ports hw).2]; exact hn')
  · simpa only [(M.add_ports hw).2] using hh.2.1.2

end ECDSAAdd.Arithmetic
