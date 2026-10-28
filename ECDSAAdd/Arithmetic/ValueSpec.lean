import ECDSAAdd.Arithmetic.ValueWires

namespace ECDSAAdd.Arithmetic

/-- 值走沿用旧布局作为视图；r/s 是任意、保持的旁路线，不参与系数运算。
旧 scratch 中 out 的零断言仅为兼容 RoundState；支持等式证明门列不触及 out。 -/
theorem valueRound_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i : Nat) (z : ValueState)
    (hi : i<512) (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i))
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    {{ L.u=z.u, L.v=z.v, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} valueRound L i
    {{ L.u=(valueStep z).u, L.v=(valueStep z).v, L.k=0, L.kNext=(valueStep z).k,
       L.done=(decide ((valueStep z).v=0)), L.swap=(valueCode z).1,
       L.subtract=(valueCode z).2, L.scratch=0 }} := by
  intro s m h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨huv,hv0⟩,hk0⟩,hn⟩,hd⟩,hs⟩,ht⟩,hw0⟩
  let full : KState := ⟨z.u,z.v,regValue L.r s.basis,regValue L.s s.basis,z.k⟩
  have hin : RoundState L full z.k 0 false (decide (z.v=0)) false false s.basis :=
    (roundState_iff L full z.k 0 _ _ _ _).mpr
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨huv,hv0⟩,rfl⟩,rfl⟩,hk0⟩,hn⟩,hd⟩,hs⟩,ht⟩,hw0⟩
  obtain ⟨hp,ho⟩ := valueRound_state L hnd hw i full hi hk hu hv s m hin
  have hout := (roundState_iff L (valueKStep full) 0 (valueKStep full).k _ _ _ _).mp ho
  rcases hout with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu1,hv1⟩,_⟩,_⟩,hk1⟩,hn1⟩,hd1⟩,hs1⟩,ht1⟩,hw1⟩
  exact ⟨hp,⟨⟨⟨⟨⟨⟨⟨hu1,hv1⟩,hk1⟩,hn1⟩,hd1⟩,hs1⟩,ht1⟩,hw1⟩⟩

/-- 两位分支记录在逆轮清零；终止后的轮也包含在同一规格内。 -/
theorem valueUnround_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i : Nat) (z : ValueState)
    (hi : i<512) (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i))
    (hu : z.u<2^L.data.width) (hv : z.v<2^L.data.width) :
    {{ L.u=(valueStep z).u, L.v=(valueStep z).v, L.k=0, L.kNext=(valueStep z).k,
       L.done=(decide ((valueStep z).v=0)), L.swap=(valueCode z).1,
       L.subtract=(valueCode z).2, L.scratch=0 }} valueUnround L i
    {{ L.u=z.u, L.v=z.v, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} := by
  intro s m h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨huv,hv0⟩,hk0⟩,hn⟩,hd⟩,hs⟩,ht⟩,hw0⟩
  let full : KState := ⟨z.u,z.v,regValue L.r s.basis,regValue L.s s.basis,z.k⟩
  have hin : RoundState L (valueKStep full) 0 (valueKStep full).k false
      (decide ((valueKStep full).v=0)) (kaliskiCode full).1 (kaliskiCode full).2 s.basis :=
    (roundState_iff L (valueKStep full) 0 (valueKStep full).k _ _ _ _).mpr
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨huv,hv0⟩,rfl⟩,rfl⟩,hk0⟩,hn⟩,hd⟩,hs⟩,ht⟩,hw0⟩
  obtain ⟨hp,ho⟩ := valueUnround_state L hnd hw i full hi hk hu hv s m hin
  have hout := (roundState_iff L full z.k 0 _ _ _ _).mp ho
  rcases hout with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu1,hv1⟩,_⟩,_⟩,hk1⟩,hn1⟩,hd1⟩,hs1⟩,ht1⟩,hw1⟩
  exact ⟨hp,⟨⟨⟨⟨⟨⟨⟨hu1,hv1⟩,hk1⟩,hn1⟩,hd1⟩,hs1⟩,ht1⟩,hw1⟩⟩

/-- 支持集外逐线保持，特别是旧布局的 r/s/out 不被值走程序使用。 -/
theorem valueRound_frame (L : KaliskiRoundLayout) (hw : L.counter.width=10)
    (hd : 2≤L.data.width) (i : Nat) (s : State) (m : List Bool) (w : Wire)
    (he : w∉L.valueUsedWires) :
    (run (valueRound L i) m s).basis w=s.basis w ∧
    (run (valueUnround L i) m s).basis w=s.basis w := by
  have h := valueRound_wires L hw hd i
  exact ⟨run_preserves_outside _ _ _ _ (by simpa [h.1] using he),
    run_preserves_outside _ _ _ _ (by simpa [h.2] using he)⟩

theorem valueRound_257_resources (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (hd : L.data.width=257) (i : Nat) :
    toffoliCount (valueRound L i)=1832 ∧ measurementCount (valueRound L i)=1057 ∧
    qubitCount (valueRound L i)=1333 ∧ toffoliCount (valueUnround L i)=1832 ∧
    measurementCount (valueUnround L i)=1057 ∧ qubitCount (valueUnround L i)=1333 := by
  have hc := valueRound_counts L hnd hw i
  have hq := valueRound_qubits L hnd hw (by omega) i
  rw [hd] at hc hq
  exact ⟨hc.1,hc.2.1,hq.1,hc.2.2.1,hc.2.2.2,hq.2⟩

end ECDSAAdd.Arithmetic
