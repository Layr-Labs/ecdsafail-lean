import ECDSAAdd.Arithmetic.RoundWires

namespace ECDSAAdd.Arithmetic

private theorem scratch_zero_iff (L : KaliskiRoundLayout) (st : BasisState) :
    regValue L.scratch st=0 ↔
      st L.data.cin=false ∧ regValue (L.data.reg .y) st=0 ∧ regValue (L.data.reg .out) st=0 ∧
      regValue (L.data.reg .carry) st=0 ∧ regValue (L.data.reg .zero) st=0 ∧
      regValue L.counter.y st=0 ∧ regValue L.counter.carry st=0 ∧
      st L.active=false ∧ st L.compareCin=false ∧ st L.oddWork=false ∧ st L.bothWork=false := by
  simp [KaliskiRoundLayout.scratch,RoundDataLayout.work,regValue_zero,or_imp,forall_and]

theorem roundState_iff (L : KaliskiRoundLayout) (z : KState) (K N : Nat) (D S T : Bool) (st : BasisState) :
    RoundState L z K N false D S T st ↔
      (((((((((regValue L.u st=z.u ∧ regValue L.v st=z.v) ∧ regValue L.r st=z.r) ∧ regValue L.s st=z.s) ∧
        regValue L.k st=K) ∧ regValue L.kNext st=N) ∧ st L.done=D) ∧ st L.swap=S) ∧ st L.subtract=T) ∧
        regValue L.scratch st=0) := by
  rw [scratch_zero_iff]
  constructor
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.1.1 .u,h.1.1 .v⟩,h.1.1 .r⟩,h.1.1 .s⟩,h.2.k⟩,h.2.next⟩,h.2.done⟩,h.2.swap⟩,h.2.subtract⟩,
      h.1.2,h.1.1 .y,h.1.1 .out,h.1.1 .carry,h.1.1 .zero,h.2.y,h.2.carry,h.2.active,h.2.cin,h.2.odd,h.2.both⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu,hv⟩,hr⟩,hs⟩,hk⟩,hn⟩,hd⟩,hS⟩,hT⟩,hcin,hy,ho,hc,hz,hcy,hcc,ha,hci,hodd,hboth⟩
    refine ⟨⟨?_,hcin⟩,hk,hn,hcy,hcc,ha,hd,hS,hT,hodd,hboth,hci⟩
    intro f
    cases f <;> assumption

/-- 公开正轮规格：四份数据、计数与两位记录一并更新，共享工作区归零。 -/
theorem kaliskiRound_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    {{ L.u=z.u, L.v=z.v, L.r=z.r, L.s=z.s, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} kaliskiRound L i
    {{ L.u=(kaliskiStep z).u, L.v=(kaliskiStep z).v, L.r=(kaliskiStep z).r, L.s=(kaliskiStep z).s,
       L.k=0, L.kNext=(kaliskiStep z).k, L.done=(decide ((kaliskiStep z).v=0)),
       L.swap=(kaliskiCode z).1, L.subtract=(kaliskiCode z).2, L.scratch=0 }} := by
  intro s m h
  have hs := (roundState_iff L z z.k 0 (decide (z.v=0)) false false s.basis).mpr h
  have hr := regValue_lt (L.data.reg .r) s.basis
  rw [hs.1.1 .r,L.data.reg_length] at hr
  obtain ⟨hphase,hout⟩ := kaliskiRound_state L hnd hw i p a z hi hk hinv hp hu hv hr s m hs
  exact ⟨hphase,(roundState_iff L (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ _).mp hout⟩

/-- 公开逆轮规格：恢复旧数据/计数/done，清除两位历史记录和全部工作区。 -/
theorem kaliskiUnround_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    {{ L.u=(kaliskiStep z).u, L.v=(kaliskiStep z).v, L.r=(kaliskiStep z).r, L.s=(kaliskiStep z).s,
       L.k=0, L.kNext=(kaliskiStep z).k, L.done=(decide ((kaliskiStep z).v=0)),
       L.swap=(kaliskiCode z).1, L.subtract=(kaliskiCode z).2, L.scratch=0 }} kaliskiUnround L i
    {{ L.u=z.u, L.v=z.v, L.r=z.r, L.s=z.s, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} := by
  intro s m h
  have hs := (roundState_iff L (kaliskiStep z) 0 (kaliskiStep z).k (decide ((kaliskiStep z).v=0))
    (kaliskiCode z).1 (kaliskiCode z).2 s.basis).mpr h
  have hr : z.r<2^L.data.width := by
    by_cases hz : z.v=0
    · have hb := regValue_lt (L.data.reg .r) s.basis
      rw [hs.1.1 .r,L.data.reg_length] at hb
      simpa only [roundDataValues,kaliskiStep,hz,if_true] using hb
    · have hsmall : z.r<p := by
        obtain ⟨hu,hs,he,_⟩ := hinv
        have hv : 0<z.v := by omega
        nlinarith
      have hwidth : L.data.width=L.low.length+1 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width]
      rw [hwidth,pow_succ]
      omega
  obtain ⟨hphase,hout⟩ := kaliskiUnround_state L hnd hw i p a z hi hk hinv hp hu hv hr s m hs
  exact ⟨hphase,(roundState_iff L z z.k 0 _ _ _ _).mp hout⟩

/-- secp256k1 使用 257 位数据/工作寄存器；这里仅计一轮，不是完整逆元成本。 -/
theorem kaliskiRound_257_resources (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (hd : L.data.width=257) (i : Nat) :
    toffoliCount (kaliskiRound L i)=3115 ∧ measurementCount (kaliskiRound L i)=1570 ∧
    qubitCount (kaliskiRound L i)=1847 ∧
    toffoliCount (kaliskiUnround L i)=3115 ∧ measurementCount (kaliskiUnround L i)=1570 ∧
    qubitCount (kaliskiUnround L i)=1847 := by
  have hc := kaliskiRound_counts L hnd hw i
  have hq := kaliskiRound_qubits L hnd hw (by omega) i
  rw [hd] at hc hq
  exact ⟨hc.1,hc.2.1,hq.1,hc.2.2.1,hc.2.2.2,hq.2⟩

end ECDSAAdd.Arithmetic
