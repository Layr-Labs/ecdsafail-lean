import ECDSAAdd.Arithmetic.OneBitRoundProof

namespace ECDSAAdd.Arithmetic

/-- 公开正轮规格：更新四份数据、计数与减法记录，交换临时位和共享工作区归零。 -/
theorem oneBitRound_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    {{ L.u=z.u, L.v=z.v, L.r=z.r, L.s=z.s, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} oneBitRound L i
    {{ L.u=(kaliskiStep z).u, L.v=(kaliskiStep z).v, L.r=(kaliskiStep z).r, L.s=(kaliskiStep z).s,
       L.k=0, L.kNext=(kaliskiStep z).k, L.done=(decide ((kaliskiStep z).v=0)),
       L.swap=false, L.subtract=(kaliskiCode z).2, L.scratch=0 }} := by
  intro s m h
  have hs := (roundState_iff L z z.k 0 (decide (z.v=0)) false false s.basis).mpr h
  have hr := regValue_lt (L.data.reg .r) s.basis
  rw [hs.1.1 .r,L.data.reg_length] at hr
  obtain ⟨hphase,hout⟩ := oneBitRound_state L hnd hw i p a z hi hk hinv hodd hp hu hv hr s m hs
  exact ⟨hphase,(roundState_iff L (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ _).mp hout⟩

/-- 公开逆轮规格：恢复旧数据/计数/done，清除减法历史和全部工作区。 -/
theorem oneBitUnround_spec (L : KaliskiRoundLayout) (hnd : L.wires.Nodup)
    (hw : L.counter.width=10) (i p a : Nat) (z : KState)
    (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    {{ L.u=(kaliskiStep z).u, L.v=(kaliskiStep z).v, L.r=(kaliskiStep z).r, L.s=(kaliskiStep z).s,
       L.k=0, L.kNext=(kaliskiStep z).k, L.done=(decide ((kaliskiStep z).v=0)),
       L.swap=false, L.subtract=(kaliskiCode z).2, L.scratch=0 }} oneBitUnround L i
    {{ L.u=z.u, L.v=z.v, L.r=z.r, L.s=z.s, L.k=z.k, L.kNext=0,
       L.done=(decide (z.v=0)), L.swap=false, L.subtract=false, L.scratch=0 }} := by
  intro s m h
  have hs := (roundState_iff L (kaliskiStep z) 0 (kaliskiStep z).k (decide ((kaliskiStep z).v=0))
    false (kaliskiCode z).2 s.basis).mpr h
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
  obtain ⟨hphase,hout⟩ := oneBitUnround_state L hnd hw i p a z hi hk hinv hodd hp hu hv hr s m hs
  exact ⟨hphase,(roundState_iff L z z.k 0 _ _ _ _).mp hout⟩


end ECDSAAdd.Arithmetic
