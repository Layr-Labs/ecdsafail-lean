import ECDSAAdd.Arithmetic.RecordRound

namespace ECDSAAdd.Arithmetic

/-- 擦除已知 active∧¬r₀；线性相位项与二次项都必须修正。 -/
def eraseSwap (L : KaliskiRoundLayout) : Program :=
  [.measureX L.swap [] [.CZ L.active L.r.head!, .Z L.active]]

/-- 任意测量记录下相位精确恢复，仅把交换临时位清零。 -/
theorem eraseSwap_correct (L : KaliskiRoundLayout) (hn : L.wires.Nodup)
    (s : State) (m : List Bool)
    (ht : s.basis L.swap=(s.basis L.active && !s.basis L.r.head!)) :
    run (eraseSwap L) m s=⟨s.phase,writeBit s.basis L.swap false⟩ := by
  have ha : L.active≠L.swap := by
    have h := (List.nodup_append'.mp (L.controls_data_nodup hn)).1
    simp only [KaliskiRoundLayout.controls,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      not_or,not_false_eq_true,and_true] at h
    tauto
  have hr : L.r.head!≠L.swap := fun he =>
    L.control_not_data hn L.swap (by simp [KaliskiRoundLayout.controls])
      (he ▸ L.data.reg_mem .r (L.head_mem .r))
  cases hm : m.head?.getD false <;> cases hac : s.basis L.active <;>
    cases hrc : s.basis L.r.head! <;>
    simp [eraseSwap,run,measureAndCorrect,correct,writeBit,ha,hr,ht,hm,hac,hrc]

theorem eraseSwap_frame (L : KaliskiRoundLayout) (hn : L.wires.Nodup)
    (s : State) (m : List Bool)
    (ht : s.basis L.swap=(s.basis L.active && !s.basis L.r.head!))
    (w : Wire) (hw : w≠L.swap) : (run (eraseSwap L) m s).basis w=s.basis w := by
  rw [eraseSwap_correct L hn s m ht]
  simp [writeBit,hw]

theorem eraseSwap_counts (L : KaliskiRoundLayout) :
    toffoliCount (eraseSwap L)=0 ∧ measurementCount (eraseSwap L)=1 := ⟨rfl,rfl⟩

theorem eraseSwap_wires (L : KaliskiRoundLayout) :
    wires (eraseSwap L)=[L.swap,L.active,L.r.head!].toFinset := by
  ext w
  simp [eraseSwap,wires,Instr.wires,correctionWires,or_assoc,or_left_comm,or_comm]

end ECDSAAdd.Arithmetic
