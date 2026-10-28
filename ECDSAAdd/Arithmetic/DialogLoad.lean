import ECDSAAdd.Arithmetic.DialogProgram
import ECDSAAdd.Arithmetic.DialogRegisters

namespace ECDSAAdd.Arithmetic

namespace DialogLayout

def vLow (L : DialogLayout) : List Wire := L.first.low.map (·.v)

theorem load_nodup (L : DialogLayout) (hn : L.wires.Nodup) :
    (L.control::L.x++L.first.u++L.vLow++[L.first.high.v]).Nodup := by
  have hh := L.registerWires_perm.nodup_iff.mpr hn
  apply List.nodup_iff_count.mpr
  intro w
  have hc := List.nodup_iff_count.mp hh w
  have hr : L.first.r=L.x++[L.control] := by
    simp [KaliskiRoundLayout.r,KaliskiRoundLayout.data,RoundDataLayout.r,RoundDataLayout.reg,
      x,control,RoundBit.get]
  have hv : L.first.v=L.vLow++[L.first.high.v] := by
    simp [KaliskiRoundLayout.v,KaliskiRoundLayout.data,RoundDataLayout.v,RoundDataLayout.reg,
      vLow,RoundBit.get]
  simp only [registerWires,hr,hv,List.count_append,List.count_cons,List.count_nil] at hc ⊢
  omega
end DialogLayout

/-- 装卸是同一XOR程序；同时保留两个目标字以外的所有位。 -/
theorem dialogLoad_correct (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup)
    (hp : p<2^L.first.u.length) (s : State) (m : List Bool) :
    (run (dialogLoad L p) m s).phase=s.phase ∧
    (∀ w, w∉L.first.u → w∉L.vLow → (run (dialogLoad L p) m s).basis w=s.basis w) ∧
    regValue L.first.u (run (dialogLoad L p) m s).basis=regValue L.first.u s.basis ^^^ p ∧
    regValue L.vLow (run (dialogLoad L p) m s).basis=regValue L.vLow s.basis ^^^
      (if s.basis L.control then regValue L.x s.basis else 1) := by
  have hd := L.load_nodup hn
  have hu : L.first.u.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hd w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc
    omega
  have dis (w : Wire) (ha : w∈L.control::L.x++L.vLow) : w∉L.first.u := by
    intro hb
    have hc := List.nodup_iff_count.mp hd w
    have h1 := List.count_pos_iff.mpr ha
    have h2 := List.count_pos_iff.mpr hb
    simp only [List.count_cons,List.count_append,List.count_nil] at hc h1
    omega
  let t := run (xorConstant L.first.u p) m s
  have ht := xorConstant_correct L.first.u hu p hp s m
  have htc : t.basis L.control=s.basis L.control := ht.2.1 _ (dis _ (by simp))
  have htx : regValue L.x t.basis=regValue L.x s.basis :=
    regValue_congr _ _ _ (fun w hw => ht.2.1 _ (dis _ (by simp [hw])))
  have htv : regValue L.vLow t.basis=regValue L.vLow s.basis :=
    regValue_congr _ _ _ (fun w hw => ht.2.1 _ (dis _ (by simp [hw])))
  have hl : L.vLow.length=256 := by simp [DialogLayout.vLow,hw.low]
  cases he : L.vLow with
  | nil => simp [he] at hl
  | cons h ts =>
    have hs : (L.control::L.x++(h::ts)).Nodup := by
      apply List.nodup_iff_count.mpr
      intro w
      have hc := List.nodup_iff_count.mp hd w
      rw [he] at hc
      simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
      omega
    have hlen : L.x.length=(h::ts).length := by
      rw [←he]; simp [DialogLayout.x,DialogLayout.vLow]
    have hf := safeDivisor_correct L.control L.x h ts hlen hs t m
    have heq : run (dialogLoad L p) m s=run (safeDivisor L.control L.x h ts) m t := by
      simp only [dialogLoad,show L.first.low.map (·.v)=h::ts from he,run_append,
        (xorConstant_counts _ _).2,List.drop_zero,t]
      rw [← (xorConstant_counts L.first.u p).2,run_take]
    rw [heq]
    refine ⟨hf.1.trans ht.1,?_,?_,?_⟩
    · intro w hwu hwv
      exact (hf.2.1 w (by simpa [←he] using hwv)).trans (ht.2.1 w hwu)
    · apply Eq.trans (regValue_congr _ _ _ ?_) ht.2.2
      intro w hwu
      apply hf.2.1
      intro hwv
      exact dis w (by simp [←he] at hwv; simp [hwv]) hwu
    · rw [←he] at hf
      have hv' := hf.2.2
      rw [htv,htc,htx] at hv'
      simpa only [he] using hv'

end ECDSAAdd.Arithmetic
