import ECDSAAdd.Arithmetic.ReplayRoundProof

namespace ECDSAAdd.Arithmetic

theorem replayNatLoop_bound (p K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) (hp : p%2=1) (hX : X<p) (hY : Y<p) :
    (replayNatLoop p K i ref rs (X,Y)).1<p ∧ (replayNatLoop p K i ref rs (X,Y)).2<p := by
  induction rs generalizing i X Y with
  | nil => exact ⟨hX,hY⟩
  | cons r rs ih =>
    have hb := replayNatStep_bound p X Y (decide (i<K)) (ref r.swap) (ref r.subtract) hp hX hY
    exact ih (i+1) _ _ hb.1 hb.2

theorem replayNatUnloop_bound (p K i : Nat) (ref : BasisState) (rs : List RoundRecord)
    (X Y : Nat) (hp : 0<p) (hX : X<p) (hY : Y<p) :
    (replayNatUnloop p K i ref rs (X,Y)).1<p ∧ (replayNatUnloop p K i ref rs (X,Y)).2<p := by
  induction rs generalizing i X Y with
  | nil => exact ⟨hX,hY⟩
  | cons r rs ih =>
    have hb := ih (i+1) X Y hX hY
    exact replayNatUnstep_bound p _ _ (decide (i<K)) (ref r.swap) (ref r.subtract) hp hb.1 hb.2

/-- 任意长度（至多剩余512轮）的正回放；记录与外部线路由 ref 精确保持。 -/
theorem replayLoop_spec (L : ReplayLayout) (n p K i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (ref : BasisState) (X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p)
    (hK : regValue L.counter.x ref=K) (hi : i+rs.length≤512) :
    Triple (ReplayState L ref false X Y) (replayLoop L p i rs)
      (ReplayState L ref false (replayNatLoop p K i ref rs (X,Y)).1
        (replayNatLoop p K i ref rs (X,Y)).2) := by
  induction rs generalizing i X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have h1 := replayRound_spec L n p (r::rs) r hv (by simp) ref K i X Y
      hp hpn hX hY hK (by simp only [List.length_cons] at hi; omega)
    have hb := replayNatStep_bound p X Y (decide (i<K)) (ref r.swap) (ref r.subtract) hp hX hY
    have h2 := ih (i+1) (hv.tail L n r rs) _ _ hb.1 hb.2 (by simp only [List.length_cons] at hi; omega)
    exact h1.seq h2

/-- 反回放按记录逆序组合，每格仍使用前向门列。 -/
theorem replayUnloop_spec (L : ReplayLayout) (n p K i : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (ref : BasisState) (X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p)
    (hK : regValue L.counter.x ref=K) (hi : i+rs.length≤512) :
    Triple (ReplayState L ref false X Y) (replayUnloop L p i rs)
      (ReplayState L ref false (replayNatUnloop p K i ref rs (X,Y)).1
        (replayNatUnloop p K i ref rs (X,Y)).2) := by
  induction rs generalizing i X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have h1 := ih (i+1) (hv.tail L n r rs) X Y hX hY (by simp only [List.length_cons] at hi; omega)
    have hb := replayNatUnloop_bound p K (i+1) ref rs X Y (by omega) hX hY
    have h2 := replayUnround_spec L n p (r::rs) r hv (by simp) ref K i _ _
      hp hpn hb.1 hb.2 hK (by simp only [List.length_cons] at hi; omega)
    exact h1.seq h2

/-- 终止后合法记录 00 对任意载荷为恒等函数。 -/
theorem replay_padding (p X Y : Nat) :
    replayNatStep p false false false X Y=(X,Y) ∧
    replayNatUnstep p false false false X Y=(X,Y) := ⟨rfl,rfl⟩

end ECDSAAdd.Arithmetic
