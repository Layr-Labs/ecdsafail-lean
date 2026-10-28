import ECDSAAdd.Arithmetic.Rotate

namespace ECDSAAdd.Arithmetic

/-- 同一物理寄存器连续右旋 k 位；不改变寄存器视图。 -/
def rotateRightBits (r : List Wire) : Nat → Program
  | 0 => []
  | k+1 => rotateRight r ++ rotateRightBits r k

/-- 无测量相邻交换的左旋，用于恢复窗口约减前的数值。 -/
def rotateLeftBits (r : List Wire) : Nat → Program
  | 0 => []
  | k+1 => rotateLeft r ++ rotateLeftBits r k

theorem rotateBits_counts (r : List Wire) (k : Nat) :
    toffoliCount (rotateRightBits r k)=0 ∧ measurementCount (rotateRightBits r k)=0 ∧
    toffoliCount (rotateLeftBits r k)=0 ∧ measurementCount (rotateLeftBits r k)=0 := by
  induction k with
  | zero => simp [rotateRightBits,rotateLeftBits,toffoliCount,measurementCount]
  | succ k ih => simp [rotateRightBits,rotateLeftBits,toffoliCount_append,
      measurementCount_append,rotate_counts,ih]

theorem rotateBits_frame (r : List Wire) (k : Nat) (s : State) (m : List Bool) :
    (run (rotateRightBits r k) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateRightBits r k) m s).basis q=s.basis q) ∧
    (run (rotateLeftBits r k) m s).phase=s.phase ∧
    (∀ q, q∉r → (run (rotateLeftBits r k) m s).basis q=s.basis q) := by
  induction k generalizing s with
  | zero => simp [rotateRightBits,rotateLeftBits,run]
  | succ k ih =>
    simp only [rotateRightBits,rotateLeftBits]
    rw [run_append,run_take,run_append,run_take,
      (rotate_counts r).2.1,(rotate_counts r).2.2.2,List.drop_zero]
    have hr := ih (run (rotateRight r) m s)
    have hl := ih (run (rotateLeft r) m s)
    have h := rotate_frame r s m
    exact ⟨hr.1.trans h.1,fun q hq => (hr.2.1 q hq).trans (h.2.1 q hq),
      hl.2.2.1.trans h.2.2.1,fun q hq => (hl.2.2.2 q hq).trans (h.2.2.2 q hq)⟩

theorem rotateRightBits_spec (r : List Wire) (k X : Nat) (hnd : r.Nodup)
    (hdiv : X%2^k=0) : {{ r=X }} rotateRightBits r k {{ r=(X/2^k) }} := by
  induction k generalizing X with
  | zero => intro s m h; exact ⟨rfl,by simpa [rotateRightBits,run] using h⟩
  | succ k ih =>
    have he : X%2=0 := by
      have hh := Nat.mod_mod_of_dvd X (show 2 ∣ 2^(k+1) by
        rw [Nat.pow_succ]; exact dvd_mul_left 2 (2^k))
      rw [hdiv] at hh
      simpa using hh.symm
    have hd : (X/2)%2^k=0 := by
      rw [← Nat.mod_mul_left_div_self,show X % (2^k*2)=0 by simpa [Nat.pow_succ] using hdiv]
    have hh := (rotateRight_spec r hnd X he).seq (ih (X/2) hd)
    simpa [rotateRightBits,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm] using hh

theorem rotateLeftBits_spec (r : List Wire) (k X : Nat) (hnd : r.Nodup)
    (hfit : 2^k*X<2^r.length) : {{ r=X }} rotateLeftBits r k {{ r=(2^k*X) }} := by
  induction k generalizing X with
  | zero => intro s m h; exact ⟨rfl,by simpa [rotateLeftBits,run] using h⟩
  | succ k ih =>
    have hp : 0<2^k := by positivity
    have hf : 2*X<2^r.length := by
      have hh : 2*X≤2^k*(2*X) := Nat.le_mul_of_pos_left _ hp
      simp only [Nat.pow_succ] at hfit
      nlinarith
    have hk : 2^k*(2*X)<2^r.length := by simpa [Nat.pow_succ,Nat.mul_assoc] using hfit
    have hh := (rotateLeft_spec r hnd X hf).seq (ih (2*X) hk)
    simpa [rotateLeftBits,Nat.pow_succ,Nat.mul_assoc] using hh

end ECDSAAdd.Arithmetic
