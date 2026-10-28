import ECDSAAdd.Arithmetic.PointOutput

namespace ECDSAAdd.Arithmetic

/-- 点输出的逐字段 XOR 和完整外部保持条件；目标无需编码曲线点。 -/
structure PointEffect (r : PointReg) (F : Bool) (X Y : Nat) (s t : State) : Prop where
  phase : t.phase=s.phase
  outside : ∀ w∉PointAddLayout.pointWires r,t.basis w=s.basis w
  finite : t.basis r.finite=(s.basis r.finite ^^ F)
  x : regValue r.x t.basis=regValue r.x s.basis ^^^ X
  y : regValue r.y t.basis=regValue r.y s.basis ^^^ Y

theorem PointEffect.trans {r : PointReg} {F G : Bool} {X Y U V : Nat} {s t u : State}
    (h : PointEffect r F X Y s t) (k : PointEffect r G U V t u) :
    PointEffect r (F^^G) (X^^^U) (Y^^^V) s u := by
  refine ⟨k.phase.trans h.phase,fun w hw => (k.outside w hw).trans (h.outside w hw),?_,?_,?_⟩
  · rw [k.finite,h.finite,Bool.xor_assoc]
  · rw [k.x,h.x,Nat.xor_assoc]
  · rw [k.y,h.y,Nat.xor_assoc]

theorem PointEffect.of_finite (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (F : Bool) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w,w≠r.finite → t.basis w=s.basis w)
    (hv : t.basis r.finite=(s.basis r.finite ^^ F)) : PointEffect r F 0 0 s t := by
  have hh := (List.nodup_cons.mp hn).1
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),hv,?_,?_⟩
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun e => hh (List.mem_append_left _ (e ▸ hw)))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun e => hh (List.mem_append_right _ (e ▸ hw)))

theorem PointEffect.of_x (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (X : Nat) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w∉r.x,t.basis w=s.basis w)
    (hv : regValue r.x t.basis=regValue r.x s.basis ^^^ X) : PointEffect r false X 0 s t := by
  have hh := List.nodup_cons.mp hn
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),?_,hv,?_⟩
  · rw [Bool.xor_false]; exact he _ (fun e => hh.1 (List.mem_append_left _ e))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (fun hx => List.disjoint_left.mp (List.nodup_append'.mp hh.2).2.2 hx hw)

theorem PointEffect.of_y (r : PointReg) (hn : (PointAddLayout.pointWires r).Nodup)
    (Y : Nat) (s t : State) (hp : t.phase=s.phase)
    (he : ∀ w∉r.y,t.basis w=s.basis w)
    (hv : regValue r.y t.basis=regValue r.y s.basis ^^^ Y) : PointEffect r false 0 Y s t := by
  have hh := List.nodup_cons.mp hn
  refine ⟨hp,fun w hw => he w (fun e => hw (by simp [PointAddLayout.pointWires,e])),?_,?_,hv⟩
  · rw [Bool.xor_false]; exact he _ (fun e => hh.1 (List.mem_append_right _ e))
  · rw [Nat.xor_zero]; apply regValue_congr; intro w hw
    exact he w (List.disjoint_left.mp (List.nodup_append'.mp hh.2).2.2 hw)

/-- 外部坐标或标志可跨输出操作使用，输出本身允许为任意位串。 -/
theorem PointEffect.reg {r : PointReg} {F : Bool} {X Y : Nat} {s t : State}
    (h : PointEffect r F X Y s t) (a : List Wire)
    (hd : a.Disjoint (PointAddLayout.pointWires r)) : regValue a t.basis=regValue a s.basis :=
  regValue_congr _ _ _ (fun w hw => h.outside w (List.disjoint_left.mp hd hw))

end ECDSAAdd.Arithmetic
