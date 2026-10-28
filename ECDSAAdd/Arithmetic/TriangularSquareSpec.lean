import ECDSAAdd.Arithmetic.TriangularSquareProof
import ECDSAAdd.Arithmetic.TriangularSquareResources

namespace ECDSAAdd.Arithmetic

private theorem square_not_dst (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup) (w : Wire)
    (hw : w∈cin::xs++pad++mask++carry) : w∉dst := by
  intro hdw
  have h := List.nodup_iff_count.mp hn w
  have hmem := List.count_pos_iff.mpr hw
  have hd := List.count_pos_iff.mpr hdw
  simp only [List.count_cons,List.count_append] at h hmem
  omega

private theorem square_run (clear : Bool) (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hk : 2*(xs.length-1)-1≤carry.length)
    (X : Nat) (s : State) (m : List Bool) (hx : regValue xs s.basis=X)
    (hv : regValue dst s.basis=if clear then X^2 else 0)
    (hz : regValue (pad++mask++carry) s.basis=0) (hi : s.basis cin=false) :
    let p := if clear then triangularSquareClear xs dst pad mask carry cin
      else triangularSquare xs dst pad mask carry cin
    (run p m s).phase=s.phase ∧
      SquareFrame dst s.basis (if clear then 0 else X^2) (run p m s).basis := by
  let base : BasisState := fun w => if w∈dst then false else s.basis w
  have keep (w : Wire) (hw : w∈cin::xs++pad++mask++carry) : base w=s.basis w := by
    simp only [base,if_neg (square_not_dst xs dst pad mask carry cin hn w hw)]
  have bx : regValue xs base=X := by
    rw [← hx]; exact regValue_congr _ _ _ (fun w hw => keep w (by simp [hw]))
  have bz : regValue (pad++mask++carry) base=0 := by
    rw [← hz]
    exact regValue_congr _ _ _ (fun w hw => keep w (by
      simp only [List.mem_append,List.mem_cons] at hw ⊢; tauto))
  have bi : base cin=false := (keep cin (by simp)).trans hi
  have bd : regValue dst base=0 := (regValue_zero _ _).mpr (fun w hw => by simp [base,hw])
  have pre : SquareFrame dst base (if clear then X^2 else 0) s.basis :=
    ⟨hv,fun w hw => by simp [base,hw]⟩
  have corr := triangularSquare_correct xs dst pad mask carry cin hn hd hp hm hk base bz bi bd
  have result :
      let p := if clear then triangularSquareClear xs dst pad mask carry cin
        else triangularSquare xs dst pad mask carry cin
      (run p m s).phase=s.phase ∧
        SquareFrame dst base (if clear then 0 else X^2) (run p m s).basis := by
    cases clear
    · simpa only [Bool.false_eq_true,if_false,bx] using corr.1 s m pre
    · simpa only [if_true,bx] using corr.2 s m (by simpa only [bx] using pre)
  refine ⟨result.1,result.2.1,?_⟩
  intro w hw
  exact (result.2.2 w hw).trans (by simp [base,hw])

private theorem square_clean (pad mask carry : List Wire) (s : BasisState)
    (hp : regValue pad s=0) (hm : regValue mask s=0) (hc : regValue carry s=0) :
    regValue (pad++mask++carry) s=0 := by
  simp [regValue_append,hp,hm,hc]

/-- 平方写入零目标；输入及全部借用寄存器恢复，测量相位精确保持。 -/
theorem triangularSquare_spec (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hk : 2*(xs.length-1)-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }}
      triangularSquare xs dst pad mask carry cin
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }} := by
  intro s m h
  obtain ⟨⟨⟨⟨⟨hx,hdst⟩,hpad⟩,hmask⟩,hcarry⟩,hcin⟩ := h
  have hr := square_run false xs dst pad mask carry cin hn hd hp hm hk X s m hx hdst
    (square_clean pad mask carry s.basis hpad hmask hcarry) hcin
  have keep (r : List Wire) (hsub : r⊆cin::xs++pad++mask++carry) :
      regValue r (run (triangularSquare xs dst pad mask carry cin) m s).basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw => hr.2.2 w (square_not_dst xs dst pad mask carry cin hn w (hsub hw)))
  refine ⟨hr.1,⟨⟨⟨⟨⟨?_,hr.2.1⟩,?_⟩,?_⟩,?_⟩,?_⟩⟩
  · exact (keep xs (by intro w hw; simp [hw])).trans hx
  · exact (keep pad (by intro w hw; simp [hw])).trans hpad
  · exact (keep mask (by intro w hw; simp [hw])).trans hmask
  · exact (keep carry (by intro w hw; simp [hw])).trans hcarry
  · exact (hr.2.2 cin (square_not_dst xs dst pad mask carry cin hn cin (by simp))).trans hcin

/-- 已知平方由独立的减法门列清零；不倒放任何测量。 -/
theorem triangularSquareClear_spec (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hk : 2*(xs.length-1)-1≤carry.length) (X : Nat) :
    {{ xs=X, dst=X^2, pad=0, mask=0, carry=0, cin=false }}
      triangularSquareClear xs dst pad mask carry cin
    {{ xs=X, dst=0, pad=0, mask=0, carry=0, cin=false }} := by
  intro s m h
  obtain ⟨⟨⟨⟨⟨hx,hdst⟩,hpad⟩,hmask⟩,hcarry⟩,hcin⟩ := h
  have hr := square_run true xs dst pad mask carry cin hn hd hp hm hk X s m hx hdst
    (square_clean pad mask carry s.basis hpad hmask hcarry) hcin
  have keep (r : List Wire) (hsub : r⊆cin::xs++pad++mask++carry) :
      regValue r (run (triangularSquareClear xs dst pad mask carry cin) m s).basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw => hr.2.2 w (square_not_dst xs dst pad mask carry cin hn w (hsub hw)))
  refine ⟨hr.1,⟨⟨⟨⟨⟨?_,hr.2.1⟩,?_⟩,?_⟩,?_⟩,?_⟩⟩
  · exact (keep xs (by intro w hw; simp [hw])).trans hx
  · exact (keep pad (by intro w hw; simp [hw])).trans hpad
  · exact (keep mask (by intro w hw; simp [hw])).trans hmask
  · exact (keep carry (by intro w hw; simp [hw])).trans hcarry
  · exact (hr.2.2 cin (square_not_dst xs dst pad mask carry cin hn cin (by simp))).trans hcin

/-- 目标之外逐线保持，包含未使用的工作区尾部。 -/
theorem triangularSquare_frame (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hk : 2*(xs.length-1)-1≤carry.length)
    (s : State) (m : List Bool) (hv : regValue dst s.basis=0)
    (hpad : regValue pad s.basis=0) (hmask : regValue mask s.basis=0)
    (hcarry : regValue carry s.basis=0) (hcin : s.basis cin=false) :
    ∀ w, w∉dst → (run (triangularSquare xs dst pad mask carry cin) m s).basis w=s.basis w := by
  exact (square_run false xs dst pad mask carry cin hn hd hp hm hk (regValue xs s.basis)
    s m rfl hv (square_clean pad mask carry s.basis hpad hmask hcarry) hcin).2.2

theorem triangularSquareClear_frame (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : xs.length-1≤pad.length)
    (hm : 2*(xs.length-1)≤mask.length) (hk : 2*(xs.length-1)-1≤carry.length)
    (s : State) (m : List Bool) (hv : regValue dst s.basis=(regValue xs s.basis)^2)
    (hpad : regValue pad s.basis=0) (hmask : regValue mask s.basis=0)
    (hcarry : regValue carry s.basis=0) (hcin : s.basis cin=false) :
    ∀ w, w∉dst → (run (triangularSquareClear xs dst pad mask carry cin) m s).basis w=s.basis w := by
  exact (square_run true xs dst pad mask carry cin hn hd hp hm hk (regValue xs s.basis)
    s m rfl hv (square_clean pad mask carry s.basis hpad hmask hcarry) hcin).2.2

end ECDSAAdd.Arithmetic
