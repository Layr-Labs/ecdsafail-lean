import ECDSAAdd.Arithmetic.CuccaroSignedSquareResources

namespace ECDSAAdd.Arithmetic

theorem notRegister_proper (r : List Wire) : ProperProgram (notRegister r) := by
  induction r with
  | nil => simp [notRegister,ProperProgram]
  | cons q r ih => simp [notRegister,ProperProgram,ProperGate]

theorem xorWhenFalse_proper (c : Wire) (ys : List Wire)
    (hnd : (c::ys).Nodup) : ProperProgram (xorWhenFalse c ys) := by
  induction ys with
  | nil => simp [xorWhenFalse,ProperProgram]
  | cons y ys ih =>
    have hcy : c≠y := by
      intro e; subst y; simp at hnd
    have ht : (c::ys).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hnd q
      simp only [List.count_cons] at h ⊢
      omega
    rw [xorWhenFalse,properProgram_append]
    constructor
    · simpa [ProperProgram,ProperGate] using hcy
    · exact ih ht

theorem copyRegister_none_proper (src dst : List Wire)
    (hnd : (src++dst).Nodup) : ProperProgram (copyRegister none src dst) := by
  induction src generalizing dst with
  | nil => simp [copyRegister,ProperProgram]
  | cons a src ih =>
    cases dst with
    | nil => simp [copyRegister,ProperProgram]
    | cons b dst =>
      have hab : a≠b := by
        intro e; subst b
        have h := List.nodup_iff_count.mp hnd a
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have ht : (src++dst).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      rw [copyRegister,properProgram_append]
      constructor
      · intro i hi
        simp only [copyGate,List.mem_singleton] at hi
        subst i
        exact hab
      · exact ih dst ht

theorem cuccaroMaj_proper (a b cin : Wire) (hnd : [a,b,cin].Nodup) :
    ProperProgram (cuccaroMaj a b cin) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  simp [cuccaroMaj,ProperProgram,ProperGate,hab,hac,
    Ne.symm hab,Ne.symm hac]

theorem cuccaroUma_proper (a b cin : Wire) (hnd : [a,b,cin].Nodup) :
    ProperProgram (cuccaroUma a b cin) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hnd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := hnd
  simp [cuccaroUma,ProperProgram,ProperGate,hac,
    Ne.symm hab,Ne.symm hac,Ne.symm hbc]

theorem cuccaroAdd_proper (a b : List Wire) (cin : Wire)
    (hnd : (cin::a++b).Nodup) : ProperProgram (cuccaroAdd a b cin) := by
  induction a generalizing b cin with
  | nil => cases b <;> simp [cuccaroAdd,ProperProgram]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases b with
      | nil => simp [cuccaroAdd,ProperProgram]
      | cons y ys =>
        cases ys with
        | nil =>
          have hxy : x≠y := by
            intro e; subst y
            have h := List.nodup_iff_count.mp hnd x
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            omega
          have hcy : cin≠y := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hnd y
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            omega
          simpa [cuccaroAdd,ProperProgram,ProperGate] using And.intro hxy hcy
        | cons y' ys' => simp [cuccaroAdd,ProperProgram]
    | cons x' xs' =>
      cases b with
      | nil => simp [cuccaroAdd,ProperProgram]
      | cons y ys =>
        cases ys with
        | nil => simp [cuccaroAdd,ProperProgram]
        | cons y' ys' =>
          have n0 := List.nodup_cons.mp hnd
          have nap := List.nodup_append'.mp n0.2
          have na := List.nodup_cons.mp nap.1
          have nb := List.nodup_cons.mp nap.2.1
          have dis := nap.2.2
          have hcx : cin≠x := fun e => n0.1 (by simp [e])
          have hcy : cin≠y := fun e => n0.1 (by simp [e])
          have hxy : x≠y := fun e =>
            List.disjoint_left.mp dis (List.mem_cons_self) (by simp [e])
          have h3 : [x,y,cin].Nodup := by
            simp [hxy,Ne.symm hcx,Ne.symm hcy]
          have ht : (x::(x'::xs')++(y'::ys')).Nodup := by
            apply List.nodup_append'.mpr
            refine ⟨nap.1,(List.nodup_cons.mp nap.2.1).2,?_⟩
            apply List.disjoint_left.mpr
            intro q hqa hqb
            exact List.disjoint_left.mp dis hqa (List.mem_cons_of_mem y hqb)
          simp only [cuccaroAdd,properProgram_append]
          exact ⟨cuccaroMaj_proper x y cin h3,⟨ih (y'::ys') x ht,
            cuccaroUma_proper x y cin h3⟩⟩

theorem cuccaroSub_proper (a b : List Wire) (cin : Wire)
    (hnd : (cin::a++b).Nodup) : ProperProgram (cuccaroSub a b cin) := by
  simp only [cuccaroSub,properProgram_append]
  exact ⟨⟨notRegister_proper b,cuccaroAdd_proper a b cin hnd⟩,notRegister_proper b⟩

theorem signedSquareTop_proper (xs dst : List Wire)
    (hnd : (xs++dst).Nodup) : ProperProgram (signedSquareTop xs dst) := by
  induction xs generalizing dst with
  | nil => simp [signedSquareTop,ProperProgram]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases dst with
      | nil => simp [signedSquareTop,ProperProgram]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,ProperProgram]
        | cons z zs =>
          have hxz : x≠z := by
            intro e; subst z
            have h := List.nodup_iff_count.mp hnd x
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            omega
          simpa [signedSquareTop,ProperProgram] using hxz
    | cons y ys =>
      cases dst with
      | nil => simp [signedSquareTop,ProperProgram]
      | cons a ds =>
        cases ds with
        | nil => simp [signedSquareTop,ProperProgram]
        | cons b tail =>
          have ht : (y::ys++tail).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := List.nodup_iff_count.mp hnd q
            simp only [List.count_cons,List.count_append] at h ⊢
            omega
          simpa [signedSquareTop] using ih tail ht

theorem signedDiagLoad_proper (cin : Wire) (xs mask : List Wire)
    (hnd : (cin::xs++mask).Nodup) : ProperProgram (signedDiagLoad xs mask cin) := by
  let low := xs.take (xs.length-1)
  let mlow := mask.take (xs.length-1)
  have ndcopy : (low++mlow).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hx := (List.take_sublist (xs.length-1) xs).count_le q
    have hm := (List.take_sublist (xs.length-1) mask).count_le q
    simp only [low,mlow,List.count_cons,List.count_append] at h ⊢
    omega
  have ndxor : (cin::mlow).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hm := (List.take_sublist (xs.length-1) mask).count_le q
    simp only [mlow,List.count_cons,List.count_append] at h ⊢
    omega
  simp only [signedDiagLoad,properProgram_append]
  exact ⟨copyRegister_none_proper low mlow ndcopy,xorWhenFalse_proper cin mlow ndxor⟩

theorem signedDiagUnload_proper (cin : Wire) (xs mask : List Wire)
    (hnd : (cin::xs++mask).Nodup) : ProperProgram (signedDiagUnload xs mask cin) := by
  let low := xs.take (xs.length-1)
  let mlow := mask.take (xs.length-1)
  have ndcopy : (low++mlow).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hx := (List.take_sublist (xs.length-1) xs).count_le q
    have hm := (List.take_sublist (xs.length-1) mask).count_le q
    simp only [low,mlow,List.count_cons,List.count_append] at h ⊢
    omega
  have ndxor : (cin::mlow).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hm := (List.take_sublist (xs.length-1) mask).count_le q
    simp only [mlow,List.count_cons,List.count_append] at h ⊢
    omega
  simp only [signedDiagUnload,properProgram_append]
  exact ⟨xorWhenFalse_proper cin mlow ndxor,copyRegister_none_proper low mlow ndcopy⟩

theorem cuccaroSignedSquareRow_proper (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) :
    ProperProgram (cuccaroSignedSquareRow c xs dst pad carry) := by
  have ndprefix : (c::dst.take xs.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have ht := (List.take_sublist xs.length dst).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have nddst : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndadd : (c::(xs++pad.take 1)++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hp := (List.take_sublist 1 pad).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  simp only [cuccaroSignedSquareRow,properProgram_append]
  exact ⟨⟨xorWhenFalse_proper c (dst.take xs.length) ndprefix,
    cuccaroAdd_proper (xs++pad.take 1) dst c ndadd⟩,xorWhenFalse_proper c dst nddst⟩

theorem cuccaroSignedSquareRows_proper (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) :
    ProperProgram (cuccaroSignedSquareRows xs dst pad carry) := by
  induction xs generalizing dst with
  | nil => simp [cuccaroSignedSquareRows,ProperProgram]
  | cons c xs ih =>
    cases xs with
    | nil => simp [cuccaroSignedSquareRows,ProperProgram]
    | cons d tail =>
      let rest := d::tail
      let row := (dst.drop 1).take (rest.length+1)
      let dst2 := dst.drop 2
      have ndrow : (c::rest++row++pad++carry).Nodup := by
        have rowSub : row.Sublist dst :=
          (List.take_sublist (rest.length+1) (dst.drop 1)).trans (List.drop_sublist 1 dst)
        have pre := (List.Sublist.refl (c::rest)).append rowSub
        have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
        have sub : (c::rest++row++pad++carry).Sublist
            (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
        exact sub.nodup hnd
      have ndrec : (rest++dst2++pad++carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := List.nodup_iff_count.mp hnd q
        have hd := (List.drop_sublist 2 dst).count_le q
        simp only [rest,dst2,List.count_cons,List.count_append] at h ⊢
        omega
      simp only [cuccaroSignedSquareRows,properProgram_append]
      exact ⟨cuccaroSignedSquareRow_proper c rest row pad carry ndrow,ih dst2 ndrec⟩

theorem cuccaroSignedDiagSub_proper (cin : Wire) (xs dst mask carry : List Wire)
    (hnd : (cin::xs++dst++mask++carry).Nodup) :
    ProperProgram (cuccaroSignedDiagSub xs dst mask carry cin) := by
  have ndload : (cin::xs++mask).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndarith : (cin::signedDiagSource xs mask++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hm := (List.take_sublist xs.length mask).count_le q
    simp only [signedDiagSource,List.count_cons,List.count_append] at h ⊢
    omega
  simp only [cuccaroSignedDiagSub,properProgram_append]
  exact ⟨signedDiagLoad_proper cin xs mask ndload,
    ⟨cuccaroSub_proper (signedDiagSource xs mask) dst cin ndarith,
      signedDiagUnload_proper cin xs mask ndload⟩⟩

theorem cuccaroSignedTriangularSquare_proper (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup) :
    ProperProgram (cuccaroSignedTriangularSquare xs dst pad mask carry cin) := by
  have ndrows : (xs++dst++pad++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndtop : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have nddiag : (cin::xs++dst++mask++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  cases xs with
  | nil => simp [cuccaroSignedTriangularSquare,ProperProgram]
  | cons x tail =>
    cases tail with
    | nil =>
      cases dst with
      | nil =>
        simp only [cuccaroSignedTriangularSquare,properProgram_append]
        exact ⟨cuccaroSignedSquareRows_proper [x] [] pad carry ndrows,
          ⟨signedSquareTop_proper [x] [] ndtop,
            cuccaroSignedDiagSub_proper cin [x] [] mask carry nddiag⟩⟩
      | cons z zs =>
        have hxz : x≠z := by
          intro e; subst z
          have h := List.nodup_iff_count.mp hnd x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        simpa [cuccaroSignedTriangularSquare,ProperProgram,ProperGate] using hxz
    | cons y ys =>
      simp only [cuccaroSignedTriangularSquare,properProgram_append]
      exact ⟨cuccaroSignedSquareRows_proper (x::y::ys) dst pad carry ndrows,
        ⟨signedSquareTop_proper (x::y::ys) dst ndtop,
          cuccaroSignedDiagSub_proper cin (x::y::ys) dst mask carry nddiag⟩⟩

theorem cuccaroSignedTriangularSquare_roundtrip (cin : Wire)
    (xs dst pad mask carry : List Wire)
    (hnd : (cin::xs++dst++pad++mask++carry).Nodup)
    (s : State) (m₁ m₂ : List Bool) :
    run (cuccaroSignedTriangularSquareClear xs dst pad mask carry cin) m₂
      (run (cuccaroSignedTriangularSquare xs dst pad mask carry cin) m₁ s)=s := by
  apply run_reverse_proper
  exact cuccaroSignedTriangularSquare_proper cin xs dst pad mask carry hnd

end ECDSAAdd.Arithmetic
