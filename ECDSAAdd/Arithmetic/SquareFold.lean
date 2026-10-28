import ECDSAAdd.Arithmetic.TriangularSquareProof

namespace ECDSAAdd.Arithmetic

/-- 将来源左移 j 位并补零到固定宽度；两段补零互不重叠。 -/
def shiftedSource (src pad : List Wire) (j width : Nat) : List Wire :=
  pad.take j ++ src ++ (pad.drop j).take (width-j-src.length)

def squareFoldAdd (src dst pad carry : List Wire) (cin : Wire) : List Nat → Program
  | [] => []
  | j::js => addInPlace (shiftedSource src pad j dst.length) dst
      (carry.take (dst.length-1)) cin ++ squareFoldAdd src dst pad carry cin js

def squareFoldClear (src dst pad carry : List Wire) (cin : Wire) : List Nat → Program
  | [] => []
  | j::js => squareFoldClear src dst pad carry cin js ++
      subInPlace (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin

def squareFoldWeight (js : List Nat) : Nat := (js.map (fun j => 2^j)).sum

theorem shiftedSource_length (src pad : List Wire) (j width : Nat)
    (hj : j+src.length≤width) (hp : width-src.length≤pad.length) :
    (shiftedSource src pad j width).length=width := by
  simp only [shiftedSource,List.length_append,List.length_take,List.length_drop]
  omega

theorem shiftedSource_value (src pad : List Wire) (j width : Nat)
    (hj : j+src.length≤width) (hp : width-src.length≤pad.length)
    (s : BasisState) (hz : regValue pad s=0) :
    regValue (shiftedSource src pad j width) s=regValue src s*2^j := by
  have hz1 : regValue (pad.take j) s=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hz w (List.mem_of_mem_take hw))
  have hz2 : regValue ((pad.drop j).take (width-j-src.length)) s=0 :=
    (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hz w
      (List.mem_of_mem_drop (List.mem_of_mem_take hw)))
  have hl : (pad.take j).length=j := by simp; omega
  simp only [shiftedSource,regValue_append,hz1,hz2,Nat.mul_zero,Nat.add_zero,Nat.zero_add,hl]
  exact Nat.mul_comm _ _

private theorem shifted_count (src pad : List Wire) (j width : Nat) (w : Wire) :
    (shiftedSource src pad j width).count w ≤ src.count w+pad.count w := by
  have h := (List.take_sublist (width-j-src.length) (pad.drop j)).count_le w
  have he := congrArg (List.count w) (List.take_append_drop j pad)
  simp only [List.count_append] at he
  simp only [shiftedSource,List.count_append]
  omega

/-- 单次移位加减，包含目标外完整逐线保持。 -/
theorem squareFoldStep_frame (sub : Bool) (src dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::(src++dst++pad++carry)).Nodup)
    (hd : 0<dst.length) (hj : j+src.length≤dst.length)
    (hp : dst.length-src.length≤pad.length) (hc : dst.length-1≤carry.length)
    (base : BasisState) (hz : regValue (pad++carry) base=0) (hi : base cin=false) (A : Nat) :
    Triple (SquareFrame dst base A)
      (if sub then subInPlace (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin
       else addInPlace (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin)
      (SquareFrame dst base (if sub then (A+2^dst.length-regValue src base*2^j)%2^dst.length
        else (A+regValue src base*2^j)%2^dst.length)) := by
  let xs := shiftedSource src pad j dst.length
  let cy := carry.take (dst.length-1)
  have hx : xs.length=dst.length := shiftedSource_length src pad j dst.length hj hp
  have hk : cy.length+1=dst.length := by simp [cy,hc]; omega
  have nd : (cin::(xs++dst++cy)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    have hxs := shifted_count src pad j dst.length w
    have hcy := (List.take_sublist (dst.length-1) carry).count_le w
    simp only [List.count_cons,List.count_append] at h ⊢
    dsimp [xs,cy] at *
    omega
  have outside (w : Wire) (hw : w∈cin::(src++pad++carry)) : w∉dst := by
    intro hm
    have h := List.nodup_iff_count.mp hn w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hm
    simp only [List.count_cons,List.count_append] at h h1
    omega
  intro s m h
  have keep (w : Wire) (hw : w∈cin::(src++pad++carry)) := h.2 w (outside w hw)
  have ci : s.basis cin=false := (keep cin (by simp)).trans hi
  have cl (r : List Wire) (hr : r⊆pad++carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hw
    have hw' := hr hw
    rw [keep w (by simp only [List.mem_cons,List.mem_append] at hw' ⊢; tauto)]
    exact (regValue_zero _ _).mp hz w hw'
  have cv : regValue cy s.basis=0 := cl cy (by intro w hw; simp [List.mem_of_mem_take hw])
  have pv : regValue pad s.basis=0 := cl pad (by simp)
  have sv : regValue xs s.basis=regValue src base*2^j := by
    rw [shiftedSource_value src pad j dst.length hj hp s.basis pv]
    rw [regValue_congr src s.basis base (fun w hw => keep w (by simp [hw]))]
  cases sub
  · obtain ⟨ph,fr,v⟩ := addInPlace_correct xs dst cy cin nd hx hk s m
      (fun w hw => (regValue_zero _ _).mp cv w hw)
    refine ⟨ph,?_,fun w hw => (fr w hw).trans (h.2 w hw)⟩
    simpa [sv,h.1,ci,Nat.add_comm] using v
  · have sp := subInPlace_spec xs dst cy cin nd hx hk (regValue src base*2^j) A s m
      ⟨⟨⟨sv,h.1⟩,ci⟩,cv⟩
    refine ⟨sp.1,sp.2.1.1.2,?_⟩
    intro w hw
    have fr : (run (subInPlace xs dst cy cin) m s).basis w=s.basis w := by
      by_cases hs : w∈xs
      · exact (regValue_eq_iff xs _ _).mp (sp.2.1.1.1.trans sv.symm) w hs
      by_cases hc' : w∈cy
      · exact (regValue_eq_iff cy _ _).mp (sp.2.2.trans cv.symm) w hc'
      by_cases he : w=cin
      · subst w; exact sp.2.1.2.trans ci.symm
      apply run_preserves_outside
      rw [subInPlace_wires xs dst cy cin hx hk]
      simpa using (show w∉cin::(xs++dst++cy) by simp [he,hs,hw,hc'])
    exact fr.trans (h.2 w hw)

/-- 同一折叠门列及逆序减法的精确计数。 -/
theorem squareFold_counts (src dst pad carry : List Wire) (cin : Wire) (js : List Nat)
    (hd : 0<dst.length) (hj : ∀j∈js,j+src.length≤dst.length)
    (hp : dst.length-src.length≤pad.length) (hc : dst.length-1≤carry.length) :
    (toffoliCount (squareFoldAdd src dst pad carry cin js)=js.length*(dst.length-1) ∧
     measurementCount (squareFoldAdd src dst pad carry cin js)=js.length*(dst.length-1)) ∧
    (toffoliCount (squareFoldClear src dst pad carry cin js)=js.length*(dst.length-1) ∧
     measurementCount (squareFoldClear src dst pad carry cin js)=js.length*(dst.length-1)) := by
  induction js with
  | nil => simp [squareFoldAdd,squareFoldClear,toffoliCount,measurementCount]
  | cons j js ih =>
    have hx := shiftedSource_length src pad j dst.length (hj j (by simp)) hp
    have hk : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
    have ha := addInPlace_counts (shiftedSource src pad j dst.length) dst _ cin hx hk
    have hs := subInPlace_counts (shiftedSource src pad j dst.length) dst _ cin hx hk
    have ht := ih (fun k hk => hj k (by simp [hk]))
    simp only [squareFoldAdd,squareFoldClear,toffoliCount_append,measurementCount_append,
      ha.1,ha.2,hs.1,hs.2,ht.1.1,ht.1.2,ht.2.1,ht.2.2,List.length_cons,Nat.add_mul,Nat.one_mul]
    simp only [Nat.add_comm,and_self]

/-- 正向累加和逆序清理的配对规格，所有部分和均由最终界保证不溢出。 -/
theorem squareFold_correct (src dst pad carry : List Wire) (cin : Wire) (js : List Nat)
    (hn : (cin::(src++dst++pad++carry)).Nodup)
    (hd : 0<dst.length) (hj : ∀j∈js,j+src.length≤dst.length)
    (hp : dst.length-src.length≤pad.length) (hc : dst.length-1≤carry.length)
    (base : BasisState) (hz : regValue (pad++carry) base=0) (hi : base cin=false)
    (A : Nat) (hb : A+regValue src base*squareFoldWeight js<2^dst.length) :
    Triple (SquareFrame dst base A) (squareFoldAdd src dst pad carry cin js)
      (SquareFrame dst base (A+regValue src base*squareFoldWeight js)) ∧
    Triple (SquareFrame dst base (A+regValue src base*squareFoldWeight js))
      (squareFoldClear src dst pad carry cin js) (SquareFrame dst base A) := by
  induction js generalizing A with
  | nil =>
    simp only [squareFoldWeight,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero,
      squareFoldAdd,squareFoldClear]
    constructor <;> intro s m h <;> exact ⟨rfl,h⟩
  | cons j js ih =>
    have he : A+regValue src base*squareFoldWeight (j::js)=
        (A+regValue src base*2^j)+regValue src base*squareFoldWeight js := by
      simp [squareFoldWeight,Nat.mul_add,Nat.add_assoc]
    rw [he] at hb ⊢
    have hm : A+regValue src base*2^j<2^dst.length := by omega
    have ha : A<2^dst.length := by omega
    have hf := squareFoldStep_frame false src dst pad carry cin hn hd
      (hj j (by simp)) hp hc base hz hi A
    simp only [Bool.false_eq_true,↓reduceIte,Nat.mod_eq_of_lt hm] at hf
    have hg := squareFoldStep_frame true src dst pad carry cin hn hd
      (hj j (by simp)) hp hc base hz hi (A+regValue src base*2^j)
    have hu : A+regValue src base*2^j+2^dst.length-regValue src base*2^j=A+2^dst.length := by omega
    simp only [↓reduceIte,hu,Nat.add_mod_right,Nat.mod_eq_of_lt ha] at hg
    have ht := ih (fun k hk => hj k (by simp [hk])) (A+regValue src base*2^j) hb
    exact ⟨hf.seq ht.1,ht.2.seq hg⟩

/-- 折叠只触及来源、目标和给定工作区，不借用其它线路。 -/
theorem squareFold_wires_subset (src dst pad carry : List Wire) (cin : Wire) (js : List Nat)
    (hd : 0<dst.length) (hj : ∀j∈js,j+src.length≤dst.length)
    (hp : dst.length-src.length≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (squareFoldAdd src dst pad carry cin js)⊆(cin::(src++dst++pad++carry)).toFinset ∧
    wires (squareFoldClear src dst pad carry cin js)⊆(cin::(src++dst++pad++carry)).toFinset := by
  induction js with
  | nil => simp [squareFoldAdd,squareFoldClear,wires]
  | cons j js ih =>
    have hx := shiftedSource_length src pad j dst.length (hj j (by simp)) hp
    have hk : (carry.take (dst.length-1)).length+1=dst.length := by simp [hc]; omega
    have step : (cin::(shiftedSource src pad j dst.length++dst++carry.take (dst.length-1))).toFinset⊆
        (cin::(src++dst++pad++carry)).toFinset := by
      intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hw ⊢
      rcases hw with he|hs|hy|hk'
      · exact Or.inl he
      · have hs' := List.count_pos_iff.mpr hs
        have hct := shifted_count src pad j dst.length w
        have hh : w∈src ∨ w∈pad := by
          by_contra h
          simp only [not_or] at h
          have h1 := List.count_eq_zero.mpr h.1
          have h2 := List.count_eq_zero.mpr h.2
          omega
        tauto
      · tauto
      · have hh := List.mem_of_mem_take hk'
        tauto
    have ht := ih (fun k hk => hj k (by simp [hk]))
    simp only [squareFoldAdd,squareFoldClear,wires_append,
      addInPlace_wires _ _ _ _ hx hk,subInPlace_wires _ _ _ _ hx hk]
    exact ⟨Finset.union_subset step ht.1,Finset.union_subset ht.2 step⟩

end ECDSAAdd.Arithmetic
