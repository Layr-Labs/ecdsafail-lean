import ECDSAAdd.Arithmetic.SquareReduceState
import ECDSAAdd.Arithmetic.SquareReduceResources

namespace ECDSAAdd.Arithmetic

private theorem first_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (lo hi : Nat) :
    let U := lo+SquareReduction.c*hi
    Triple (SquareReduceValues L lo hi 0 0 false false)
      (copyRegister none L.low L.value ++ squareFoldAdd L.high L.r L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) false false) ∧
    Triple (SquareReduceValues L lo hi (U%SquareReduction.B) (U/SquareReduction.B) false false)
      (squareFoldClear L.high L.r L.pad L.carry L.cin squareFoldShifts ++ copyRegister none L.low L.value)
      (SquareReduceValues L lo hi 0 0 false false) := by
  dsimp
  constructor
  · intro s m h
    have sp := (squareFirstFold_correct L hw hn s.basis h.work_zero h.cin).1 s m
      ⟨by simpa using h.r_read hw, fun _ _ => rfl⟩
    simp only [h.low,h.high] at sp
    exact ⟨sp.1,h.of_r_frame hw hn _ sp.2⟩
  · intro s m h
    have sp := (squareFirstFold_correct L hw hn s.basis h.work_zero h.cin).2 s m
      ⟨by rw [h.r_read hw,h.low,h.high]; exact Nat.mod_add_div _ _, fun _ _ => rfl⟩
    simpa using And.intro sp.1 (h.of_r_frame hw hn _ sp.2)

private theorem second_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A Q : Nat) (hA : A<SquareReduction.B) (hV : A+SquareReduction.c*Q<2^257)
    (lo hi : Nat) :
    let V := A+SquareReduction.c*Q
    Triple (SquareReduceValues L lo hi A Q false false)
      (squareFoldAdd L.quotient L.extended L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi (V%SquareReduction.B) Q (decide (SquareReduction.B≤V)) false) ∧
    Triple (SquareReduceValues L lo hi (V%SquareReduction.B) Q (decide (SquareReduction.B≤V)) false)
      (squareFoldClear L.quotient L.extended L.pad L.carry L.cin squareFoldShifts)
      (SquareReduceValues L lo hi A Q false false) := by
  have hweight : squareFoldWeight squareFoldShifts=SquareReduction.c := by
    norm_num [squareFoldWeight,squareFoldShifts,SquareReduction.c]
  have primitive (base : BasisState) (hz : regValue (L.pad++L.carry) base=0)
      (hc : base L.cin=false) (hq : regValue L.quotient base=Q) :=
    squareFold_correct L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
      (L.second_nodup hn) (by rw [L.extended_length hw]; omega)
      (by intro j hj; rw [L.quotient_length hw,L.extended_length hw]; simp [squareFoldShifts] at hj; omega)
      (by rw [hw.pad,L.extended_length hw,L.quotient_length hw]; omega)
      (by rw [hw.carry,L.extended_length hw]; omega)
      base hz hc A (by simpa only [L.extended_length hw,hweight,hq,Nat.mul_comm Q] using hV)
  dsimp
  constructor
  · intro s m h
    have sp := (primitive s.basis h.work_zero h.cin h.quotient).1 s m
      ⟨by simpa using h.extended_read hw,fun _ _ => rfl⟩
    simp only [hweight,h.quotient,Nat.mul_comm Q] at sp
    exact ⟨sp.1,h.of_extended_frame hw hn _ sp.2⟩
  · intro s m h
    have he : (decide (SquareReduction.B≤A+SquareReduction.c*Q)).toNat =
        (A+SquareReduction.c*Q)/SquareReduction.B := by
      have hv : A+SquareReduction.c*Q<2*SquareReduction.B := by simpa only [SquareReduction.B,show 2^257=2*2^256 by omega] using hV
      have hb := SquareReduction.carry_bound _ hv
      by_cases hc : SquareReduction.B≤A+SquareReduction.c*Q
      · simp only [hc,decide_true,Bool.toNat_true]
        have hp : 0<SquareReduction.B := by norm_num [SquareReduction.B]
        have hh : 1≤(A+SquareReduction.c*Q)/SquareReduction.B := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hc)
        omega
      · simp only [hc,decide_false,Bool.toNat_false]
        exact (Nat.div_eq_of_lt (by omega)).symm
    have sp := (primitive s.basis h.work_zero h.cin h.quotient).2 s m
      ⟨by rw [h.extended_read hw,he,hweight,h.quotient,Nat.mul_comm Q]; exact Nat.mod_add_div _ _,fun _ _ => rfl⟩
    have hv := h.of_extended_frame hw hn _ sp.2
    simpa [Nat.mod_eq_of_lt hA,show ¬SquareReduction.B≤A by omega] using And.intro sp.1 hv

private theorem third_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (A Q : Nat) (b : Bool) (hW : A+SquareReduction.c*b.toNat<SquareReduction.B)
    (lo hi : Nat) :
    let W := A+SquareReduction.c*b.toNat
    Triple (SquareReduceValues L lo hi A Q b false)
      (maskedAddConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c)
      (SquareReduceValues L lo hi W Q b false) ∧
    Triple (SquareReduceValues L lo hi W Q b false)
      (maskedSubConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c)
      (SquareReduceValues L lo hi A Q b false) := by
  have nd : (L.b::L.cin::(L.mask++L.value++L.carry.take 255)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    have hv := (List.take_sublist 256 L.r).count_le w
    have hc := (List.take_sublist 255 L.carry).count_le w
    simp only [SquareReduceLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    simp only [SquareReduceLayout.value,List.count_append,List.count_cons]
    omega
  have prim (sub : Bool) (base : BasisState) (hz : regValue (L.mask++L.carry.take 255) base=0)
      (hc : base L.cin=false) (X : Nat) :=
    maskedConst_frame sub L.b L.cin L.mask L.value (L.carry.take 255) nd
      (by rw [hw.mask,L.value_length hw]) (by simp [hw.carry,L.value_length hw])
      SquareReduction.c (by norm_num [hw.mask,SquareReduction.c]) base hz hc X
  have clean {X : Nat} {s : BasisState} (h : SquareReduceValues L lo hi X Q b false s) :
      regValue (L.mask++L.carry.take 255) s=0 := by
    apply (regValue_zero _ _).mpr; intro w hh
    simp only [List.mem_append] at hh
    exact hh.elim ((regValue_zero _ _).mp h.mask w)
      (fun hh => (regValue_zero _ _).mp h.carry w (List.mem_of_mem_take hh))
  have hb : (if b then SquareReduction.c else 0)=SquareReduction.c*b.toNat := by cases b <;> simp
  have hA : A<SquareReduction.B := by omega
  dsimp
  constructor
  · intro s m h
    have sp := prim false s.basis (clean h) h.cin A s m ⟨h.value,fun _ _ => rfl⟩
    simp only [Bool.false_eq_true,↓reduceIte,h.bit,hb,L.value_length hw,
      Nat.mod_eq_of_lt (show A+SquareReduction.c*b.toNat<2^256 from hW)] at sp
    exact ⟨sp.1,h.of_value_frame hn _ sp.2⟩
  · intro s m h
    have sp := prim true s.basis (clean h) h.cin (A+SquareReduction.c*b.toNat) s m
      ⟨h.value,fun _ _ => rfl⟩
    have he : A+SquareReduction.c*b.toNat+2^256-SquareReduction.c*b.toNat=A+2^256 := by omega
    simp only [↓reduceIte,h.bit,hb,L.value_length hw,he,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show A<2^256 from hA)] at sp
    exact ⟨sp.1,h.of_value_frame hn _ sp.2⟩

private theorem norm_values (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (W Q : Nat) (b : Bool) (hW : W<SquareReduction.B) (lo hi : Nat) :
    Triple (SquareReduceValues L lo hi W Q b false) (squareNormalize L)
      (SquareReduceValues L lo hi (W%SquareReduction.p) Q b (decide (SquareReduction.p≤W))) ∧
    Triple (SquareReduceValues L lo hi (W%SquareReduction.p) Q b (decide (SquareReduction.p≤W)))
      (squareDenormalize L) (SquareReduceValues L lo hi W Q b false) := by
  constructor
  · intro s m h
    have hz : regValue (L.mask++L.carry) s.basis=0 := by simp [regValue_append,h.mask,h.carry]
    have sp := (squareNormalize_correct L hn hw s.basis hz h.cin W hW).1 s m
      ⟨h.value,h.flag,fun _ _ => rfl⟩
    exact ⟨sp.1,h.of_norm_frame hn _ _ sp.2⟩
  · intro s m h
    have hz : regValue (L.mask++L.carry) s.basis=0 := by simp [regValue_append,h.mask,h.carry]
    have sp := (squareNormalize_correct L hn hw s.basis hz h.cin W hW).2 s m
      ⟨h.value,h.flag,fun _ _ => rfl⟩
    exact ⟨sp.1,h.of_norm_frame hn _ _ sp.2⟩

/-- 约减历史：商 q、第二折叠进位 b、规范化标志 f 保留到外部输出更新以后。 -/
def SquareReduced (L : SquareReduceLayout) (lo hi : Nat) : BasisState → Prop :=
  let U := lo+SquareReduction.c*hi
  let V := U%SquareReduction.B+SquareReduction.c*(U/SquareReduction.B)
  let W := V%SquareReduction.B+SquareReduction.c*(V/SquareReduction.B)
  SquareReduceValues L lo hi ((lo+SquareReduction.B*hi)%SquareReduction.p)
    (U/SquareReduction.B) (decide (SquareReduction.B≤V)) (decide (SquareReduction.p≤W))

/-- 同一合法门列的完整准备与独立前向清理；相位对全部测量记录精确保持。 -/
theorem squareReduce_correct (L : SquareReduceLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (lo hi : Nat) (hlo : lo<SquareReduction.B) (hhi : hi<SquareReduction.B) :
    Triple (SquareReduceValues L lo hi 0 0 false false) (squareReduce L) (SquareReduced L lo hi) ∧
    Triple (SquareReduced L lo hi) (squareReduceClear L) (SquareReduceValues L lo hi 0 0 false false) := by
  let U := lo+SquareReduction.c*hi
  let V := U%SquareReduction.B+SquareReduction.c*(U/SquareReduction.B)
  let b := decide (SquareReduction.B≤V)
  let W := V%SquareReduction.B+SquareReduction.c*(V/SquareReduction.B)
  have hV : V<2*SquareReduction.B := SquareReduction.second_bound lo hi hlo hhi
  have hb : b.toNat=V/SquareReduction.B := by
    have hq := SquareReduction.carry_bound V hV
    by_cases h : SquareReduction.B≤V
    · simp only [b,h,decide_true,Bool.toNat_true]
      have hp : 0<SquareReduction.B := by norm_num [SquareReduction.B]
      have hh : 1≤V/SquareReduction.B := (Nat.le_div_iff_mul_le hp).mpr (by simpa using h)
      omega
    · simp only [b,h,decide_false,Bool.toNat_false]
      exact (Nat.div_eq_of_lt (by omega)).symm
  have hW : W<SquareReduction.B := SquareReduction.third_bound V (SquareReduction.second_fine_bound lo hi hlo hhi)
  have hmod : W%SquareReduction.p=(lo+SquareReduction.B*hi)%SquareReduction.p := by
    dsimp [W,V,U]
    rw [SquareReduction.fold_mod,SquareReduction.fold_mod,SquareReduction.first_mod]
  have f1 := first_values L hw hn lo hi
  have f2 := second_values L hw hn (U%SquareReduction.B) (U/SquareReduction.B)
    (Nat.mod_lt _ (by norm_num [SquareReduction.B]))
    (by simpa only [SquareReduction.B,show 2^257=2*2^256 by omega] using hV) lo hi
  have f3 := third_values L hw hn (V%SquareReduction.B) (U/SquareReduction.B) b
    (by simpa only [hb] using hW) lo hi
  have f4 := norm_values L hw hn W (U/SquareReduction.B) b hW lo hi
  simp only [hb] at f3
  constructor
  · simpa only [squareReduce,SquareReduced,U,V,W,b,hmod,List.append_assoc] using
      f1.1.seq (f2.1.seq (f3.1.seq f4.1))
  · simpa only [squareReduceClear,SquareReduced,U,V,W,b,hmod,List.append_assoc] using
      f4.2.seq (f3.2.seq (f2.2.seq f1.2))

/-- 所有视图外线路逐位保持，准备和恢复使用各自实际支持集。 -/
theorem squareReduce_frame (L : SquareReduceLayout) (hw : L.Widths)
    (m : List Bool) (s : State) (w : Wire) (ho : w∉L.wires) :
    (run (squareReduce L) m s).basis w=s.basis w ∧
    (run (squareReduceClear L) m s).basis w=s.basis w := by
  have hs := squareReduce_wires_subset L hw
  constructor
  · exact run_preserves_outside _ m s w (fun hm => ho (List.mem_toFinset.mp (hs.1 hm)))
  · exact run_preserves_outside _ m s w (fun hm => ho (List.mem_toFinset.mp (hs.2 hm)))

end ECDSAAdd.Arithmetic
