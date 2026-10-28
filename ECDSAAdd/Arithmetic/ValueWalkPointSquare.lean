/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.SquareSubSpec

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def valueWalkPointDialogSquare (L : ControlledPointLayout) : Program :=
  copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256) ++
  squareSub L.dialogSquare ++
  copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256)

private theorem masked_square (K : SquareSubLayout) (c : Wire) (src : List Wire)
    (hw : K.Widths) (hn : (c::src++K.wires).Nodup) (hl : src.length=K.x.length)
    (X Y : Nat) (B : Bool) (hX : X<SquareReduction.p) (s : State) (m : List Bool)
    (hb : s.basis c=B) (hy : regValue src s.basis=Y) (hx : regValue K.out s.basis=X)
    (ha : regValue K.x s.basis=0) (hc : regValue K.work s.basis=0) :
    let C := copyRegister (some c) src K.x
    (run (C++squareSub K++C) m s).phase=s.phase ∧
    regValue K.out (run (C++squareSub K++C) m s).basis=
      (X+SquareReduction.p-(if B then Y*Y else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉K.out → (run (C++squareSub K++C) m s).basis q=s.basis q := by
  dsimp only
  let C := copyRegister (some c) src K.x
  have nd : K.wires.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have cpnd : (src++K.x).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h ⊢
    omega
  have away (q : Wire) (hq : q∈c::src++K.out++K.work) : q∉K.x := by
    intro hh
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  have cno := away c (by simp)
  generalize hs1 : run C (m.take (measurementCount C)) s = s1
  let rest := m.drop (measurementCount C)

  obtain ⟨p1,f1,v1⟩ := copyRegister_correct (some c) src K.x hl cpnd (by simpa using cno)
    s (m.take (measurementCount C))
  change run (copyRegister (some c) src K.x) (m.take (measurementCount C)) s=s1 at hs1
  rw [hs1] at p1 f1 v1
  have a1 : regValue K.x s1.basis=(if B then Y else 0) := by
    simpa only [copyValue,hb,hy,ha,Nat.zero_xor] using v1
  have x1 : regValue K.out s1.basis=X :=
    (regValue_congr _ _ _ (fun q hq => f1 q (away q (by simp [hq])))).trans hx
  have w1 : regValue K.work s1.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => f1 q (away q (by simp [hq])))).trans hc
  obtain ⟨p2,v2⟩ := squareSub_spec K hw nd (if B then Y else 0) X hX s1
    (rest.take (measurementCount (squareSub K))) ⟨⟨a1,x1⟩,w1⟩
  have f2 := squareSub_frame K hw nd (if B then Y else 0) X hX s1
    (rest.take (measurementCount (squareSub K))) a1 x1 w1
  generalize hs2 : run (squareSub K) (rest.take (measurementCount (squareSub K))) s1=s2
  rw [hs2] at p2 v2 f2
  have outAway (q : Wire) (hq : q∈c::src) : q∉K.out := by
    intro hh
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [SquareSubLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  have b2 : s2.basis c=B := (f2 c (outAway c (by simp))).trans ((f1 c cno).trans hb)
  have y2 : regValue src s2.basis=Y :=
    (regValue_congr _ _ _ (fun q hq =>
      (f2 q (outAway q (by simp [hq]))).trans (f1 q (away q (by simp [hq]))))).trans hy
  obtain ⟨p3,f3,v3⟩ := copyRegister_correct (some c) src K.x hl cpnd (by simpa using cno)
    s2 (rest.drop (measurementCount (squareSub K)))
  have av2 : regValue K.x s2.basis=(if B then Y else 0) := v2.1.1
  have a3 : regValue K.x (run C (rest.drop (measurementCount (squareSub K))) s2).basis=0 := by
    simpa only [C,copyValue,b2,y2,av2,Nat.xor_self] using v3
  have result : run (C++squareSub K++C) m s=run C (rest.drop (measurementCount (squareSub K))) s2 := by
    rw [List.append_assoc,run_append]
    change run (squareSub K++C) rest (run C (m.take (measurementCount C)) s)=_
    rw [hs1,run_append,hs2]
  rw [result]
  refine ⟨p3.trans (p2.trans p1),?_,?_⟩
  · have eqv := regValue_congr K.out _ _ (fun q hq => f3 q (away q (by simp [hq])))
    rw [eqv,v2.1.2]
    cases B <;> simp [pow_two]
  · intro q hq
    by_cases hqa : q∈K.x
    · exact (regValue_eq_iff _ _ _).mp (a3.trans ha.symm) q hqa
    · exact (f3 q hqa).trans ((f2 q hq).trans (f1 q hqa))

theorem valueWalkPointDialogSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (valueWalkPointDialogSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (valueWalkPointDialogSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (valueWalkPointDialogSquare L) m s).basis q=s.basis q := by
  have nd : (L.core.generic::L.point.y++L.dialogSquare.wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 2217 (L.dialogPool.drop 256)).count_le q
    have he := congrArg (List.count q) (List.take_append_drop 256 L.dialogPool)
    rw [SquareSubLayout.wires,L.dialogSquare_work hw]
    change (L.core.generic::L.point.y++((L.dialogPool.take 256)++L.point.x++
      (L.dialogPool.drop 256).take 2217)).count q≤1
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h ht he ⊢
    omega
  have ha : regValue L.dialogSquare.x s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (List.take_subset 256 _ hq))
  have hz : regValue L.dialogSquare.work s.basis=0 := by
    rw [L.dialogSquare_work hw]
    exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q
      (List.drop_subset 256 _ (List.take_subset 2217 _ hq)))
  have hp : SquareReduction.p=p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have h := masked_square L.dialogSquare L.core.generic L.point.y
    (L.dialogSquare_widths hw) nd (by simp [dialogSquare,SquareSubLayout.fromPool,point,hw.inputY,L.dialogPool_length hw])
    X Y B (by simpa only [hp] using hX) s m hb hy hx ha hz
  simpa only [valueWalkPointDialogSquare,hp] using h

end ECDSAAdd.Arithmetic
