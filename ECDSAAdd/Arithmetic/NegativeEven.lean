import ECDSAAdd.Arithmetic.ModUnaryResources
import ECDSAAdd.Arithmetic.ConditionalXor
import ECDSAAdd.Math.KaliskiTerminal

namespace ECDSAAdd.Arithmetic
namespace ModInPlaceLayout

/-- 半倍只借源a和现有scratch；原目标z在整个取负阶段保持。 -/
def sourceUnary (L : ModInPlaceLayout) : ModUnaryLayout :=
  ⟨L.a.take L.low.length,L.a.getD L.low.length L.high,
    L.constant,L.carry,L.cin,L.mask,L.flag⟩

theorem sourceUnary_target (L : ModInPlaceLayout) (n : Nat) (hw : L.Widths n) :
    L.sourceUnary.z=L.a := by
  have hh : n<L.a.length := by rw [hw.core.a]; omega
  have he : L.a.take n++[L.a.getD n L.high]=L.a.take (n+1) := by
    rw [List.take_succ_eq_append_getElem hh]
    simp [List.getD,hh]
  change L.a.take L.low.length++[L.a.getD L.low.length L.high]=L.a
  rw [hw.core.low,he,← hw.core.a,List.take_length]

theorem sourceUnary_work (L : ModInPlaceLayout) : L.sourceUnary.work=L.work := rfl

theorem sourceUnary_widths (L : ModInPlaceLayout) (n : Nat) (hw : L.Widths n) :
    L.sourceUnary.Widths n := by
  exact ⟨by simp [sourceUnary,hw.core.low,hw.core.a],hw.core.constant,hw.core.carry,hw.mask⟩

theorem sourceUnary_nodup (L : ModInPlaceLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) : L.sourceUnary.wires.Nodup := by
  rw [ModUnaryLayout.wires,L.sourceUnary_target n hw,L.sourceUnary_work]
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [wires,List.count_append] at h ⊢
  omega

end ModInPlaceLayout

/-- 正偶r先除2、取负、规范模加倍；不丢失约减分支。 -/
def negativeEven (L : ModInPlaceLayout) (q : Nat) : Program :=
  rotateRight L.a ++ negRaw L q ++ dblInPlace L.sourceUnary q

/-- 显式前向恢复；不逆转任何测量门。 -/
def restoreNegativeEven (L : ModInPlaceLayout) (q : Nat) : Program :=
  halfInPlace L.sourceUnary q ++ negRaw L q ++ rotateLeft L.a

private theorem negativeEven_values (L : ModInPlaceLayout) (n q R : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hq : q<2^n) (ho : q%2=1)
    (hR : 0<R) (hb : R<2*q) (he : R%2=0) (base : BasisState)
    (hwork : regValue L.work base=0) :
    let P := fun X st => regValue L.a st=X ∧ ∀ w,w∉L.a → st w=base w
    Triple (P R) (negativeEven L q) (P (-(R : ZMod q)).val) ∧
    Triple (P (-(R : ZMod q)).val) (restoreNegativeEven L q) (P R) := by
  let P := fun X st => regValue L.a st=X ∧ ∀ w,w∉L.a → st w=base w
  change Triple (P R) _ _ ∧ Triple _ _ (P R)
  have ha : L.a.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have away (w : Wire) (hh : w∈L.work) : w∉L.a := by
    intro hx
    have hc := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hh
    have h2 := List.count_pos_iff.mpr hx
    simp only [ModInPlaceLayout.wires,List.count_append] at hc
    omega
  have clean (X : Nat) (s : BasisState) (hs : P X s) : regValue L.work s=0 :=
    (regValue_congr _ _ _ (fun w hh => hs.2 w (away w hh))).trans hwork
  have neg (X : Nat) (hx : X≤q) : Triple (P X) (negRaw L q) (P (q-X)) := by
    intro s m hs
    obtain ⟨hf,he,hv⟩ := negRaw_correct L n q X hw hnd hq hx s m hs.1 (clean X s.basis hs)
    exact ⟨hf,hv,fun w hh => (he w hh).trans (hs.2 w hh)⟩
  have right (X : Nat) (hx : X%2=0) : Triple (P X) (rotateRight L.a) (P (X/2)) := by
    intro s m hs
    obtain ⟨hf,hv⟩ := rotateRight_spec L.a ha X hx s m hs.1
    exact ⟨hf,hv,fun w hh => ((rotate_frame L.a s m).2.1 w hh).trans (hs.2 w hh)⟩
  have left (X : Nat) (hx : 2*X<2^(n+1)) : Triple (P X) (rotateLeft L.a) (P (2*X)) := by
    intro s m hs
    obtain ⟨hf,hv⟩ := rotateLeft_spec L.a ha X (by simpa [hw.core.a] using hx) s m hs.1
    exact ⟨hf,hv,fun w hh => ((rotate_frame L.a s m).2.2.2 w hh).trans (hs.2 w hh)⟩
  have hu := L.sourceUnary_widths n hw
  have hn := L.sourceUnary_nodup n hw hnd
  have hz := L.sourceUnary_target n hw
  have hd (X : Nat) (hx : X<q) : Triple (P X) (dblInPlace L.sourceUnary q) (P ((2*X)%q)) := by
    intro s m hs
    have hA : regValue L.sourceUnary.z s.basis=X := by rw [hz]; exact hs.1
    have hC : regValue L.sourceUnary.work s.basis=0 := clean X s.basis hs
    obtain ⟨hf,hv⟩ := dblInPlace_spec L.sourceUnary n q X hu hn ho hq hx s m ⟨hA,hC⟩
    simp only [Holds.holds] at hv
    refine ⟨hf,by simpa only [hz] using hv.1,?_⟩
    intro w hh
    exact ((modUnary_frame L.sourceUnary n q X hu hn ho hq hx s m hA hC w
      (by simpa only [hz] using hh)).1).trans (hs.2 w hh)
  have hh (X : Nat) (hx : X<q) : Triple (P X) (halfInPlace L.sourceUnary q) (P (halveMod q X)) := by
    intro s m hs
    have hA : regValue L.sourceUnary.z s.basis=X := by rw [hz]; exact hs.1
    have hC : regValue L.sourceUnary.work s.basis=0 := clean X s.basis hs
    obtain ⟨hf,hv⟩ := halfInPlace_spec L.sourceUnary n q X hu hn ho hq hx s m ⟨hA,hC⟩
    simp only [Holds.holds] at hv
    refine ⟨hf,by simpa only [hz] using hv.1,?_⟩
    intro w haway
    exact ((modUnary_frame L.sourceUnary n q X hu hn ho hq hx s m hA hC w
      (by simpa only [hz] using haway)).2).trans (hs.2 w haway)
  have hv := negative_even_value q R hR hb he
  have hr := negative_even_restore q R ho hR hb he
  have hf := ((right R he).seq (neg (R/2) (by omega))).seq (hd (q-R/2) hv.2.2.1)
  rw [hv.2.2.2] at hf
  have hN : (-(R : ZMod q)).val<q := by
    letI : NeZero q := ⟨by omega⟩
    exact ZMod.val_lt _
  have hhalf := hh _ hN
  rw [hr.1] at hhalf
  have hback := hhalf.seq (neg (q-R/2) (by omega))
  have hfit : 2*(q-(q-R/2))<2^(n+1) := by rw [Nat.pow_succ]; omega
  have hfinish := hback.seq (left _ hfit)
  have hrestore : 2*(q-(q-R/2))=R := by omega
  rw [hrestore] at hfinish
  exact ⟨hf,hfinish⟩

/-- 两个方向均保持目标外的每根线，并对任意测量记录恢复相位。 -/
theorem negativeEven_correct (L : ModInPlaceLayout) (n q R : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hq : q<2^n) (ho : q%2=1)
    (hR : 0<R) (hb : R<2*q) (he : R%2=0) (s : State) (m : List Bool)
    (hwork : regValue L.work s.basis=0) :
    (regValue L.a s.basis=R →
      (run (negativeEven L q) m s).phase=s.phase ∧
      regValue L.a (run (negativeEven L q) m s).basis=(-(R : ZMod q)).val ∧
      ∀ w,w∉L.a → (run (negativeEven L q) m s).basis w=s.basis w) ∧
    (regValue L.a s.basis=(-(R : ZMod q)).val →
      (run (restoreNegativeEven L q) m s).phase=s.phase ∧
      regValue L.a (run (restoreNegativeEven L q) m s).basis=R ∧
      ∀ w,w∉L.a → (run (restoreNegativeEven L q) m s).basis w=s.basis w) := by
  have h := negativeEven_values L n q R hw hnd hq ho hR hb he s.basis hwork
  exact ⟨fun hx => h.1 s m ⟨hx,fun _ _ => rfl⟩,
    fun hx => h.2 s m ⟨hx,fun _ _ => rfl⟩⟩

/-- 供求逆组合的双向寄存器规格：原目标z保持，工作位全部清零。 -/
theorem negativeEven_spec (L : ModInPlaceLayout) (n q R Z : Nat)
    (hw : L.Widths n) (hnd : L.wires.Nodup) (hq : q<2^n) (ho : q%2=1)
    (hR : 0<R) (hb : R<2*q) (he : R%2=0) :
    ({{ L.a=R,L.z=Z,L.work=0 }} negativeEven L q
      {{ L.a=(-(R : ZMod q)).val,L.z=Z,L.work=0 }}) ∧
    ({{ L.a=(-(R : ZMod q)).val,L.z=Z,L.work=0 }} restoreNegativeEven L q
      {{ L.a=R,L.z=Z,L.work=0 }}) := by
  have away (w : Wire) (hh : w∈L.z++L.work) : w∉L.a := by
    intro hx
    have hc := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hh
    have h2 := List.count_pos_iff.mpr hx
    simp only [ModInPlaceLayout.wires,List.count_append] at hc h1
    omega
  constructor
  · intro s m hs
    simp only [Holds.holds] at hs ⊢
    obtain ⟨hf,hv,hkeep⟩ := (negativeEven_correct L n q R hw hnd hq ho hR hb he s m hs.2).1 hs.1.1
    exact ⟨hf,⟨hv,(regValue_congr _ _ _ (fun w hh => hkeep w (away w (by simp [hh])))).trans hs.1.2⟩,
      (regValue_congr _ _ _ (fun w hh => hkeep w (away w (by simp [hh])))).trans hs.2⟩
  · intro s m hs
    simp only [Holds.holds] at hs ⊢
    obtain ⟨hf,hv,hkeep⟩ := (negativeEven_correct L n q R hw hnd hq ho hR hb he s m hs.2).2 hs.1.1
    exact ⟨hf,⟨hv,(regValue_congr _ _ _ (fun w hh => hkeep w (away w (by simp [hh])))).trans hs.1.2⟩,
      (regValue_congr _ _ _ (fun w hh => hkeep w (away w (by simp [hh])))).trans hs.2⟩

/-- 旋转无T/M；取负n、模加倍2n−1、模减半2n。 -/
theorem negativeEven_counts (L : ModInPlaceLayout) (n q : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    toffoliCount (negativeEven L q)=3*n-1 ∧ measurementCount (negativeEven L q)=3*n-1 ∧
    toffoliCount (restoreNegativeEven L q)=3*n ∧ measurementCount (restoreNegativeEven L q)=3*n := by
  have hr := rotate_counts L.a
  have hg := negRaw_counts L n q hw
  have hu := modUnary_counts L.sourceUnary n q (L.sourceUnary_widths n hw) hn
  simp only [negativeEven,restoreNegativeEven,toffoliCount_append,measurementCount_append,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hg.1,hg.2,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2]
  omega

/-- 与规格同一程序的精确支持；恢复多触及一个减半标志。 -/
theorem negativeEven_wires (L : ModInPlaceLayout) (n q : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (negativeEven L q)=(L.a++L.toModAddCoreLayout.work).toFinset ∧
    wires (restoreNegativeEven L q)=(L.a++L.toModAddCoreLayout.work++[L.flag]).toFinset := by
  have hr := rotate_wires L.a
  have hg := negRaw_wires L n q hw
  have hu := modUnary_wires L.sourceUnary n q (L.sourceUnary_widths n hw) hn
  have hz := L.sourceUnary_target n hw
  have hc : L.sourceUnary.core.work=L.toModAddCoreLayout.work := rfl
  have hlen : ¬L.a.length<2 := by rw [hw.core.a]; omega
  simp only [negativeEven,restoreNegativeEven,wires_append,hr.1,hr.2,hlen,if_false,hg,hu.1,hu.2,hz,hc]
  constructor <;> ext w <;> simp [ModInPlaceLayout.sourceUnary]
  tauto

end ECDSAAdd.Arithmetic
