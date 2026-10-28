import ECDSAAdd.Arithmetic.SkywalkPayloadProgram
import ECDSAAdd.Arithmetic.ConditionalXor
import ECDSAAdd.Math.SkywalkTrace

namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem dialog_p_pos : 0<p := Secp256k1.p_prime.pos
private theorem dialog_p_odd : p%2=1 := by norm_num [p]
private theorem dialog_p_bound : p<2^256 := by norm_num [p]

/-- Physical record pairs are (parity g, swap s), and are read without modification. -/
def skywalkTapeControls (base : BasisState) (rs : List (Wire × Wire)) : List (Bool × Bool) :=
  rs.map (fun r => (base r.1,base r.2))

/-- Actual forward payload replay, in record order. -/
def skywalkDialogReplay (L : ModInPlaceLayout) : List (Wire × Wire) → Program
  | [] => []
  | r::rs => skywalkFieldCell r.1 r.2 L p ++ skywalkDialogReplay L rs

/-- Actual reverse payload replay: reverse record order, using separately proved
forward inverse cells, never reversing measurement instructions. -/
def skywalkDialogUnreplay (L : ModInPlaceLayout) : List (Wire × Wire) → Program
  | [] => []
  | r::rs => skywalkDialogUnreplay L rs ++ skywalkFieldUncell r.1 r.2 L p

/-- Each record/control is disjoint from the payload and all arithmetic scratch. -/
def SkywalkTapeLayout (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire × Wire)) : Prop :=
  ∀ r∈rs,(active::r.2::r.1::L.wires).Nodup

private theorem dialog_work_away (active g swap : Wire) (L : ModInPlaceLayout)
    (hn : (active::swap::g::L.wires).Nodup) (w : Wire) (hw : w∈L.work) : w∉L.z ∧ w∉L.a := by
  have hh := List.nodup_iff_count.mp hn w
  have hk := List.count_pos_iff.mpr hw
  simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hh
  constructor <;> intro hm <;> have hM := List.count_pos_iff.mpr hm <;> omega

private theorem dialog_work_clean (active g swap : Wire) (L : ModInPlaceLayout)
    (hn : (active::swap::g::L.wires).Nodup) (base s : BasisState) (X Y : Nat)
    (hk : regValue L.work base=0) (h : PairFrame L.z L.a base X Y s) : regValue L.work s=0 := by
  apply (regValue_zero _ _).mpr
  intro w hw
  have ha := dialog_work_away active g swap L hn w hw
  rw [h.2.2 w ha.1 ha.2]
  exact (regValue_zero _ _).mp hk w hw

private theorem dialog_cell_bound (q : Nat) (G S : Bool) (X Y : Nat)
    (hp0 : 0<q) (hp : q%2=1) (_hX : X<q) (hY : Y<q) :
    (skywalkFieldNat q G S X Y).1<q ∧ (skywalkFieldNat q G S X Y).2<q := by
  have hd : skywalkSignedNat q G X Y<q := by
    cases G
    · change (X+q-Y)%q<q
      exact Nat.mod_lt _ hp0
    · change (X+Y)%q<q
      exact Nat.mod_lt _ hp0
  have hh := halve_mod_bound q _ hp hd
  cases S <;> simp only [skywalkFieldNat,Bool.false_eq_true,if_false,if_true]
  · exact ⟨hh,hY⟩
  · exact ⟨hY,hh⟩

private theorem dialog_uncell_bound (q : Nat) (G S : Bool) (X Y : Nat)
    (hp0 : 0<q) (hX : X<q) (hY : Y<q) :
    (skywalkFieldUnnat q G S X Y).1<q ∧ (skywalkFieldUnnat q G S X Y).2<q := by
  cases S <;> simp only [skywalkFieldUnnat,Bool.false_eq_true,if_false,if_true]
  · constructor
    · cases G
      · change (((2*X)%q)+Y)%q<q
        exact Nat.mod_lt _ hp0
      · change (((2*X)%q)+q-Y)%q<q
        exact Nat.mod_lt _ hp0
    · exact hY
  · constructor
    · cases G
      · change (((2*Y)%q)+X)%q<q
        exact Nat.mod_lt _ hp0
      · change (((2*Y)%q)+q-X)%q<q
        exact Nat.mod_lt _ hp0
    · exact hX

/-- A leaf cell as a complete two-register frame, on arbitrary Fp inputs. -/
private theorem dialog_leaf_frame (inverse : Bool) (active g swap : Wire) (L : ModInPlaceLayout)
    (hw : L.Widths 256) (hn : (active::swap::g::L.wires).Nodup)
    (base : BasisState) (hk : regValue L.work base=0) (X Y : Fp) :
    Triple (PairFrame L.z L.a base X.val Y.val)
      (if inverse then skywalkFieldUncell g swap L p else skywalkFieldCell g swap L p)
      (PairFrame L.z L.a base
        (if inverse then (skywalkPayloadUncell (base g) (base swap) (X,Y)).1.val
          else (skywalkPayloadCell (base g) (base swap) (X,Y)).1.val)
        (if inverse then (skywalkPayloadUncell (base g) (base swap) (X,Y)).2.val
          else (skywalkPayloadCell (base g) (base swap) (X,Y)).2.val)) := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  have hX := ZMod.val_lt X
  have hY := ZMod.val_lt Y
  have hp : p%2=1 := dialog_p_odd
  have hpn : p<2^256 := dialog_p_bound
  intro st m h
  have control (q : Wire) (hq : q∈[active,swap,g]) : st.basis q=base q :=
    h.2.2 q (ReplayValues.control_outside active swap g L hn q hq).1
      (ReplayValues.control_outside active swap g L hn q hq).2
  have pre : ReplayValues active swap g L (base active) (base swap) (base g) X.val Y.val st.basis :=
    ⟨control active (by simp),control swap (by simp),control g (by simp),h.1,h.2.1,
      dialog_work_clean active g swap L hn base st.basis X.val Y.val hk h⟩
  cases inverse
  · obtain ⟨hf,hv⟩ := skywalkFieldCell_spec active swap g L 256 p X.val Y.val
      (base active) (base swap) (base g) hw hn hp hpn hX hY st m pre
    have hb := dialog_cell_bound p (base g) (base swap) X.val Y.val dialog_p_pos dialog_p_odd hX hY
    have he := skywalkFieldNat_field (base g) (base swap) X.val Y.val hY
    simp only [ZMod.natCast_zmod_val] at he
    have hx := congrArg (fun q : Fp×Fp => q.1.val) he
    have hy := congrArg (fun q : Fp×Fp => q.2.val) he
    simp only at hx hy
    rw [ZMod.val_natCast_of_lt hb.1] at hx
    rw [ZMod.val_natCast_of_lt hb.2] at hy
    refine ⟨hf,hv.2.2.2.1.trans hx,hv.2.2.2.2.1.trans hy,?_⟩
    intro q hz ha
    exact ((skywalkField_frame active swap g L 256 p X.val Y.val (base active) (base swap) (base g)
      hw hn hp hpn hX hY st m pre q hz ha).1).trans (h.2.2 q hz ha)
  · obtain ⟨hf,hv⟩ := skywalkFieldUncell_spec active swap g L 256 p X.val Y.val
      (base active) (base swap) (base g) hw hn hp hpn hX hY st m pre
    have hb := dialog_uncell_bound p (base g) (base swap) X.val Y.val dialog_p_pos hX hY
    have he := skywalkFieldUnnat_field (base g) (base swap) X.val Y.val hX hY
    simp only [ZMod.natCast_zmod_val] at he
    have hx := congrArg (fun q : Fp×Fp => q.1.val) he
    have hy := congrArg (fun q : Fp×Fp => q.2.val) he
    simp only at hx hy
    rw [ZMod.val_natCast_of_lt hb.1] at hx
    rw [ZMod.val_natCast_of_lt hb.2] at hy
    refine ⟨hf,hv.2.2.2.1.trans hx,hv.2.2.2.2.1.trans hy,?_⟩
    intro q hz ha
    exact ((skywalkField_frame active swap g L 256 p X.val Y.val (base active) (base swap) (base g)
      hw hn hp hpn hX hY st m pre q hz ha).2).trans (h.2.2 q hz ha)

/-- Full forward field replay: every record control, source-external bit and scratch bit is preserved. -/
theorem skywalkDialogReplay_spec (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (hw : L.Widths 256) (ht : SkywalkTapeLayout active L rs) (base : BasisState)
    (hk : regValue L.work base=0) (X Y : Fp) :
    Triple (PairFrame L.z L.a base X.val Y.val) (skywalkDialogReplay L rs)
      (PairFrame L.z L.a base
        (skywalkPayloadReplay (skywalkTapeControls base rs) (X,Y)).1.val
        (skywalkPayloadReplay (skywalkTapeControls base rs) (X,Y)).2.val) := by
  induction rs generalizing X Y with
  | nil => intro st m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active L rs := fun q hq => ht q (by simp [hq])
    let Q := skywalkPayloadCell (base r.1) (base r.2) (X,Y)
    have h1 := dialog_leaf_frame false active r.1 r.2 L hw hr base hk X Y
    have h2 := ih ht' Q.1 Q.2
    simpa only [skywalkDialogReplay,skywalkTapeControls,List.map_cons,skywalkPayloadReplay,Q] using h1.seq h2

/-- Full inverse field replay uses the same recorded Boolean controls, in reverse record order. -/
theorem skywalkDialogUnreplay_spec (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (hw : L.Widths 256) (ht : SkywalkTapeLayout active L rs) (base : BasisState)
    (hk : regValue L.work base=0) (X Y : Fp) :
    Triple (PairFrame L.z L.a base X.val Y.val) (skywalkDialogUnreplay L rs)
      (PairFrame L.z L.a base
        (skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)).1.val
        (skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)).2.val) := by
  induction rs generalizing X Y with
  | nil => intro st m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active L rs := fun q hq => ht q (by simp [hq])
    let Q := skywalkPayloadReplayInverse (skywalkTapeControls base rs) (X,Y)
    have h1 := ih ht' X Y
    have h2 := dialog_leaf_frame true active r.1 r.2 L hw hr base hk Q.1 Q.2
    simpa only [skywalkDialogUnreplay,skywalkTapeControls,List.map_cons,skywalkPayloadReplayInverse,Q] using h1.seq h2

/-- Exact static counts of both actual replay streams, including all measurement corrections. -/
theorem skywalkDialogReplay_counts (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (n : Nat) (hw : L.Widths n) (ht : SkywalkTapeLayout active L rs) (hn : 0<n) :
    toffoliCount (skywalkDialogReplay L rs)=rs.length*(9*n-1) ∧
    measurementCount (skywalkDialogReplay L rs)=rs.length*(8*n-1) ∧
    toffoliCount (skywalkDialogUnreplay L rs)=rs.length*(9*n-2) ∧
    measurementCount (skywalkDialogUnreplay L rs)=rs.length*(8*n-2) := by
  induction rs with
  | nil => simp [skywalkDialogReplay,skywalkDialogUnreplay,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active L rs := fun q hq => ht q (by simp [hq])
    have hrg := ReplayValues.control_nodup active r.2 r.1 L hr r.1 (by simp)
    have hc := skywalkField_counts r.1 r.2 L n p hw hrg hn
    have hi := ih ht'
    simp only [skywalkDialogReplay,skywalkDialogUnreplay,toffoliCount_append,measurementCount_append,
      hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,List.length_cons,Nat.add_mul]
    omega

/-- Division preparation doubles the numerator; the equal terminal payload is Clifford-cleared. -/
def skywalkFieldDivision (L : ModInPlaceLayout) (rs : List (Wire×Wire)) : Program :=
  dblInPlace L.unary p ++ skywalkDialogReplay L rs ++ copyRegister none L.z L.a

/-- Multiplication first duplicates its payload, inversely replays the actual records, then halves. -/
def skywalkFieldMultiplication (L : ModInPlaceLayout) (rs : List (Wire×Wire)) : Program :=
  copyRegister none L.z L.a ++ skywalkDialogUnreplay L rs ++ halfInPlace L.unary p
private theorem dialog_double_val (X : Fp) : (2*X.val)%p=(2*X).val := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  have hh := skywalkFieldUnnat_field true false X.val 0 (ZMod.val_lt X) dialog_p_pos
  simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_true,Bool.false_eq_true,if_false,if_true,
    Nat.sub_zero,Nat.add_mod_right,Nat.mod_mod,Nat.cast_zero,add_zero,neg_zero,
    skywalkPayloadUncell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ dialog_p_pos)] at hx
  exact hx

private theorem dialog_half_val (X : Fp) : halveMod p X.val=(X/2).val := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  have hh := skywalkFieldNat_field true false X.val 0 dialog_p_pos
  simp only [skywalkFieldNat,skywalkSignedNat,Bool.false_eq_true,if_false,if_true,
    Nat.mod_eq_of_lt (ZMod.val_lt X),Nat.cast_zero,add_zero,
    skywalkPayloadCell,ZMod.natCast_zmod_val] at hh
  have hx := congrArg (fun q : Fp×Fp => q.1.val) hh
  simp only at hx
  rw [ZMod.val_natCast_of_lt (halve_mod_bound p X.val dialog_p_odd (ZMod.val_lt X))] at hx
  exact hx

private theorem dialog_unary_nat_frame (half : Bool) (active g swap : Wire) (L : ModInPlaceLayout)
    (n q X Y : Nat) (hw : L.Widths n) (hn : (active::swap::g::L.wires).Nodup)
    (ho : q%2=1) (hq : q<2^n) (hX : X<q)
    (base : BasisState) (hk : regValue L.work base=0) :
    Triple (PairFrame L.z L.a base X Y)
      (if half then halfInPlace L.unary q else dblInPlace L.unary q)
      (PairFrame L.z L.a base (if half then halveMod q X else (2*X)%q) Y) := by
  have hu := L.unary_widths n hw
  have hn' := (List.nodup_cons.mp (ReplayValues.unary_nodup active L
    (ReplayValues.control_nodup active swap g L hn active (by simp)))).2
  intro st m h
  have hc := dialog_work_clean active g swap L hn base st.basis X Y hk h
  have keep (w : Wire) (hw : w∉L.z) :
      (run (if half then halfInPlace L.unary q else dblInPlace L.unary q) m st).basis w=st.basis w := by
    have hh := modUnary_frame L.unary n q X hu hn' ho hq hX st m h.1 hc w hw
    cases half
    · exact hh.1
    · exact hh.2
  have hvalue : (run (if half then halfInPlace L.unary q else dblInPlace L.unary q) m st).phase=st.phase ∧
      regValue L.z (run (if half then halfInPlace L.unary q else dblInPlace L.unary q) m st).basis=
        (if half then halveMod q X else (2*X)%q) := by
    cases half
    · obtain ⟨hf,hv⟩ := dblInPlace_spec L.unary n q X hu hn' ho hq hX st m ⟨h.1,hc⟩
      exact ⟨hf,hv.1⟩
    · obtain ⟨hf,hv⟩ := halfInPlace_spec L.unary n q X hu hn' ho hq hX st m ⟨h.1,hc⟩
      exact ⟨hf,hv.1⟩
  have hdis : L.z.Disjoint L.a := by
    apply List.disjoint_left.mpr
    intro w hz ha
    have hh := List.nodup_iff_count.mp hn w
    have hZ := List.count_pos_iff.mpr hz
    have hA := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hh
    omega
  exact ⟨hvalue.1,PairFrame.update_temp L.z L.a base st.basis _ X Y _ hdis h keep hvalue.2⟩

private theorem dialog_unary_frame (half : Bool) (active g swap : Wire) (L : ModInPlaceLayout)
    (hw : L.Widths 256) (hn : (active::swap::g::L.wires).Nodup)
    (base : BasisState) (hk : regValue L.work base=0) (X Y : Fp) :
    Triple (PairFrame L.z L.a base X.val Y.val)
      (if half then halfInPlace L.unary p else dblInPlace L.unary p)
      (PairFrame L.z L.a base (if half then (X/2).val else (2*X).val) Y.val) := by
  letI : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩
  cases half
  · have hh := dialog_unary_nat_frame false active g swap L 256 p X.val Y.val hw hn
      dialog_p_odd dialog_p_bound (ZMod.val_lt X) base hk
    simp only [Bool.false_eq_true,if_false] at hh ⊢
    rw [dialog_double_val X] at hh
    exact hh
  · have hh := dialog_unary_nat_frame true active g swap L 256 p X.val Y.val hw hn
      dialog_p_odd dialog_p_bound (ZMod.val_lt X) base hk
    simp only [if_true] at hh ⊢
    rw [dialog_half_val X] at hh
    exact hh

private theorem dialog_copy_frame (active g swap : Wire) (L : ModInPlaceLayout)
    (hw : L.Widths 256) (hn : (active::swap::g::L.wires).Nodup)
    (base : BasisState) (X Y : Nat) :
    Triple (PairFrame L.z L.a base X Y) (copyRegister none L.z L.a)
      (PairFrame L.z L.a base X (Y^^^X)) := by
  have hlen : L.z.length=L.a.length := by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hnd : (L.z++L.a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd : L.z.Disjoint L.a := (List.nodup_append'.mp hnd).2.2
  intro st m h
  obtain ⟨hf,he,hv⟩ := copyRegister_correct none L.z L.a hlen hnd (by simp) st m
  refine ⟨hf,PairFrame.update_dst L.z L.a base st.basis _ X Y _ hd h he ?_⟩
  simpa only [copyValue,h.1,h.2.1] using hv

/-- Full division leg on the actual signed-rail transcript. The integer-loop bridge must
supply the tape equality; no sampled termination schedule or canonical tie convention is assumed. -/
theorem skywalkFieldDivision_spec (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (hw : L.Widths 256) (ht : SkywalkTapeLayout active L rs) (base : BasisState)
    (hk : regValue L.work base=0) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base rs=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame L.z L.a base Y.val 0) (skywalkFieldDivision L rs)
      (PairFrame L.z L.a base (Y/(x : Fp)).val 0) := by
  cases rs with
  | nil =>
    have hh := congrArg List.length hr
    simp [skywalkTapeControls,SkywalkTrace.trace_length] at hh
  | cons r rs =>
    have hn := ht r (by simp)
    have h1 := dialog_unary_frame false active r.1 r.2 L hw hn base hk Y 0
    have h2 := skywalkDialogReplay_spec active L (r::rs) hw ht base hk (2*Y) 0
    have hq := SkywalkTrace.quotient512 x Y hx0 hx
    rw [←hr] at hq
    rw [hq] at h2
    have h3 := dialog_copy_frame active r.1 r.2 L hw hn base (Y/(x : Fp)).val (Y/(x : Fp)).val
    simp only [Nat.xor_self] at h3
    simpa only [skywalkFieldDivision,List.append_assoc,ZMod.val_zero] using (h1.seq h2).seq h3

/-- Full multiplication leg, with duplicated input and exact modular-half finishing. -/
theorem skywalkFieldMultiplication_spec (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (hw : L.Widths 256) (ht : SkywalkTapeLayout active L rs) (base : BasisState)
    (hk : regValue L.work base=0) (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base rs=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame L.z L.a base Y.val 0) (skywalkFieldMultiplication L rs)
      (PairFrame L.z L.a base (Y*(x : Fp)).val 0) := by
  cases rs with
  | nil =>
    have hh := congrArg List.length hr
    simp [skywalkTapeControls,SkywalkTrace.trace_length] at hh
  | cons r rs =>
    have hn := ht r (by simp)
    have h1 := dialog_copy_frame active r.1 r.2 L hw hn base Y.val 0
    simp only [Nat.zero_xor] at h1
    have h2 := skywalkDialogUnreplay_spec active L (r::rs) hw ht base hk Y Y
    have hq := SkywalkTrace.product512 x Y hx0 hx
    rw [←hr] at hq
    rw [hq] at h2
    have h3 := dialog_unary_frame true active r.1 r.2 L hw hn base hk (2*(Y*(x : Fp))) 0
    have ht2 : (2 : Fp)≠0 := by decide
    have he : (2*(Y*(x : Fp)))/2=Y*(x : Fp) := by field_simp [ht2]
    rw [he] at h3
    simpa only [skywalkFieldMultiplication,List.append_assoc,ZMod.val_zero] using (h1.seq h2).seq h3

/-- Exact complete field-leg counts, including preparation, duplication cleanup and finishing. -/
theorem skywalkFieldLeg_counts (active : Wire) (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (n : Nat) (hw : L.Widths n) (ht : SkywalkTapeLayout active L rs) (hn : 0<n) :
    toffoliCount (skywalkFieldDivision L rs)=2*n-1+rs.length*(9*n-1) ∧
    measurementCount (skywalkFieldDivision L rs)=2*n-1+rs.length*(8*n-1) ∧
    toffoliCount (skywalkFieldMultiplication L rs)=rs.length*(9*n-2)+2*n ∧
    measurementCount (skywalkFieldMultiplication L rs)=rs.length*(8*n-2)+2*n := by
  have hr := skywalkDialogReplay_counts active L rs n hw ht hn
  have hu := modUnary_counts L.unary n p (L.unary_widths n hw) hn
  have hlen : L.z.length=L.a.length := by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none L.z L.a hlen
  have hcopy : toffoliCount (copyRegister none L.z L.a)=0 ∧
      measurementCount (copyRegister none L.z L.a)=0 := by simpa using hc
  refine ⟨?_,?_,?_,?_⟩
  · rw [skywalkFieldDivision,toffoliCount_append,toffoliCount_append,hu.1,hr.1,hcopy.1]
    simp only [Nat.add_zero]
  · rw [skywalkFieldDivision,measurementCount_append,measurementCount_append,hu.2.1,hr.2.1,hcopy.2]
    simp only [Nat.add_zero]
  · rw [skywalkFieldMultiplication,toffoliCount_append,toffoliCount_append,hcopy.1,hr.2.2.1,hu.2.2.1]
    simp only [Nat.zero_add]
  · rw [skywalkFieldMultiplication,measurementCount_append,measurementCount_append,hcopy.2,hr.2.2.2,hu.2.2.2]
    simp only [Nat.zero_add]



end ECDSAAdd.Arithmetic
