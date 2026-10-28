import ECDSAAdd.Arithmetic.ReplayCellResources
import ECDSAAdd.Arithmetic.ModUnaryResources
import ECDSAAdd.Math.SkywalkPayload
import ECDSAAdd.Arithmetic.SkywalkSignedModAdd

namespace ECDSAAdd.Arithmetic

/-- Exact optimized signed add, with addition for g=true and subtraction for g=false.
The copied source mask is restored and Clifford-cleared after one modular-add core. -/
def skywalkSignedAdd (g : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  skywalkSignedModAdd g L p

/-- Exact butterfly reference cell. Halving is unconditional; only the sign and swap are recorded. -/
def skywalkFieldCell (g swap : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  skywalkSignedAdd g L p ++ halfInPlace L.unary p ++
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length)

/-- Independent forward implementation of the inverse: swap, double, opposite signed add. -/
def skywalkFieldUncell (g swap : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length) ++
  dblInPlace L.unary p ++ [.X g] ++ skywalkSignedAdd g L p ++ [.X g]

def skywalkSignedNat (p : Nat) (G : Bool) (X Y : Nat) : Nat :=
  if G then (X+Y)%p else (X+p-Y)%p

def skywalkFieldNat (p : Nat) (G S : Bool) (X Y : Nat) : Nat × Nat :=
  let T := halveMod p (skywalkSignedNat p G X Y)
  if S then (Y,T) else (T,Y)

def skywalkFieldUnnat (p : Nat) (G S : Bool) (X Y : Nat) : Nat × Nat :=
  let A := if S then Y else X
  let B := if S then X else Y
  (skywalkSignedNat p (!G) ((2*A)%p) B,B)

private theorem skywalk_toggle_step (active swap g : Wire) (L : ModInPlaceLayout)
    (C S G : Bool) (X Y : Nat) (hnd : (active::swap::g::L.wires).Nodup) :
    Triple (ReplayValues active swap g L C S G X Y) [.X g]
      (ReplayValues active swap g L C S (!G) X Y) := by
  intro st m h
  have hg := ReplayValues.control_nodup active swap g L hnd g (by simp)
  have hga : g≠active := by
    intro he
    subst g
    simp at hnd
  have hgs : g≠swap := by
    intro he
    subst g
    simp at hnd
  have keep (w : Wire) (hw : w∈L.wires) : (run [.X g] m st).basis w=st.basis w := by
    have hwg : w≠g := fun he => (List.nodup_cons.mp hg).1 (he ▸ hw)
    simp [run,writeBit,hwg]
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · simpa [run,writeBit,Ne.symm hga] using h.1
  · simpa [run,writeBit,Ne.symm hgs] using h.2.1
  · simpa [run,writeBit] using congrArg Bool.not h.2.2.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (by simp [ModInPlaceLayout.wires,hw]))).trans h.2.2.2.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (by simp [ModInPlaceLayout.wires,hw]))).trans h.2.2.2.2.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (by simp [ModInPlaceLayout.wires,hw]))).trans h.2.2.2.2.2

/-- Standalone signed field addition; controls, source, work and phase are restored for every record. -/
theorem skywalkSignedAdd_spec (active swap g : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C S G : Bool) (hw : L.Widths n)
    (hnd : (active::swap::g::L.wires).Nodup) (hp : 0<p) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap g L C S G X Y) (skywalkSignedAdd g L p)
      (ReplayValues active swap g L C S G (skywalkSignedNat p G X Y) Y) := by
  intro st m h
  have hg := ReplayValues.control_nodup active swap g L hnd g (by simp)
  obtain ⟨hf,hv⟩ := skywalkSignedModAdd_spec g L n p Y X G hw hg hp hpn (by omega) hX
    st m ⟨⟨⟨h.2.2.1,h.2.2.2.2.1⟩,h.2.2.2.1⟩,h.2.2.2.2.2⟩
  simp only [Holds.holds] at hv
  have keep (q : Wire) (hq : q∉L.z) :=
    (skywalkSignedModAdd_correct g L n p Y X G hw hg hp hpn (by omega) hX st m
      h.2.2.1 h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2).2.2 q hq
  exact ⟨hf,(keep active (ReplayValues.control_outside active swap g L hnd active (by simp)).1).trans h.1,
    (keep swap (ReplayValues.control_outside active swap g L hnd swap (by simp)).1).trans h.2.1,
    hv.1.1.1,hv.1.2,hv.1.1.2,hv.2⟩

private theorem skywalk_unary_step (half : Bool) (active swap g : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C S G : Bool) (hw : L.Widths n)
    (hnd : (active::swap::g::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n) (hX : X<p) :
    Triple (ReplayValues active swap g L C S G X Y)
      (if half then halfInPlace L.unary p else dblInPlace L.unary p)
      (ReplayValues active swap g L C S G (if half then halveMod p X else (2*X)%p) Y) := by
  intro st m h
  have hn := (List.nodup_cons.mp (ReplayValues.unary_nodup active L
    (ReplayValues.control_nodup active swap g L hnd active (by simp)))).2
  have hu := L.unary_widths n hw
  have hz : regValue L.unary.z st.basis=X := h.2.2.2.1
  have hk : regValue L.unary.work st.basis=0 := h.2.2.2.2.2
  have hspec : (run (if half then halfInPlace L.unary p else dblInPlace L.unary p) m st).phase=st.phase ∧
      regValue L.z (run (if half then halfInPlace L.unary p else dblInPlace L.unary p) m st).basis=
        (if half then halveMod p X else (2*X)%p) ∧
      regValue L.work (run (if half then halfInPlace L.unary p else dblInPlace L.unary p) m st).basis=0 := by
    cases half
    · obtain ⟨hf,hv⟩ := dblInPlace_spec L.unary n p X hu hn hp hpn hX st m ⟨hz,hk⟩
      exact ⟨hf,hv.1,hv.2⟩
    · obtain ⟨hf,hv⟩ := halfInPlace_spec L.unary n p X hu hn hp hpn hX st m ⟨hz,hk⟩
      exact ⟨hf,hv.1,hv.2⟩
  have keep (q : Wire) (hq : q∉L.z) :
      (run (if half then halfInPlace L.unary p else dblInPlace L.unary p) m st).basis q=st.basis q := by
    have hh := modUnary_frame L.unary n p X hu hn hp hpn hX st m hz hk q hq
    cases half
    · exact hh.1
    · exact hh.2
  have outside (q : Wire) (hq : q∈[active,swap,g]) : q∉L.z :=
    (ReplayValues.control_outside active swap g L hnd q hq).1
  refine ⟨hspec.1,(keep active (outside active (by simp))).trans h.1,
    (keep swap (outside swap (by simp))).trans h.2.1,
    (keep g (outside g (by simp))).trans h.2.2.1,hspec.2.1,?_,hspec.2.2⟩
  apply Eq.trans (regValue_congr _ _ _ ?_) h.2.2.2.2.1
  intro q hq
  apply keep q
  intro hzq
  have hh := List.nodup_iff_count.mp
    (List.nodup_cons.mp (ReplayValues.control_nodup active swap g L hnd active (by simp))).2 q
  have ha := List.count_pos_iff.mpr hq
  have hb := List.count_pos_iff.mpr hzq
  simp only [ModInPlaceLayout.wires,List.count_append] at hh
  omega

/-- Full exact forward butterfly gate interface, including source/work/control/phase restoration. -/
theorem skywalkFieldCell_spec (active swap g : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C S G : Bool) (hw : L.Widths n)
    (hnd : (active::swap::g::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap g L C S G X Y) (skywalkFieldCell g swap L p)
      (ReplayValues active swap g L C S G (skywalkFieldNat p G S X Y).1 (skywalkFieldNat p G S X Y).2) := by
  have hp0 : 0<p := by omega
  let A := skywalkSignedNat p G X Y
  have ha : A<p := by dsimp [A,skywalkSignedNat]; split <;> exact Nat.mod_lt _ hp0
  have hh := halve_mod_bound p A hp ha
  have h1 := skywalkSignedAdd_spec active swap g L n p X Y C S G hw hnd hp0 hpn hX hY
  have h2 := skywalk_unary_step true active swap g L n p A Y C S G hw hnd hp hpn ha
  have h3 := ReplayValues.swap_step active swap g L n (halveMod p A) Y C S G hw hnd (by omega) (by omega)
  have hall := (h1.seq h2).seq h3
  cases S <;> simpa [skywalkFieldCell,skywalkFieldNat,A,List.append_assoc] using hall

/-- Full exact inverse butterfly gate interface; it never reverses measurement instructions. -/
theorem skywalkFieldUncell_spec (active swap g : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C S G : Bool) (hw : L.Widths n)
    (hnd : (active::swap::g::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) :
    Triple (ReplayValues active swap g L C S G X Y) (skywalkFieldUncell g swap L p)
      (ReplayValues active swap g L C S G (skywalkFieldUnnat p G S X Y).1 (skywalkFieldUnnat p G S X Y).2) := by
  let A := if S then Y else X
  let B := if S then X else Y
  have ha : A<p := by dsimp [A]; split <;> assumption
  have hb : B<p := by dsimp [B]; split <;> assumption
  have hp0 : 0<p := by omega
  have hd : (2*A)%p<p := Nat.mod_lt _ hp0
  have h1 := ReplayValues.swap_step active swap g L n X Y C S G hw hnd (by omega) (by omega)
  have h2 := skywalk_unary_step false active swap g L n p A B C S G hw hnd hp hpn ha
  have h3 := skywalk_toggle_step active swap g L C S G ((2*A)%p) B hnd
  have h4 := skywalkSignedAdd_spec active swap g L n p ((2*A)%p) B C S (!G) hw hnd hp0 hpn hd hb
  have h5 := skywalk_toggle_step active swap g L C S (!G) (skywalkSignedNat p (!G) ((2*A)%p) B) B hnd
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  cases S <;> simpa [skywalkFieldUncell,skywalkFieldUnnat,A,B,List.append_assoc] using hall

/-- Same actual gate streams as the specifications; static counts include all correction branches. -/
theorem skywalkField_counts (g swap : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (_hnd : (g::L.wires).Nodup) (hn : 0<n) :
    toffoliCount (skywalkFieldCell g swap L p)=9*n-1 ∧
    measurementCount (skywalkFieldCell g swap L p)=8*n-1 ∧
    toffoliCount (skywalkFieldUncell g swap L p)=9*n-2 ∧
    measurementCount (skywalkFieldUncell g swap L p)=8*n-2 := by
  have hz : L.z.length=n+1 := by simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low]
  have hl : (L.z.take L.low.length).length=n := by simp [hw.core.low,hz]
  have hr : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have ca := copyRegister_counts (some swap) (L.z.take L.low.length) (L.a.take L.low.length) (hl.trans hr.symm)
  have cb := copyRegister_counts none (L.a.take L.low.length) (L.z.take L.low.length) (hr.trans hl.symm)
  have hs : toffoliCount (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length))=n ∧
      measurementCount (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length))=0 := by
    simp [swapRegisters,ca.1,ca.2,cb.1,cb.2,hl]
  have hSigned := skywalkSignedModAdd_counts g L n p hw hn
  have hu := modUnary_counts L.unary n p (L.unary_widths n hw) hn
  have hFlip : toffoliCount [.X g]=0 ∧ measurementCount [.X g]=0 := ⟨rfl,rfl⟩
  simp only [skywalkFieldCell,skywalkFieldUncell,skywalkSignedAdd,toffoliCount_append,measurementCount_append,
    hSigned.1,hSigned.2,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2,hs.1,hs.2,hFlip.1,hFlip.2]
  omega

set_option maxHeartbeats 2000000 in
/-- Full reference-cell support, with no scratch allocation beyond the supplied layout. -/
theorem skywalkField_wires_subset (g swap : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (skywalkFieldCell g swap L p) ⊆ (g::swap::L.wires).toFinset ∧
    wires (skywalkFieldUncell g swap L p) ⊆ (g::swap::L.wires).toFinset := by
  let own := (g::swap::L.wires).toFinset
  have hs : (L.z.take L.low.length).length=(L.a.take L.low.length).length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hswap : wires (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length)) ⊆ own := by
    intro q hq
    have hq' := swapRegisters_wires swap (L.z.take L.low.length) (L.a.take L.low.length) hs hq
    have hz : q∈L.z.take L.low.length → q∈L.z := List.mem_of_mem_take
    have ha : q∈L.a.take L.low.length → q∈L.a := List.mem_of_mem_take
    simp only [own,List.mem_toFinset,List.mem_cons,List.mem_append,ModInPlaceLayout.wires] at hq' ⊢
    tauto
  have hUnary := modUnary_wires L.unary n p (L.unary_widths n hw) hn
  have hHalf : wires (halfInPlace L.unary p) ⊆ own := by
    rw [hUnary.2]
    intro q hq
    simp only [own,List.mem_toFinset,List.mem_cons,List.mem_append,
      ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.unary,
      ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hDouble : wires (dblInPlace L.unary p) ⊆ own := by
    rw [hUnary.1]
    intro q hq
    simp only [own,List.mem_toFinset,List.mem_cons,List.mem_append,
      ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.unary,
      ModUnaryLayout.z,ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hFlip : wires [.X g] ⊆ own := by simp [own,wires,Instr.wires]
  have hSigned : wires (skywalkSignedAdd g L p) ⊆ own := by
    intro q hq
    have hh := skywalkSignedModAdd_wires_subset g L n p hw hn hq
    simp only [own,List.mem_toFinset,List.mem_cons,List.mem_append,
      ModInPlaceLayout.wires,ModInPlaceLayout.work] at hh ⊢
    tauto
  simp only [skywalkFieldCell,skywalkFieldUncell,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hSigned,hHalf⟩,hswap⟩,⟨⟨⟨⟨hswap,hDouble⟩,hFlip⟩,hSigned⟩,hFlip⟩⟩

private theorem skywalk_frame_of_spec (active swap g : Wire) (L : ModInPlaceLayout)
    (C S G : Bool) (X Y A B : Nat) (circuit : Program)
    (hspec : Triple (ReplayValues active swap g L C S G X Y) circuit
      (ReplayValues active swap g L C S G A B))
    (hsupport : wires circuit ⊆ (g::swap::L.wires).toFinset)
    (st : State) (m : List Bool) (h : ReplayValues active swap g L C S G X Y st.basis)
    (q : Wire) (hqz : q∉L.z) (hqa : q∉L.a) : (run circuit m st).basis q=st.basis q := by
  obtain ⟨_,hv⟩ := hspec st m h
  by_cases hg : q=g
  · subst q; exact hv.2.2.1.trans h.2.2.1.symm
  by_cases hs : q=swap
  · subst q; exact hv.2.1.trans h.2.1.symm
  by_cases hk : q∈L.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.2.2.2.trans h.2.2.2.2.2.symm) q hk
  apply run_preserves_outside
  intro hq
  have hh := hsupport hq
  simp [ModInPlaceLayout.wires,hg,hs,hk,hqz,hqa] at hh

/-- Every wire outside the two payload registers is restored, including unused work tails. -/
theorem skywalkField_frame (active swap g : Wire) (L : ModInPlaceLayout)
    (n p X Y : Nat) (C S G : Bool) (hw : L.Widths n)
    (hnd : (active::swap::g::L.wires).Nodup) (hp : p%2=1) (hpn : p<2^n)
    (hX : X<p) (hY : Y<p) (st : State) (m : List Bool)
    (h : ReplayValues active swap g L C S G X Y st.basis) (q : Wire)
    (hz : q∉L.z) (ha : q∉L.a) :
    (run (skywalkFieldCell g swap L p) m st).basis q=st.basis q ∧
    (run (skywalkFieldUncell g swap L p) m st).basis q=st.basis q := by
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  have hs := skywalkField_wires_subset g swap L n p hw hn
  exact ⟨skywalk_frame_of_spec active swap g L C S G X Y _ _ _
    (skywalkFieldCell_spec active swap g L n p X Y C S G hw hnd hp hpn hX hY)
    hs.1 st m h q hz ha,
    skywalk_frame_of_spec active swap g L C S G X Y _ _ _
    (skywalkFieldUncell_spec active swap g L n p X Y C S G hw hnd hp hpn hX hY)
    hs.2 st m h q hz ha⟩

private theorem skywalk_cast_halfMod (X : Nat) : (halveMod p X : Fp)=(X : Fp)/2 := by
  have h := halve_mod_correct p X (by decide : p%2=1)
  have ht : (2 : Fp)≠0 := by decide
  apply (eq_div_iff ht).mpr
  simpa [mul_comm] using h

private theorem skywalk_cast_signed (G : Bool) (X Y : Nat) (hY : Y<p) :
    (skywalkSignedNat p G X Y : Fp)=(X : Fp)+(if G then (Y : Fp) else -(Y : Fp)) := by
  cases G
  · rw [skywalkSignedNat,if_neg Bool.false_ne_true,ZMod.natCast_mod,
      Nat.cast_sub (by omega : Y≤X+p),Nat.cast_add]
    simp [sub_eq_add_neg]
  · simp [skywalkSignedNat,Nat.cast_add]

/-- Canonical natural gate outputs agree exactly with the field-level butterfly. -/
theorem skywalkFieldNat_field (G S : Bool) (X Y : Nat) (hY : Y<p) :
    (((skywalkFieldNat p G S X Y).1 : Fp),((skywalkFieldNat p G S X Y).2 : Fp))=
      skywalkPayloadCell G S ((X : Fp),(Y : Fp)) := by
  cases S <;> simp [skywalkFieldNat,skywalkPayloadCell,skywalk_cast_halfMod,skywalk_cast_signed G X Y hY]
theorem skywalkFieldUnnat_field (G S : Bool) (X Y : Nat) (hX : X<p) (hY : Y<p) :
    (((skywalkFieldUnnat p G S X Y).1 : Fp),((skywalkFieldUnnat p G S X Y).2 : Fp))=
      skywalkPayloadUncell G S ((X : Fp),(Y : Fp)) := by
  cases S
  · have hh := skywalk_cast_signed (!G) ((2*X)%p) Y hY
    cases G <;> apply Prod.ext
    all_goals first | rfl | simpa [skywalkFieldUnnat,skywalkPayloadUncell,Nat.cast_mul] using hh
  · have hh := skywalk_cast_signed (!G) ((2*Y)%p) X hX
    cases G <;> apply Prod.ext
    all_goals first | rfl | simpa [skywalkFieldUnnat,skywalkPayloadUncell,Nat.cast_mul] using hh

/-- The exact gate stream implements the Fp cell on arbitrary canonical Fp inputs.
The extra active wire is a preserved frame witness and never appears in the gate stream. -/
theorem skywalkFieldCell_correct_fp (active swap g : Wire) (L : ModInPlaceLayout)
    (X Y : Fp) (C S G : Bool) (hw : L.Widths 256)
    (hnd : (active::swap::g::L.wires).Nodup) (st : State) (m : List Bool)
    (h : ReplayValues active swap g L C S G X.val Y.val st.basis) :
    (run (skywalkFieldCell g swap L p) m st).phase=st.phase ∧
    (((regValue L.z (run (skywalkFieldCell g swap L p) m st).basis : Nat) : Fp),
      ((regValue L.a (run (skywalkFieldCell g swap L p) m st).basis : Nat) : Fp))=
      skywalkPayloadCell G S (X,Y) ∧
    regValue L.work (run (skywalkFieldCell g swap L p) m st).basis=0 ∧
    (∀ q,q∉L.z → q∉L.a → (run (skywalkFieldCell g swap L p) m st).basis q=st.basis q) := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  have hX : X.val<p := ZMod.val_lt X
  have hY : Y.val<p := ZMod.val_lt Y
  have hp : p%2=1 := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  obtain ⟨hf,hv⟩ := skywalkFieldCell_spec active swap g L 256 p X.val Y.val C S G hw hnd hp hpn hX hY st m h
  refine ⟨hf,?_,hv.2.2.2.2.2,?_⟩
  · rw [hv.2.2.2.1,hv.2.2.2.2.1,skywalkFieldNat_field G S X.val Y.val hY,
      ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  · intro q hz ha
    exact (skywalkField_frame active swap g L 256 p X.val Y.val C S G hw hnd hp hpn hX hY st m h q hz ha).1

/-- The separately specified inverse gate stream implements the Fp inverse on all inputs. -/
theorem skywalkFieldUncell_correct_fp (active swap g : Wire) (L : ModInPlaceLayout)
    (X Y : Fp) (C S G : Bool) (hw : L.Widths 256)
    (hnd : (active::swap::g::L.wires).Nodup) (st : State) (m : List Bool)
    (h : ReplayValues active swap g L C S G X.val Y.val st.basis) :
    (run (skywalkFieldUncell g swap L p) m st).phase=st.phase ∧
    (((regValue L.z (run (skywalkFieldUncell g swap L p) m st).basis : Nat) : Fp),
      ((regValue L.a (run (skywalkFieldUncell g swap L p) m st).basis : Nat) : Fp))=
      skywalkPayloadUncell G S (X,Y) ∧
    regValue L.work (run (skywalkFieldUncell g swap L p) m st).basis=0 ∧
    (∀ q,q∉L.z → q∉L.a → (run (skywalkFieldUncell g swap L p) m st).basis q=st.basis q) := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  have hX : X.val<p := ZMod.val_lt X
  have hY : Y.val<p := ZMod.val_lt Y
  have hp : p%2=1 := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  obtain ⟨hf,hv⟩ := skywalkFieldUncell_spec active swap g L 256 p X.val Y.val C S G hw hnd hp hpn hX hY st m h
  refine ⟨hf,?_,hv.2.2.2.2.2,?_⟩
  · rw [hv.2.2.2.1,hv.2.2.2.2.1,skywalkFieldUnnat_field G S X.val Y.val hX hY,
      ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  · intro q hz ha
    exact (skywalkField_frame active swap g L 256 p X.val Y.val C S G hw hnd hp hpn hX hY st m h q hz ha).2


end ECDSAAdd.Arithmetic
