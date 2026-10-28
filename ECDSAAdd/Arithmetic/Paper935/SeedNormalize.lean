import ECDSAAdd.Arithmetic.Paper935.ScalingSeed
import ECDSAAdd.Arithmetic.Divsteps.SignedEndpoint
import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- Complementing a signed word gives -v-1, including the most negative word. -/
theorem signedDecode_complement (w v : Nat) (hw : 0<w) (hv : v<2^w) :
    signedDecode w (2^w-1-v) = -signedDecode w v-1 := by
  have hp : 2^w=2*2^(w-1) := by
    calc
      2^w = 2^((w-1)+1) := by congr 1; omega
      _ = 2*2^(w-1) := by rw [pow_succ]; omega
  unfold signedDecode
  split_ifs <;> omega

/-- Temporarily complement the signed source, reduce it canonically, add the
missing one, and restore the source. This uses the existing wide unary layout;
it is a reference normalization circuit, not a 935-wire placement. -/
def seedNormalize (q : Wire) (row : WindowRow) (U : ModUnaryLayout) (p : Nat) : Program :=
  signComplement q row.wires ++ endpointSigned U p row.payload row.sign ++
    endpointConstant q U p 1 ++ signComplement q row.wires

theorem seedNormalize_run (q : Wire) (row : WindowRow) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hu : U.wires.Nodup) (hr : row.wires.Nodup)
    (hq : q∉row.wires) (hqu : q∉U.wires) (sep : List.Disjoint row.wires U.wires)
    (hp : 1<p) (hpn : p<2^n) (s : State) (m : List Bool)
    (hz : regValue U.z s.basis=0) (clean : regValue U.work s.basis=0) :
    let out := run (seedNormalize q row U p) m s
    out.phase=s.phase ∧
    regValue U.z out.basis=(if s.basis q then -(row.value s.basis : ZMod p)
      else (row.value s.basis : ZMod p)).val ∧
    regValue U.work out.basis=0 ∧ ∀ w, w∉U.z → out.basis w=s.basis w := by
  let a := run (signComplement q row.wires) m s
  let b := run (endpointSigned U p row.payload row.sign) m a
  let tape := m.drop (measurementCount (endpointSigned U p row.payload row.sign))
  let c := run (endpointConstant q U p 1) tape b
  let d := run (signComplement q row.wires)
    (tape.drop (measurementCount (endpointConstant q U p 1))) c
  have ha := signComplement_correct q row.wires hr hq s m
  have away (w : Wire) (h : w∈U.wires) : w∉row.wires :=
    fun bad => List.disjoint_left.mp sep bad h
  have zmem (w : Wire) (h : w∈U.z) : w∈U.wires := List.mem_append_left _ h
  have wmem (w : Wire) (h : w∈U.work) : w∈U.wires := List.mem_append_right _ h
  have az : regValue U.z a.basis=0 :=
    (regValue_congr _ _ _ (fun w h => ha.2.1 w (away w (zmem w h)))).trans hz
  have aw : regValue U.work a.basis=0 :=
    (regValue_congr _ _ _ (fun w h => ha.2.1 w (away w (wmem w h)))).trans clean
  have hb := endpointSigned_run U n p row.payload row.sign hw hu sep (by omega) hpn a m az aw
  have qz : q∉U.z := fun h => hqu (zmem q h)
  have cq : c.basis q=s.basis q := by
    exact ((endpointConstant_run q U n p 1 (regValue U.z b.basis) hw
      (List.nodup_cons.mpr ⟨hqu,hu⟩) (by omega) hpn hp hb.2.1 b tape rfl hb.2.2.2.1).2.2.2 q qz).trans
      ((hb.2.2.2.2 q qz).trans (ha.2.1 q hq))
  have hc := endpointConstant_run q U n p 1 (regValue U.z b.basis) hw
    (List.nodup_cons.mpr ⟨hqu,hu⟩) (by omega) hpn hp hb.2.1 b tape rfl hb.2.2.2.1
  have hd := signComplement_correct q row.wires hr hq c
    (tape.drop (measurementCount (endpointConstant q U p 1)))
  have rz (w : Wire) (h : w∈row.wires) : w∉U.z :=
    fun bad => List.disjoint_left.mp sep h (zmem w bad)
  have cr : regValue row.wires c.basis=regValue row.wires a.basis :=
    regValue_congr _ _ _ (fun w h => (hc.2.2.2 w (rz w h)).trans (hb.2.2.2.2 w (rz w h)))
  have dr : regValue row.wires d.basis=regValue row.wires s.basis := by
    rw [hd.2.2,cq,cr,ha.2.2]
    have bound := regValue_lt row.wires s.basis
    cases s.basis q <;> simp only [Bool.false_eq_true,if_false,if_true]
    omega
  have frame (w : Wire) (h : w∉U.z) : d.basis w=s.basis w := by
    by_cases r : w∈row.wires
    · exact (regValue_eq_iff _ _ _).mp dr w r
    · exact (hd.2.1 w r).trans ((hc.2.2.2 w h).trans ((hb.2.2.2.2 w h).trans (ha.2.1 w r)))
  have value : regValue U.z d.basis=(if s.basis q then -(row.value s.basis : ZMod p)
      else (row.value s.basis : ZMod p)).val := by
    letI : NeZero p := ⟨by omega⟩
    have dz : regValue U.z d.basis=regValue U.z c.basis :=
      regValue_congr _ _ _ (fun w h => hd.2.1 w (away w (zmem w h)))
    have bq : b.basis q=s.basis q := (hb.2.2.2.2 q qz).trans (ha.2.1 q hq)
    have ar : row.value a.basis=if s.basis q then -row.value s.basis-1 else row.value s.basis := by
      unfold WindowRow.value signedRegValue
      rw [ha.2.2]
      cases s.basis q <;> simp only [Bool.false_eq_true,if_false,if_true]
      exact signedDecode_complement _ _ (by simp [WindowRow.wires]) (regValue_lt _ _)
    have eq : (regValue U.z c.basis : ZMod p)=
        if s.basis q then -(row.value s.basis : ZMod p) else (row.value s.basis : ZMod p) := by
      rw [hc.2.1,ZMod.natCast_mod,Nat.cast_add,hb.2.2.1,bq]
      change (row.value a.basis : ZMod p)+_=_
      rw [ar]
      cases s.basis q <;> simp
    rw [dz]
    have cb : regValue U.z c.basis<p := by rw [hc.2.1]; exact Nat.mod_lt _ (by omega)
    simpa only [ZMod.val_natCast_of_lt cb] using congrArg ZMod.val eq
  have dw : regValue U.work d.basis=0 := by
    rw [←clean]
    apply regValue_congr
    intro w h
    exact frame w (fun hz => List.disjoint_left.mp (List.nodup_append'.mp hu).2.2 hz h)
  have runEq : run (seedNormalize q row U p) m s=d := by
    rw [seedNormalize,run_append,run_take,run_append,run_take,run_append,run_take]
    simp only [measurementCount_append,(signComplement_counts q row.wires).2,
      Nat.zero_add,List.drop_zero]
    dsimp [d,c,tape,b,a]
    rw [List.drop_drop]
  rw [runEq]
  exact ⟨hd.1.trans (hc.1.trans (hb.1.trans ha.1)),value,dw,frame⟩

/-- The endpoint f=±1 sign is read from its actual signed row, not supplied as
an unrelated Boolean witness. -/
theorem seedNormalize_bank (bank : WindowBank) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hu : U.wires.Nodup) (hr : bank.fv.wires.Nodup)
    (hq : bank.f.sign∉bank.fv.wires) (hqu : bank.f.sign∉U.wires)
    (sep : List.Disjoint bank.fv.wires U.wires) (hp : 1<p) (hpn : p<2^n)
    (s : State) (m : List Bool) (unit : (bank.f.value s.basis).natAbs=1)
    (hz : regValue U.z s.basis=0) (clean : regValue U.work s.basis=0) :
    let out := run (seedNormalize bank.f.sign bank.fv U p) m s
    out.phase=s.phase ∧ regValue U.z out.basis=endpointSeedRead p bank s.basis ∧
    regValue U.work out.basis=0 ∧ ∀ w, w∉U.z → out.basis w=s.basis w := by
  have h := seedNormalize_run bank.f.sign bank.fv U n p hw hu hr hq hqu sep hp hpn s m hz clean
  refine ⟨h.1,h.2.1.trans ?_,h.2.2⟩
  have sg := signedRegValue_neg_iff bank.f.payload bank.f.sign s.basis
  change bank.f.value s.basis<0 ↔ s.basis bank.f.sign=true at sg
  have fv : bank.f.value s.basis=1 ∨ bank.f.value s.basis= -1 := by omega
  unfold endpointSeedRead
  rcases fv with pos|neg
  · have bit : s.basis bank.f.sign=false := by
      cases hb : s.basis bank.f.sign
      · rfl
      · have := sg.mpr hb; omega
    simp [bit,pos]
  · have bit := sg.mp (show bank.f.value s.basis<0 by omega)
    simp [bit,neg]

/-- The reference layout alone needs 1029 distinct lines at field width 256,
before any source rows. It cannot certify the compact 935-line implementation. -/
theorem seedNormalize_layout_size (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n) :
    U.wires.length=4*n+5 := by
  simp [ModUnaryLayout.wires,ModUnaryLayout.z,ModUnaryLayout.work,ModUnaryLayout.core,
    ModAddCoreLayout.work,hw.low,hw.constant,hw.carry,hw.mask]
  omega

theorem seedNormalize_counts (q : Wire) (row : WindowRow) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (seedNormalize q row U p)=(row.payload.length+2)*(4*n-1) ∧
    measurementCount (seedNormalize q row U p)=(row.payload.length+2)*(4*n-1) := by
  have a := endpointSigned_counts U n p row.payload row.sign hw hn
  have b := endpointConstant_counts q U n p 1 hw hn
  simp only [seedNormalize,toffoliCount_append,measurementCount_append,
    (signComplement_counts q row.wires).1,(signComplement_counts q row.wires).2,
    a.1,a.2,b.1,b.2,Nat.zero_add,Nat.add_zero]
  constructor <;> nlinarith [a.1,a.2]

/-- Normalize the actual seeded-walk output into U.z. Auxiliary readiness is
required at that actual state; it is not inferred from unrelated clean inputs. -/
theorem seededAuthorWalk_normalize {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (hp1 : 1<p) (x : X)
    (odd : (p : Int)%2=1) (coprime : Int.gcd p (input x)=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m tape : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x)
    (U : ModUnaryLayout) (hw : U.Widths 256) (hu : U.wires.Nodup)
    (hr : (walkExitBank walkSeedBank slots).fv.wires.Nodup)
    (hq : (walkExitBank walkSeedBank slots).f.sign∉(walkExitBank walkSeedBank slots).fv.wires)
    (hqu : (walkExitBank walkSeedBank slots).f.sign∉U.wires)
    (sep : List.Disjoint (walkExitBank walkSeedBank slots).fv.wires U.wires)
    (hz : regValue U.z (runWithTape (seededAuthorWalkProgram p slots) m ordinal s).basis=0)
    (clean : regValue U.work (runWithTape (seededAuthorWalkProgram p slots) m ordinal s).basis=0) :
    let before := runWithTape (seededAuthorWalkProgram p slots) m ordinal s
    let bank := walkExitBank walkSeedBank slots
    let out := run (seedNormalize bank.f.sign bank.fv U p) tape before
    out.phase=before.phase ∧ regValue U.z out.basis=scaledInverseSeed p (input x) ∧
    regValue U.work out.basis=0 ∧ ∀ w, w∉U.z → out.basis w=before.basis w := by
  have endpoint := seededAuthorWalk_scaled_inverse input p hp x odd coprime good slots compiled
    s m ordinal ready encoding
  have norm := seedNormalize_bank (walkExitBank walkSeedBank slots) U 256 p hw hu hr hq hqu sep hp1 hp
    (runWithTape (seededAuthorWalkProgram p slots) m ordinal s) tape endpoint.2.2.1 hz clean
  have read := seededAuthorWalk_seed_read input p hp x odd good slots compiled s m ordinal ready encoding
  exact ⟨norm.1,norm.2.1.trans read,norm.2.2⟩

/-- A canonical field result in the widened accumulator is also the value of
its n low bits; the extra high wire is zero for the next stage. -/
theorem seedNormalize_low_word (U : ModUnaryLayout) (n v : Nat) (hw : U.Widths n)
    (s : BasisState) (hv : v<2^n) (hz : regValue U.z s=v) :
    s U.high=false ∧ regValue U.low s=v := by
  have h := regValue_highBit U.low U.high s
  have bit : s U.high=false := by
    cases he : s U.high with
    | false => rfl
    | true =>
      have bound := h.mp he
      change 2^U.low.length≤regValue U.z s at bound
      rw [hw.low,hz] at bound
      omega
  refine ⟨bit,?_⟩
  simpa [ModUnaryLayout.z,regValue_append,regValue,bit] using hz

end ECDSAAdd.Arithmetic.Paper935
