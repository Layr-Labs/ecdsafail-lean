import ECDSAAdd.Submission.Entrant.JointInverse1588
set_option Elab.async false

/-! Forward joint entry of the S1 (divide) first packet, placed in the 1,588-qubit Rolling layout.

The divide stage's first packet starts on the pair `(Z, 0)`.  Its first measured selector swap
(`FrontierSW1591.firstSwapS`, controlled by `S0`) and its trit-1 half window (controlled by `G1`)
together compute `((±Z)/2, S0 ? Z : 0)`.  The joint entry `EntryRetained5.program` (spariev,
submission 74fe2201, already in the record) computes the same pair directly; the measured joint
inverse of the multiplication stage (`JointInverse1588`) is its mirror image.

As there, the record's layout has no sites for the virtual carries `516` and `1541`, so the
forward program hosts them inside the kernel:
* during the inner adder (source bits 4..255) of the forward addition on `lowY` (u = J∧B) and
  `sign` (e = lower∧u), which are measured away before and recomputed after (+2 Toffolis), with
  `JointInverse1588.loanW`;
* during the final `clearParity` on the scalars `one` and `sign`, which `eraseScalars` has
  just cleared (`JointInverse1588.clearH`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

/-- The forward addition with carry #4 on `lowY` and carry #254 on `sign` inside source bits 4..255. -/
def arithH (L : Layout) (J B : Wire) : Program :=
  pre4 L++loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)++post4 L

/-- `EntryRetained5.program` with the two hosted carries. -/
def programF (L : Layout) (J B : Wire) : Program :=
  prepare L J B++arithH L J B++eraseScalarsAt L J B++clearH L J

theorem pre4_keep (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (b : State) (q : Wire)
    (hc : ∀i,i<4 → q≠cAt L i) :
    (run (pre4 L) [] b).basis q=b.basis q ∧ (run (pre4 L) [] b).phase=b.phase := by
  have p := pre4_run L hw hn b []
  exact ⟨p.2 q (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide)),p.1⟩

/-- On a state where `sign = lower∧lowY`, `lowY = J∧B` and every carry is clean, the measured loan
around the inner adder runs as the inner adder (it only reads two extra records). -/
theorem loan_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (r : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    run (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)) r (run (pre4 L) [] b)=
      run (inner L) (r.drop 2) (run (pre4 L) [] b) := by
  let x := run (pre4 L) [] b
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have nd7 := dist.1
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have lowCarry (i : Nat) (hi : i<4) : cAt L i∈L.carry := carry_mem L hw i (by omega)
  have offData (q : Wire) (hq : q∉L.r++L.y++L.carry) : q∉L.r ∧ ∀i,i<4 → q≠cAt L i :=
    ⟨fun h => hq (by simp [h]),fun i hi e => hq (by rw [e];simp [lowCarry i hi])⟩
  have keepS := pre4_keep L hw hn b L.sign (offData _ (flags _ (by simp))).2
  have keepA := pre4_keep L hw hn b L.lower (offData _ (flags _ (by simp))).2
  have keepU := pre4_keep L hw hn b (lowY L)
    (fun i hi e => y_not_carry L hn _ y0 (by rw [e];exact lowCarry i hi))
  have keepJ := pre4_keep L hw hn b J (offData _ (notData _ hJ)).2
  have keepB := pre4_keep L hw hn b B (offData _ (notData _ hB)).2
  have hiIdx (k : Nat) (hk : k=4 ∨ k=254) (i : Nat) (hi : i<4) : L.carry.getD k 0≠cAt L i :=
    carry_index_ne L hw hn k i (by omega) (by omega) (by omega)
  have keepLo := pre4_keep L hw hn b (cLo L) (hiIdx 4 (Or.inl rfl))
  have keepHi := pre4_keep L hw hn b (cHi L) (hiIdx 254 (Or.inr rfl))
  have cleanX : ∀q∈(L.carry.take 255).drop 4,x.basis q=false := by
    intro q hq
    obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
    have qc : q∈L.carry := List.mem_of_mem_take (List.mem_of_mem_drop hq)
    have ndc : (L.carry.take 255).Nodup := (carry_nodup L hn).sublist (List.take_sublist _ _)
    rw [hct] at ndc hq
    simp only [List.drop_succ_cons,List.drop_zero] at hq
    simp only [List.nodup_cons,List.mem_cons,not_or] at ndc
    have ne (i : Nat) (hi : i<4) : q≠cAt L i := by
      intro e
      interval_cases i
      · rw [f0] at e;exact ndc.1.2.2.2 (e ▸ hq)
      · rw [f1] at e;exact ndc.2.1.2.2 (e ▸ hq)
      · rw [f2] at e;exact ndc.2.2.1.2 (e ▸ hq)
      · rw [f3] at e;exact ndc.2.2.2.1 (e ▸ hq)
    exact ((pre4_keep L hw hn b q ne).1).trans (hc q qc)
  have inn (t : List Bool) := inner_correct L hw hn x t cleanX
  apply loanW_run L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L) x r nd7
  · rw [keepS.1,keepA.1,keepU.1];exact he
  · rw [keepU.1,keepJ.1,keepB.1];exact hu
  · exact inner_free L hw hn _ (fun h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e
      · exact flags L.parity (by simp) (by rw [←e];simp [y0])
      · exact flags L.lower (by simp) (by rw [←e];simp [y0])
      · exact flags L.one (by simp) (by rw [←e];simp [y0]))
      (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  · exact inner_free L hw hn _ (fun h => by
      have sc := scalarND L hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e <;>
        (have c := List.nodup_iff_count.mp sc L.sign
         rw [e] at c;simp [List.count_cons] at c;omega))
      (offData _ (flags _ (by simp))).1 (fun h => flags L.sign (by simp) (by simp [h]))
  · intro t
    have i := (inn t).2
    exact ⟨i _ (offData _ (flags _ (by simp))).1,i _ (offData _ (notData _ hJ)).1,
      i _ (offData _ (notData _ hB)).1⟩
  · exact keepLo.1.trans (hc _ (carry_mem L hw 4 (by decide)))
  · exact keepHi.1.trans (hc _ (carry_mem L hw 254 (by decide)))
  · intro t
    exact ((inn t).2 _ (carry_not_r L hn _ (carry_mem L hw 4 (by decide)))).trans
      (keepLo.1.trans (hc _ (carry_mem L hw 4 (by decide))))
  · intro t
    exact ((inn t).2 _ (carry_not_r L hn _ (carry_mem L hw 254 (by decide)))).trans
      (keepHi.1.trans (hc _ (carry_mem L hw 254 (by decide))))

/-- The final parity clear with carries #4 and #254 on the cleared `one` and `sign` runs as the
record's `clearParity` on every state reached by the forward prefix and the scalar erasure. -/
theorem tail_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (t1 t2 n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (clearH L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s))=
      run (clearParity L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s)) := by
  have pref := prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s t1 hR hY hc hz hj hb
  generalize hbdef : run (prefixProgram L J B) t1 s=b at pref ⊢
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  generalize hcdef : run (eraseScalarsAt L J B) t2 b=c
  have erased : c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ := by
    rw [←hcdef]
    exact eraseScalarsAt_run L hw hn J B hJ hB hJB b t2 ee aa dd uu
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  exact clearH_eq L hw hn J hJ _ rc c n cR ca cCarry cOne cSign

/-- The hosted forward program runs as `EntryRetained5.program` on the entry frame, for a
re-aligned record list. -/
theorem programF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    ∃m',run (programF L J B) m s=run (EntryRetained5.program L J B) m' s := by
  let Pre := prepare L J B++pre4 L
  let Q := loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)
  let Post := post4 L++eraseScalarsAt L J B++clearH L J
  have shapeF : programF L J B=Pre++Q++Post := by
    simp only [programF,arithH,Pre,Q,Post,List.append_assoc]
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have pc := prepare_counts L hw J B
  have preRun : run Pre [] s=run (pre4 L) [] (run (prepare L J B) [] s) := by
    simp only [Pre,run_append,List.take_nil,List.drop_nil]
  have hpre : measurementCount Pre=0 := by
    simp only [Pre,measurementCount_append,pc.2,(pre4_counts L).2]
  have stepA := context_eq Pre (inner L) Q Post 2 s m hpre (loanW_counts _ _ _ _ _ _ _ _).2 (by
    intro r
    rw [preRun]
    exact loan_run L hw hn J B hJ hB hJB _ r
      (by rw [prep.a,prep.u];exact prep.e)
      (by rw [prep.u,prep.j,prep.b])
      prep.carry)
  refine ⟨(m.drop 2).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeF,stepA]
  generalize (m.drop 2).take (measurementCount (inner L))++m.drop (measurementCount Q)=n
  have shape1 : Pre++inner L++Post=(prefixProgram L J B++eraseScalarsAt L J B)++clearH L J := by
    simp only [Pre,Post,prefixProgram,arithmetic,add_split L hw,List.append_assoc]
  have shape2 : EntryRetained5.program L J B=
      (prefixProgram L J B++eraseScalarsAt L J B)++clearParity L J := rfl
  rw [shape1,shape2,run_append,run_append (prefixProgram L J B++eraseScalarsAt L J B),
    run_append (prefixProgram L J B)]
  exact tail_eq L hw hn J B hJ hB hJB Jv Bv Y hy s _ _ _ hR hY hc hz hj hb

end ECDSAAdd.Entrant.JointForward1588


/-! ### The hosted forward joint entry -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Secp256k1

def jointF (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G]++programF L J G++[.X G]

theorem xwrap_run (G : Wire) (P : Program) (m : List Bool) (s : State) :
    run ([.X G]++P++[.X G]) m s=run [.X G] [] (run P m (run [.X G] [] s)) := by
  have xm : measurementCount [Instr.X G]=0 := rfl
  have any (r : List Bool) (t : State) : run [Instr.X G] r t=run [Instr.X G] [] t := by
    have h := run_take [Instr.X G] r t
    rw [xm,List.take_zero] at h
    exact h.symm
  rw [run_append ([Instr.X G]++P) [Instr.X G],any,run_append [Instr.X G] P,xm,List.take_zero,
    List.drop_zero,measurementCount_append,xm,Nat.zero_add,run_take]

private theorem outside_layoutF (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- The hosted forward joint runs as `FrontierEntry.joint` on the entry frame. -/
theorem jointF_eq (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    ∃m',run (jointF L J G) m s=run (FrontierEntry.joint L J G) m' s := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutF L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  obtain ⟨m',h⟩ := programF_eq L hw hn J G hJ hG hJG Jv (!Gv) Y hy a m aR aY ac
    ((keep _ sg).trans sign) aj ag
  refine ⟨m',?_⟩
  rw [jointF,xwrap_run,FrontierEntry.joint,xwrap_run,head,h]

/-- `(Z, 0) ↦ ((±Z)/2, J ? Z : 0)`: the first selector swap and the G1 half of the divide replay. -/
theorem jointF_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin (centerWord Z) 0) (jointF L J G)
      (PairFrame L.r L.y origin
        (centerWord ((if origin J && !origin G then -Z else Z)/2))
        (centerWord (if origin J then Z else 0))) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have ss : s.basis L.sign=false := (h.2.2 _ sa.1 sa.2).trans sign
  have sj : s.basis J=origin J := h.2.2 _ (outside J hJ).1 (outside J hJ).2
  have sg : s.basis G=origin G := h.2.2 _ (outside G hG).1 (outside G hG).2
  obtain ⟨m',eq⟩ := jointF_eq L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m h.1 h.2.1 hc ss sj sg
  have out := FrontierEntry.joint_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m' h.1 h.2.1 hc ss sj sg
  dsimp only at out
  rw [unary_half,source_word] at out
  rw [eq]
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

end ECDSAAdd.Entrant.JointForward1588


/-! ### Resources, support and physicality of the hosted forward joint -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
  Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programF_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (programF L J B)=773 ∧ measurementCount (programF L J B)=516 := by
  have p:=prepare_counts L hw J B
  have i:=inner_counts L hw
  have w:=loanW_counts L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)
  have e:=eraseScalars_counts L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb
  have c:=clearParity_counts L hw J
  have c1:=renameProgram_counts (Equiv.swap (cLo L) L.one) (clearParity L J)
  have c2:=renameProgram_counts (Equiv.swap (cHi L) L.sign)
    (renameProgram (Equiv.swap (cLo L) L.one) (clearParity L J))
  simp only [programF,arithH,clearH,eraseScalarsAt,toffoliCount_append,measurementCount_append,
    p.1,p.2,w.1,w.2,i.1,i.2,e.1,e.2,c.1,c.2,c1.1,c1.2,c2.1,c2.2,(pre4_counts L).1,(pre4_counts L).2,
    (post4_counts L).1,(post4_counts L).2]
  all_goals simp

theorem jointF_counts (L : Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (jointF L J G)=773 ∧ measurementCount (jointF L J G)=516 := by
  have h:=programF_counts L hw J G
  simpa only [jointF,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

theorem programF_slots (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (programF L J B)≤7975 := by
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParity_slots_le L hw J
  have er : gateSlots (eraseScalarsAt L J B)=11 := rfl
  have split : gateSlots (pre4 L)+gateSlots (inner L)+gateSlots (post4 L)=4369 := by
    rw [←arith,show arithmetic L=pre4 L++inner L++post4 L from add_split L hw]
    simp only [gateSlots_append]
  have loanS : gateSlots (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L))=
      gateSlots (inner L)+6 := by
    have a : gateSlots ([Instr.measureX L.sign [] [Correction.CZ L.lower (lowY L)],
        Instr.measureX (lowY L) [] [Correction.CZ J B]] : Program)=4 := rfl
    have b : gateSlots ([Instr.CCX J B (lowY L),Instr.CCX L.lower (lowY L) L.sign] : Program)=2 := rfl
    simp only [loanW,gateSlots_append,rename_gateSlots,a,b]
    omega
  simp only [programF,arithH,clearH,gateSlots_append,rename_gateSlots,er,loanS]
  omega

theorem jointF_slots (L : Layout) (hw : L.Widths) (J G : Wire) : gateSlots (jointF L J G)≤7977 := by
  have h := programF_slots L hw J G
  have x : gateSlots [Instr.X G]=1 := rfl
  simp only [jointF,gateSlots_append,x]
  omega

theorem programF_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J B : Wire) :
    wires (programF L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have ha : L.lower∈retSites L J B := by simp [retSites]
  have hd : L.one∈retSites L J B := by simp [retSites]
  have he : L.sign∈retSites L J B := by simp [retSites]
  have hj : J∈retSites L J B := by simp [retSites]
  have hb : B∈retSites L J B := by simp [retSites]
  have hu := y (lowY L) y0
  have carryIn (i : Nat) (hi : i<255) : L.carry.getD i 0∈retSites L J B := by
    have m := carry_take_mem L hw i hi
    simp only [retSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr m)
  have split := pre4_post4_support L hw
  have clearS : wires (clearH L J)⊆retSites L J B :=
    swap2_support _ _ _ _ _ _ parts.2 (carryIn 4 (by decide)) hd (carryIn 254 (by decide)) he
  have loan : wires (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L))⊆retSites L J B := by
    simp only [loanW,wires_append,Finset.union_subset_iff]
    refine ⟨⟨?_,swap2_support _ _ _ _ _ _ (split.2.1.trans parts.1.1.2) (carryIn 4 (by decide)) hu
      (carryIn 254 (by decide)) he⟩,?_⟩
    · simp [wires,Instr.wires,correctionWires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
  simp only [programF,arithH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨parts.1.1.1,⟨⟨split.1.trans parts.1.1.2,loan⟩,split.2.2.trans parts.1.1.2⟩⟩,parts.1.2⟩,clearS⟩

theorem jointF_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J G : Wire) :
    wires (jointF L J G)⊆retSites L J G := by
  have g : G∈retSites L J G := by simp [retSites]
  have x : wires [Instr.X G]⊆retSites L J G := by
    intro q hq
    have : q=G := by simpa [wires,Instr.wires] using hq
    rw [this];exact g
  simp only [jointF,wires_append,Finset.union_subset_iff]
  exact ⟨⟨x,programF_support L hw hn J G⟩,x⟩

theorem programF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L) : q∉wires (programF L J B) := by
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have hd := hosts_distinct L hw hn
  have nd7 := dist.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd7
  rcases nd7 with ⟨⟨sl,su,sj,sb,slo,shi⟩,⟨⟨lu,lj,lb,llo,lhi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
  have qr : q∉L.r := carry_not_r L hn q qc
  have qy : q∉L.y := fun h => y_not_carry L hn q h qc
  have flagNe (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q≠f := fun e => flagAway L hn f hf (by rw [←e];simp [qc])
  have qJ : q≠J := fun e => hJ (e ▸ data_member L q (by simp [qc]))
  have qB : q≠B := fun e => hB (e ▸ data_member L q (by simp [qc]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have qu : q≠lowY L := fun e => qy (e ▸ y0)
  have qlow (i : Nat) (hi : i<4) : q≠cAt L i := by
    rcases hq with rfl|rfl
    · exact carry_index_ne L hw hn 4 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 254 i (by decide) (by omega) (by omega)
  have qsite (h : q∈Affine.sites (sources L)) : False := by
    have m := sources_sites L q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
  have edge (P : Program) (hP : wires P⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,
      lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset) : q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    have rmem (i : Nat) (hi : i<4) : rAt L i∈L.r := by
      have len := BalancedCleanup.widths L.toLayout hw
      have lt : i<L.r.length := by rw [len.2.1];omega
      simp only [rAt,List.getD_eq_getElem _ _ lt]
      exact List.getElem_mem lt
    rcases m with h|e|e|e|e|e|e|e|e|e
    · exact qsite h
    · exact qr (e ▸ rmem 0 (by decide))
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qr (e ▸ rmem 2 (by decide))
    · exact qr (e ▸ rmem 3 (by decide))
    · exact qu e
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
    · exact qlow 2 (by decide) e
    · exact qlow 3 (by decide) e
  have es := edge_support L
  have clearF : q∉wires (clearH L J) :=
    swap2_free (cLo L) L.one (cHi L) L.sign (clearParity L J)
      (clearParity_scalar_free L hw hn J hJ L.one (Or.inl rfl))
      (clearParity_scalar_free L hw hn J hJ L.sign (Or.inr rfl))
      hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q hq
  have eraseSub : wires (eraseScalarsAt L J B)⊆
      ([L.parity,L.lower,L.one,L.sign,lowY L,J,B,L.rmsb] : List Wire).toFinset := by
    intro x hx
    simp only [eraseScalarsAt,eraseScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    change x=L.parity ∨ x=L.lower ∨ x=L.one ∨ x=L.sign ∨ x=L.ylow.getD 0 0 ∨ x=J ∨ x=B ∨ x=L.rmsb
    tauto
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have eraseF : q∉wires (eraseScalarsAt L J B) := by
    intro used
    have m := List.mem_toFinset.mp (eraseSub used)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e|e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
    · exact qr (e ▸ rh)
  have innerF : q∉wires (renameProgram (Equiv.swap (cHi L) L.sign)
      (renameProgram (Equiv.swap (cLo L) (lowY L)) (inner L))) := by
    have sc := scalarND L hn
    exact swap2_free (cLo L) (lowY L) (cHi L) L.sign (inner L)
      (inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0))
      (inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h])))
      hd.2.2.2.2.2.1 (Ne.symm slo) su q hq
  have edgeSub : wires ([.measureX L.sign [] [.CZ L.lower (lowY L)],.measureX (lowY L) [] [.CZ J B]] : Program)∪
      wires ([.CCX J B (lowY L),.CCX L.lower (lowY L) L.sign] : Program)⊆
      ([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro x hx
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.union_empty] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have edgeF : q∉([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro h
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e
    · exact flagNe L.sign (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
  have loanF : q∉wires (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)) := by
    simp only [loanW,wires_append,Finset.mem_union,not_or]
    refine ⟨⟨fun h => edgeF (edgeSub (Finset.mem_union_left _ h)),innerF⟩,
      fun h => edgeF (edgeSub (Finset.mem_union_right _ h))⟩
  have prepF : q∉wires (prepare L J B) := by
    intro used
    have m := List.mem_toFinset.mp (prepare_support L hw J B used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with (h|h)|e|e|e|e|e|e
    · exact qr h
    · exact qy h
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qJ e
    · exact qB e
  simp only [programF,arithH,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨prepF,⟨⟨edge _ es.1,loanF⟩,edge _ es.2⟩⟩,eraseF⟩,clearF⟩

theorem jointF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L) : q∉wires (jointF L J G) := by
  have core := programF_free L hw hn J G hJ hG hJG q hq
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
  have qG : q≠G := fun e => hG (e ▸ data_member L q (by simp [qc]))
  simp only [jointF,wires_append,Finset.mem_union,not_or]
  refine ⟨⟨?_,core⟩,?_⟩ <;> simp [wires,Instr.wires,qG]

theorem programF_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programF L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨aE,Ne.symm eU,Ne.symm uJ,Ne.symm uB⟩
  have jb : J≠B := by
    intro e
    simp [e] at hJB
  have arith : GatePhysical (pre4 L) ∧ GatePhysical (inner L) ∧ GatePhysical (post4 L) := by
    have h := parts.1.1.2
    rw [show arithmetic L=pre4 L++inner L++post4 L from add_split L hw] at h
    simp only [gatePhysical_append] at h
    exact ⟨h.1.1,h.1.2,h.2⟩
  have clear : GatePhysical (clearH L J) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ parts.2)
  have loan : GatePhysical (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)) := by
    simp only [loanW,gatePhysical_append]
    refine ⟨⟨?_,gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ arith.2.1)⟩,?_⟩
    · simp [GatePhysical,PhysicalInstr]
    · simp [GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,ctr.2.2.1,ctr.2.2.2,jb]
  simp only [programF,arithH,gatePhysical_append]
  exact ⟨⟨⟨parts.1.1.1,⟨⟨arith.1,loan⟩,arith.2.2⟩⟩,parts.1.2⟩,clear⟩

theorem jointF_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup) :
    GatePhysical (jointF L J G) := by
  have core := programF_physical L hw hn J G hJ hG hJG
  have x : GatePhysical [Instr.X G] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [jointF,gatePhysical_append]
  exact ⟨⟨x,core⟩,x⟩

end ECDSAAdd.Entrant.JointForward1588


/-! ## The S1 first-packet kernel in the record's 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines
attribute [local irreducible] wires

/-- The forward joint with virtual carry `719` on the open trit hole `s 0 4 = base 1032`. -/
def kernel : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032)) (jointF portsJ (base 1028) (base 1))

/-- Record-length padding: 507 empty-correction erasures of the clean carry `base 512` (the
replaced first selector swap has 1 and the G1 half window 1022 records; the kernel has 516). -/
def padded : Program := kernel++JointInverse1588.padding

theorem padded_counts : toffoliCount padded=773 ∧ measurementCount padded=1023 := by
  have j := jointF_counts portsJ portsJ_widths (base 1028) (base 1)
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032)) (jointF portsJ (base 1028) (base 1))
  have p := padding_counts
  simp only [padded,kernel,toffoliCount_append,measurementCount_append,r.1,r.2,j.1,j.2,p.1,p.2]
  all_goals simp

theorem padded_slots : gateSlots padded≤8484 := by
  have j := jointF_slots portsJ portsJ_widths (base 1028) (base 1)
  have p : gateSlots JointInverse1588.padding=507 := by
    have h (n : Nat) : gateSlots (List.replicate n (Instr.measureX (base 512) [] []))=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ,gateSlots_cons,ih]
        simp [instructionSlots]
        omega
    exact h 507
  simp only [padded,kernel,gateSlots_append,rename_gateSlots,p]
  omega

theorem padded_physical : GatePhysical padded := by
  have j := jointF_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  have p : GatePhysical JointInverse1588.padding := by
    intro i hi
    rw [JointInverse1588.padding,List.mem_replicate] at hi
    rw [hi.2]
    simp [PhysicalInstr]
  simp only [padded,kernel,gatePhysical_append]
  exact ⟨gatePhysical_rename _ (Equiv.swap _ _).injective _ j,p⟩

theorem hole_free : base 1032∉wires (jointF portsJ (base 1028) (base 1)) := by
  have sup := jointF_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  intro used
  have m := List.mem_toFinset.mp (sup used)
  have off := off_ports 1032 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [retSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact off.1 h
  · exact off.2.1 h
  · exact off.2.2 (List.mem_of_mem_take h)
  · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
    omega

theorem padded_support : wires padded⊆kernelSites := by
  have sup := jointF_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq] at lo
  have keep (q : Wire) (hq : q∈wires (jointF portsJ (base 1028) (base 1))) : q∈kernelSites := by
    have m := List.mem_toFinset.mp (sup hq)
    have q1541 : q≠base 1541 := fun e => lo _ (Or.inr e) hq
    simp only [retSites,List.mem_append] at m
    simp only [kernelSites,List.mem_toFinset,List.mem_append]
    rcases m with ((h|h)|h)|h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [portsJ_take255,List.mem_append,List.mem_singleton] at h
      rcases h with h|h
      · exact Or.inl (Or.inr h)
      · exact absurd h q1541
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  intro q hq
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at hq
  rcases hq with hq|hq
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    by_cases a719 : a=base 719
    · subst a
      rw [Equiv.swap_apply_left]
      simp [kernelSites]
    · by_cases a1032 : a=base 1032
      · exact absurd (a1032 ▸ ha) hole_free
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032]
        exact keep a ha
  · have e : q=base 512 := Finset.mem_singleton.mp (pad_wires (base 512) 507 hq)
    subst e
    have m : base 512∈wireBlock base 512 253 :=
      List.mem_map.mpr ⟨512,by simp [List.mem_range'_1],rfl⟩
    simp only [kernelSites,List.mem_toFinset,List.mem_append,portsJ_take254]
    exact Or.inl (Or.inr (Or.inl m))

theorem padded_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires padded := by
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq] at lo
  rcases hi with rfl|rfl|rfl|rfl
  · intro used
    have m := List.mem_toFinset.mp (padded_support used)
    have off := off_ports 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact off.1 h
    · exact off.2.1 h
    · exact off.2.2 (List.mem_of_mem_take h)
    · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
      omega
  all_goals
    intro used
    simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
    rcases used with used|used
    · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
      by_cases a719 : a=base 719
      · subst a719
        rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
        omega
      · by_cases a1032 : a=base 1032
        · subst a1032
          exact hole_free ha
        · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
          subst eq
          first
            | exact a719 rfl
            | exact lo _ (Or.inl rfl) ha
            | exact lo _ (Or.inr rfl) ha
    · have e := Finset.mem_singleton.mp (pad_wires (base 512) 507 used)
      rw [base_injective.eq_iff] at e
      omega

/-- On any replay state with clean scalar bank, clean flag and open trit hole, the padded kernel
performs the joint entry `(Z,0) ↦ ((±Z)/2, J?Z:0)`. -/
theorem padded_pair (st : BasisState) (clean : ∀q∈BalancedCircuit.work portsJ,st q=false)
    (sign : st (base 2409)=false) (hole : st (base 1032)=false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st (centerWord Z) 0) padded
      (PairFrame portsJ.r portsJ.y st
        (centerWord ((if st (base 1028) && !st (base 1) then -Z else Z)/2))
        (centerWord (if st (base 1028) then Z else 0))) := by
  have j := jointF_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have a512 := off_data 512 (by omega) (by omega)
  let mk := m.take (measurementCount kernel)
  have out := j s mk input
  have in719 : s.basis (base 719)=false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032)=false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 719)=false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 1032)=false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  have k : run kernel mk s=run (jointF portsJ (base 1028) (base 1)) mk s :=
    rebind_swap_run _ _ _ s mk in719 in1032 o719 o1032
  have o512 : (run (jointF portsJ (base 1028) (base 1)) mk s).basis (base 512)=false :=
    (out.2.2.2 _ a512.1 a512.2).trans (clean _ (carry_work 512 (by omega)))
  have shape : run padded m s=run (jointF portsJ (base 1028) (base 1)) mk s := by
    rw [padded,run_append,k,JointInverse1588.padding]
    exact pad_run (base 512) 507 _ _ o512
  rw [shape]
  exact out

/-- Toffoli saving of the S1 (divide) first body: the 256-T first selector swap and the 765-T
comparator-free G1 half window become the 773-T padded forward joint. -/
def saving (divide : Bool) : Nat := if divide then 248 else 0

end ECDSAAdd.Entrant.JointForward1588

/-! ### Syntax-slot comparison with the replaced half window -/
set_option maxRecDepth 100000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic MappedCompressed Challenge

/-- Checked by kernel evaluation (`decide +kernel`): the generic forward half has at least 8484
slots, so the padded forward joint (≤ 8484) never increases the slot count. -/
theorem half_slots_lower : 8484≤gateSlots (Q6EndpointCell.half true base (base 2409)) := by
  decide +kernel

end ECDSAAdd.Entrant.JointForward1588
