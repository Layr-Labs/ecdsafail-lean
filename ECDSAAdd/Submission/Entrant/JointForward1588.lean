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
  just cleared (as `JointInverse1588.clearH`).

Retiring virtual `760` (carry #248) for the 1,587-qubit layout, exactly as in `JointInverse1588`:
* during the parity carry chain of the final `clearParity` carry #248 sits on `rmsb`, which
  `prepareMagnitude` has just cleared and the chain never reads (`clearParityF`, a pure rename);
* during the inner adder carry #248 sits on carry #1, measured away before `loanW`'s two
  measurements and recomputed after its two Toffolis (`loanF`, +1 Toffoli, +1 record). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false


/-! ### Retiring carry #248 (virtual `760`): the measured loan of carry #1 and the `rmsb` host
(copies of the `JointInverse1588` lemmas, so that this file only relies on unchanged helpers there) -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

/-- After the four leading majorities, carry #1 is the majority of source bit 1, `r1` and carry #0. -/
theorem pre4_c1F (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (h1 : s.basis (cAt L 1)=false) :
    (run (pre4 L) [] s).basis (cAt L 1)=carryBit ((source L 1).value (run (pre4 L) [] s).basis)
      ((run (pre4 L) [] s).basis (rAt L 1)) ((run (pre4 L) [] s).basis (cAt L 0)) := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  rw [hr,hc] at nd
  have sub : [lowY L,L.r0,r1,r2,r3,c0,c1,c2,c3].Sublist
      (lowY L::(L.r0::r1::r2::r3::r4::rt++c0::c1::c2::c3::ct)) := by
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    exact List.nil_sublist _
  have nd9 := nd.sublist sub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd9
  rcases nd9 with ⟨⟨u0,u1,u2,u3,uc0,uc1,uc2,uc3⟩,⟨⟨a1,a2,a3,a0c0,a0c1,a0c2,a0c3⟩,
    ⟨⟨b2,b3,b1c0,b1c1,b1c2,b1c3⟩,⟨⟨c23,c2c0,c2c1,c2c2,c2c3⟩,⟨⟨d0,d1,d2,d3⟩,
    ⟨⟨g01,g02,g03⟩,⟨⟨g12,g13⟩,g23⟩⟩⟩⟩⟩⟩⟩
  have src (i : Nat) (hi : i<4) (y cin co : Wire) (hy : y∈L.r)
      (hcin : cin=lowY L ∨ cin∈L.carry.take 255) (hco : co∈L.carry.take 255) :
      ∀q∈(source L i).wires,q∉[y,cin,co] := by
    intro q hq bad
    have aw := away q (source_site L i (by omega) q hq)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at aw bad
    rcases bad with rfl|rfl|rfl
    · exact aw.2.1 hy
    · rcases hcin with rfl|h
      · exact aw.1 rfl
      · exact aw.2.2 h
    · exact aw.2.2 hco
  have valid (i : Nat) (hi : i<4) := sources_valid L hn _ (source_mem L i (by omega))
  have rm (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    rw [hr]
    interval_cases i <;> simp [e0,e1,e2,e3]
  have cm (i : Nat) (hi : i<4) : cAt L i∈L.carry.take 255 := by
    rw [hc]
    interval_cases i <;> simp [f0,f1,f2,f3]
  have k0 := maj_keep (source L 0) (valid 0 (by decide)) (rAt L 0) (lowY L) (cAt L 0)
    (by rw [e0,f0];simp [Ne.symm u0,uc0,a0c0])
    (src 0 (by decide) _ _ _ (rm 0 (by decide)) (Or.inl rfl) (cm 0 (by decide)))
  have m1 := Affine.majority_correct (source L 1) (valid 1 (by decide)) (rAt L 1) (cAt L 0) (cAt L 1)
    (by rw [e1,f0,f1];simp [b1c0,b1c1,g01])
    (src 1 (by decide) _ _ _ (rm 1 (by decide)) (Or.inr (cm 0 (by decide))) (cm 1 (by decide)))
  have k2 := maj_keep (source L 2) (valid 2 (by decide)) (rAt L 2) (cAt L 1) (cAt L 2)
    (by rw [e2,f1,f2];simp [c2c1,c2c2,g12])
    (src 2 (by decide) _ _ _ (rm 2 (by decide)) (Or.inr (cm 1 (by decide))) (cm 2 (by decide)))
  have k3 := maj_keep (source L 3) (valid 3 (by decide)) (rAt L 3) (cAt L 2) (cAt L 3)
    (by rw [e3,f2,f3];simp [d2,d3,g23])
    (src 3 (by decide) _ _ _ (rm 3 (by decide)) (Or.inr (cm 2 (by decide))) (cm 3 (by decide)))
  have z (b : Affine.Bit) (y cin co : Wire) : measurementCount (Affine.majority b y cin co)=0 :=
    (Affine.bit_counts b y cin co).2.1
  -- wires of source bit 1 and the two read sites avoid carries #1..#3
  have sw (q : Wire) (hq : q∈(source L 1).wires) (i : Nat) (hi : i<4) : q≠cAt L i := by
    intro e
    have aw := away q (source_site L 1 (by decide) q hq)
    exact aw (by rw [e]; simp [cm i hi])
  have r1c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : rAt L 1≠cAt L i := by
    rw [e1]
    interval_cases i
    · rw [f1];exact b1c1
    · rw [f2];exact b1c2
    · rw [f3];exact b1c3
  have c0c (i : Nat) (h1 : 1 ≤ i) (h4 : i<4) : cAt L 0≠cAt L i := by
    rw [f0]
    interval_cases i
    · rw [f1];exact g01
    · rw [f2];exact g02
    · rw [f3];exact g03
  have c1c (i : Nat) (h1 : 2 ≤ i) (h4 : i<4) : cAt L 1≠cAt L i := by
    rw [f1]
    interval_cases i
    · rw [f2];exact g12
    · rw [f3];exact g13
  have c10 : cAt L 1≠cAt L 0 := by rw [f0,f1];exact Ne.symm g01
  simp only [pre4,run_append,measurementCount_append,z,Nat.add_zero,List.take_zero,List.drop_zero,
    List.take_nil,List.drop_nil]
  generalize hs0 : run (Affine.majority (source L 0) (rAt L 0) (lowY L) (cAt L 0)) [] s=s0
  have s0c1 : s0.basis (cAt L 1)=false := by rw [←hs0,(k0 _ _).2 _ c10];exact h1
  rw [m1 s0 []]
  generalize hs1 : (⟨s0.phase,writeBit s0.basis (cAt L 1) (s0.basis (cAt L 1) ^^
    carryBit ((source L 1).value s0.basis) (s0.basis (rAt L 1)) (s0.basis (cAt L 0)))⟩ : State)=s1
  have k23 (q : Wire) (h2 : q≠cAt L 2) (h3 : q≠cAt L 3) :
      (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis q=s1.basis q := by
    rw [(k3 _ _).2 q h3,(k2 _ _).2 q h2]
  have s1keep (q : Wire) (hq : q≠cAt L 1) : s1.basis q=s0.basis q := by
    rw [←hs1];simp [writeBit,hq]
  have value : (source L 1).value (run (Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)) []
        (run (Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)) [] s1)).basis=
      (source L 1).value s0.basis := by
    apply Affine.Bit.value_congr
    intro q hq
    rw [k23 q (sw q hq 2 (by decide)) (sw q hq 3 (by decide)),s1keep q (sw q hq 1 (by decide))]
  rw [value,k23 _ (c1c 2 (by decide) (by decide)) (c1c 3 (by decide) (by decide)),
    k23 _ (r1c 2 (by decide) (by decide)) (r1c 3 (by decide) (by decide)),k23 _ (c0c 2 (by decide) (by decide)) (c0c 3 (by decide) (by decide)),
    s1keep _ (r1c 1 (by decide) (by decide)),s1keep _ (c0c 1 (by decide) (by decide)),←hs1]
  simp [writeBit,s0c1]

/-- The inner adder's carries are not among carries #0..#3. -/
theorem carry_drop4_neF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈(L.carry.take 255).drop 4) (i : Nat) (hi : i<4) : q≠cAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndc : (L.carry.take 255).Nodup := (carry_nodup L hn).sublist (List.take_sublist _ _)
  rw [hct] at ndc hq
  simp only [List.drop_succ_cons,List.drop_zero] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndc
  intro e
  interval_cases i
  · rw [f0] at e;exact ndc.1.2.2.2 (e ▸ hq)
  · rw [f1] at e;exact ndc.2.1.2.2 (e ▸ hq)
  · rw [f2] at e;exact ndc.2.2.1.2 (e ▸ hq)
  · rw [f3] at e;exact ndc.2.2.2.1 (e ▸ hq)

/-- The inner adder's targets are not among targets #0..#3. -/
theorem r_drop4_neF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.r.drop 4) (i : Nat) (hi : i<4) : q≠rAt L i := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have ndr := EntryHalf5.target_nodup L hn
  rw [hr] at ndr hq
  simp only [List.drop_succ_cons,List.drop_zero,List.mem_cons] at hq
  simp only [List.nodup_cons,List.mem_cons,not_or] at ndr
  intro e
  interval_cases i
  · rw [e0] at e;subst e
    rcases hq with h|h
    · exact ndr.1.2.2.2.1 h
    · exact ndr.1.2.2.2.2 h
  · rw [e1] at e;subst e
    rcases hq with h|h
    · exact ndr.2.1.2.2.1 h
    · exact ndr.2.1.2.2.2 h
  · rw [e2] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.1.2.1 h
    · exact ndr.2.2.1.2.2 h
  · rw [e3] at e;subst e
    rcases hq with h|h
    · exact ndr.2.2.2.1.1 h
    · exact ndr.2.2.2.1.2 h

/-- Carries #0..#2 and the targets #0..#3 lie outside the inner adder. -/
theorem low_inner_freeF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (∀i,i<3 → cAt L i∉wires (inner L)) ∧ (∀i,i<4 → rAt L i∉wires (inner L)) := by
  have flagsAway (q : Wire) (hq : q∈[L.parity,L.lower,L.one]) : q∉L.r++L.y++L.carry :=
    flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  constructor
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ci : cAt L i∈L.carry := carry_mem L hw i (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ci])
    · exact carry_not_r L hn _ ci (List.mem_of_mem_drop h)
    · exact carry_drop4_neF L hw hn _ h i (by omega) rfl
    · exact carry_index_ne L hw hn i 3 (by omega) (by decide) (by omega) h
  · intro i hi used
    have m := List.mem_toFinset.mp (inner_support L used)
    have ri : rAt L i∈L.r := by
      have len := BalancedCleanup.widths L.toLayout hw
      have lt : i<L.r.length := by rw [len.2.1];omega
      simp only [rAt,List.getD_eq_getElem _ _ lt]
      exact List.getElem_mem lt
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact flagsAway _ (inner_sites L _ h) (by simp [ri])
    · exact r_drop4_neF L hw hn _ h i hi rfl
    · exact carry_not_r L hn _ (List.mem_of_mem_take (List.mem_of_mem_drop h)) ri
    · exact carry_not_r L hn (cAt L 3) (carry_mem L hw 3 (by decide)) (by rw [←h];exact ri)

/-- A wire outside `P` and distinct from the two swapped sites stays outside the renamed `P`. -/
theorem swap_freeF (a b q : Wire) (P : Program) (hq : q∉wires P) (ha : q≠a) (hb : q≠b) :
    q∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=Equiv.swap a b q := by rw [←ex];simp only [Equiv.swap_apply_self]
  rw [Equiv.swap_apply_of_ne_of_ne ha hb] at back
  exact hq (back ▸ hx)

/-- The image of a renamed program lies in any set containing the old support and both sites. -/
theorem swap_supportF (a b : Wire) (P : Program) (W : Finset Wire) (hP : wires P⊆W)
    (ha : a∈W) (hb : b∈W) : wires (renameProgram (Equiv.swap a b) P)⊆W := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  have hyW := hP hy
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- The measured loan of carry #1 around `loanW`: carry #1 (`maj(one⊕sign,r1,c0)`, still readable
while `sign` is present) is erased before `loanW`'s two measurements and recomputed after its two
Toffolis; inside, carry #248 is hosted on carry #1's site. -/
def loanF (L : Layout) (J B : Wire) : Program :=
  Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++
    (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L)
      (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))++
    Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))

theorem loanF_counts (L : Layout) (J B : Wire) :
    toffoliCount (loanF L J B)=toffoliCount (inner L)+3 ∧
    measurementCount (loanF L J B)=3+measurementCount (inner L) := by
  have e := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have w := loanW_counts L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L))
  have r := renameProgram_counts (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)
  simp only [loanF,toffoliCount_append,measurementCount_append,e.1,e.2.1,e.2.2.1,e.2.2.2.1,
    w.1,w.2,r.1,r.2]
  omega

/-- On a state where `sign = lower∧lowY`, `lowY = J∧B` and every carry is clean, the carry-#1 loan
after `pre4` runs as the inner adder (it only reads three extra records). -/
theorem loanF_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (r : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    run (loanF L J B) r (run (pre4 L) [] b)=run (inner L) (r.drop 3) (run (pre4 L) [] b) := by
  generalize hx : run (pre4 L) [] b=x
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have nd7 := dist.1
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have lowCarry (i : Nat) (hi : i<4) : cAt L i∈L.carry := carry_mem L hw i (by omega)
  have offData (q : Wire) (hq : q∉L.r++L.y++L.carry) : q∉L.r ∧ ∀i,i<4 → q≠cAt L i :=
    ⟨fun h => hq (by simp [h]),fun i hi e => hq (by rw [e];simp [lowCarry i hi])⟩
  have pk (q : Wire) (h4 : ∀i,i<4 → q≠cAt L i) : x.basis q=b.basis q := by
    rw [←hx]
    exact (pre4_run L hw hn b []).2 q (h4 0 (by decide)) (h4 1 (by decide)) (h4 2 (by decide))
      (h4 3 (by decide))
  have keepS := pk L.sign (offData _ (flags _ (by simp))).2
  have keepA := pk L.lower (offData _ (flags _ (by simp))).2
  have keepU := pk (lowY L) (fun i hi e => y_not_carry L hn _ y0 (by rw [e];exact lowCarry i hi))
  have keepJ := pk J (offData _ (notData _ hJ)).2
  have keepB := pk B (offData _ (notData _ hB)).2
  have hiIdx (k : Nat) (hk : 4≤k ∧ k<256) (i : Nat) (hi : i<4) : L.carry.getD k 0≠cAt L i :=
    carry_index_ne L hw hn k i (by omega) (by omega) (by omega)
  have keepLo := pk (cLo L) (hiIdx 4 (by decide))
  have keepHi := pk (cHi L) (hiIdx 254 (by decide))
  have keep248 := pk (cAt L 248) (hiIdx 248 (by decide))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have cleanX : ∀q∈(L.carry.take 255).drop 4,x.basis q=false := fun q hq =>
    (pk q (carry_drop4_neF L hw hn q hq)).trans (hc q (List.mem_of_mem_take (List.mem_of_mem_drop hq)))
  -- carry #1 holds its majority: erase it
  have c1val : x.basis (cAt L 1)=carryBit ((source L 1).value x.basis) (x.basis (rAt L 1))
      (x.basis (cAt L 0)) := by
    rw [←hx];exact pre4_c1F L hw hn b (hc _ (lowCarry 1 (by decide)))
  have valid1 := sources_valid L hn _ (source_mem L 1 (by decide))
  have r1mem : rAt L 1∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have c10 : cAt L 1≠cAt L 0 := carry_index_ne L hw hn 1 0 (by decide) (by decide) (by decide)
  have loc : [rAt L 1,cAt L 0,cAt L 1].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
      not_false_eq_true,and_true]
    exact ⟨⟨fun e => carry_not_r L hn _ (lowCarry 0 (by decide)) (e ▸ r1mem),
      fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)⟩,Ne.symm c10⟩
  have srcAway (q : Wire) (hq : q∈(source L 1).wires) : q∉L.r++L.y++L.carry := by
    have m := source_sites L 1 hq
    exact flagAway L hn q (by simp only [List.mem_cons,List.not_mem_nil,or_false] at m ⊢;tauto)
  have locAway : ∀q∈(source L 1).wires,q∉[rAt L 1,cAt L 0,cAt L 1] := by
    intro q hq bad
    simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl
    · exact srcAway _ hq (by simp [r1mem])
    · exact srcAway _ hq (by simp [lowCarry 0 (by decide)])
    · exact srcAway _ hq (by simp [lowCarry 1 (by decide)])
  have erase (t : List Bool) :
      run (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t x=
        ⟨x.phase,writeBit x.basis (cAt L 1) false⟩ :=
    Affine.erase_correct _ valid1 _ _ _ loc locAway x t c1val
  generalize hx1 : (⟨x.phase,writeBit x.basis (cAt L 1) false⟩ : State)=x1 at erase
  have x1keep (q : Wire) (hq : q≠cAt L 1) : x1.basis q=x.basis q := by
    rw [←hx1];simp [writeBit,hq]
  have x1c1 : x1.basis (cAt L 1)=false := by rw [←hx1];simp [writeBit]
  have lf := low_inner_freeF L hw hn
  have c1In : cAt L 1∉wires (inner L) := lf.1 1 (by decide)
  have c248ne1 : cAt L 248≠cAt L 1 := carry_index_ne L hw hn 248 1 (by decide) (by decide) (by decide)
  have cleanX1 : ∀q∈(L.carry.take 255).drop 4,x1.basis q=false := fun q hq =>
    (x1keep q (carry_drop4_neF L hw hn q hq 1 (by decide))).trans (cleanX q hq)
  have inn (t : List Bool) := inner_correct L hw hn x1 t cleanX1
  -- the renamed inner adder runs as the inner adder on `x1`
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) t x1=run (inner L) t x1 := by
    apply rebind_swap_run
    · rw [x1keep _ c248ne1,keep248];exact hc _ m248
    · exact x1c1
    · rw [(inn t).2 _ (carry_not_r L hn _ m248),x1keep _ c248ne1,keep248];exact hc _ m248
    · rw [run_preserves_outside _ _ _ _ c1In];exact x1c1
  -- loanW on `x1`
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e
      · exact flags L.parity (by simp) (by rw [←e];simp [y0])
      · exact flags L.lower (by simp) (by rw [←e];simp [y0])
      · exact flags L.one (by simp) (by rw [←e];simp [y0]))
      (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
      have sc := scalarND L hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e <;>
        (have c := List.nodup_iff_count.mp sc L.sign
         rw [e] at c;simp [List.count_cons] at c;omega))
      (offData _ (flags _ (by simp))).1 (fun h => flags L.sign (by simp) (by simp [h]))
  have uc (i : Nat) (hi : i<256) : lowY L≠L.carry.getD i 0 :=
    fun e => y_not_carry L hn _ y0 (by rw [e];exact carry_mem L hw i hi)
  have ec (i : Nat) (hi : i<256) : L.sign≠L.carry.getD i 0 :=
    fun e => flags L.sign (by simp) (by rw [e];exact List.mem_append_right _ (carry_mem L hw i hi))
  have loC : cLo L≠cAt L 1 := carry_index_ne L hw hn 4 1 (by decide) (by decide) (by decide)
  have hiC : cHi L≠cAt L 1 := carry_index_ne L hw hn 254 1 (by decide) (by decide) (by decide)
  have aC : L.lower≠cAt L 1 := fun e => flags L.lower (by simp)
    (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have jC : J≠cAt L 1 := fun e => notData J hJ (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have bC : B≠cAt L 1 := fun e => notData B hB (by rw [e];exact List.mem_append_right _ (lowCarry 1 (by decide)))
  have loan (t : List Bool) := loanW_run L.sign L.lower (lowY L) J B (cLo L) (cHi L)
    (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) x1 t nd7
    (by rw [x1keep _ (ec 1 (by decide)),x1keep _ aC,x1keep _ (uc 1 (by decide)),keepS,keepA,keepU];exact he)
    (by rw [x1keep _ (uc 1 (by decide)),x1keep _ jC,x1keep _ bC,keepU,keepJ,keepB];exact hu)
    (swap_freeF _ _ _ _ uIn (uc 248 (by decide)) (uc 1 (by decide)))
    (swap_freeF _ _ _ _ eIn (ec 248 (by decide)) (ec 1 (by decide)))
    (by
      intro t
      rw [host t]
      have i := (inn t).2
      exact ⟨i _ (offData _ (flags _ (by simp))).1,i _ (offData _ (notData _ hJ)).1,
        i _ (offData _ (notData _ hB)).1⟩)
    (by rw [x1keep _ loC,keepLo];exact hc _ (carry_mem L hw 4 (by decide)))
    (by rw [x1keep _ hiC,keepHi];exact hc _ (carry_mem L hw 254 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cLo L) (carry_not_r L hn _ (carry_mem L hw 4 (by decide))),x1keep _ loC,keepLo]
      exact hc _ (carry_mem L hw 4 (by decide)))
    (by
      intro t
      rw [host t,(inn t).2 (cHi L) (carry_not_r L hn _ (carry_mem L hw 254 (by decide))),x1keep _ hiC,keepHi]
      exact hc _ (carry_mem L hw 254 (by decide)))
  -- the inner adder on `x1` is the inner adder on `x` with carry #1 cleared
  have outside (t : List Bool) : run (inner L) t x1=
      ⟨(run (inner L) t x).phase,writeBit (run (inner L) t x).basis (cAt L 1) false⟩ := by
    rw [←hx1];exact G0CarryLoan5.run_write_outside (inner L) (cAt L 1) c1In x t false
  have innX (t : List Bool) := inner_correct L hw hn x t cleanX
  -- recompute carry #1
  have r1c1 : rAt L 1≠cAt L 1 := fun e => carry_not_r L hn _ (lowCarry 1 (by decide)) (e ▸ r1mem)
  have restore (t t' : List Bool) :
      run (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) t' (run (inner L) t x1)=
        run (inner L) t x := by
    rw [outside t,Affine.majority_correct _ valid1 _ _ _ loc locAway]
    generalize hy : run (inner L) t x=y
    have yc1 : y.basis (cAt L 1)=x.basis (cAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ c1In
    have yr1 : y.basis (rAt L 1)=x.basis (rAt L 1) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.2 1 (by decide))
    have yc0 : y.basis (cAt L 0)=x.basis (cAt L 0) := by
      rw [←hy];exact run_preserves_outside _ _ _ _ (lf.1 0 (by decide))
    have yv : (source L 1).value (Function.update y.basis (cAt L 1) false)=(source L 1).value x.basis := by
      apply Affine.Bit.value_congr
      intro q hq
      have qc1 : q≠cAt L 1 := fun e => locAway q hq (by simp [e])
      have qr : q∉L.r := fun h => srcAway q hq (by simp [h])
      rw [Function.update_of_ne qc1,←hy]
      exact (innX t).2 q qr
    apply State.extensionality
    · rfl
    · funext q
      by_cases qe : q=cAt L 1
      · subst qe
        simp only [writeBit,Function.update_self,Function.update_of_ne r1c1,Function.update_of_ne (Ne.symm c10),
          Bool.false_xor]
        rw [yv,yr1,yc0,←c1val,yc1]
      · simp [writeBit,qe]
  -- assemble
  have e1c : measurementCount (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))=1 :=
    (Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)).2.2.2.1
  rw [loanF,run_append,e1c,erase,run_append,run_take,loan,host,restore]
  congr 1
  rw [List.drop_drop]

/-- `positiveParity` with carry #248 hosted on `rmsb`: `prepareMagnitude` copies `rmsb` into the clean
`lower` and complements the whole target word under it, so `rmsb` is clean for the whole carry chain,
which reads only the low 255 target bits. -/
def positiveParityF (L : Layout) (ctl : Wire) : Program :=
  EntryHalf5.prepareMagnitude L++(renameProgram (Equiv.swap (cAt L 248) L.rmsb)
    (EntryHalf5.parityCarry L ctl)++(EntryHalf5.prepareMagnitude L).reverse)

def recoverParityF (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParityF L J++[.X J]

def clearParityF (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++recoverParityF L J

theorem positiveParityF_counts (L : Layout) (ctl : Wire) :
    toffoliCount (positiveParityF L ctl)=toffoliCount (EntryHalf5.positiveParity L ctl) ∧
    measurementCount (positiveParityF L ctl)=measurementCount (EntryHalf5.positiveParity L ctl) := by
  have r := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  simp only [positiveParityF,EntryHalf5.positiveParity,toffoliCount_append,measurementCount_append,r.1,r.2]
  exact ⟨trivial,trivial⟩

/-- `prepareMagnitude` leaves `rmsb` clean on a centered target word with clean `lower`. -/
theorem prepare_rmsbF (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    (run (EntryHalf5.prepareMagnitude L) m s).basis L.rmsb=false := by
  have nd := (List.nodup_append'.mp hn).2.1
  have h := BalancedCleanup.prepareSign_value L.toLayout hw nd R hr s m hR hz
  let t := run (EntryHalf5.prepareMagnitude L) m s
  change regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) at h
  change t.basis L.rmsb=false
  have b := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg b.1
  have c := constants
  have bound : (magnitude R).toNat<2^255 := by norm_num only [Nat.reducePow] at ⊢; omega
  have split : regValue L.r t.basis=regValue L.low t.basis+2^255*(t.basis L.rmsb).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append,(BalancedCleanup.widths L.toLayout hw).1]
    cases k : t.basis L.rmsb <;> simp [regValue,k]
  rw [h.1] at split
  cases k : t.basis L.rmsb
  · rfl
  · rw [k] at split
    simp only [Bool.toNat_true,Nat.mul_one] at split
    omega

theorem positiveParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParityF L ctl) m s=run (EntryHalf5.positiveParity L ctl) m s := by
  let c := run (EntryHalf5.prepareMagnitude L) [] s
  have pv := EntryHalf5.prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have rz : c.basis L.rmsb=false := prepare_rmsbF L hw hn R hr s [] hR hz
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have notLower (a : Wire) (ha : a∈L.carry) : a≠L.lower := fun e =>
    flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ ha)
  have c248 : c.basis (cAt L 248)=false :=
    (pv.2.2 _ (carry_not_r L hn _ m248) (notLower _ m248)).trans (hc _ m248)
  have nd := EntryHalf5.carry_nodup L hn ctl hctl
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    have am := List.mem_of_mem_take ha
    exact (pv.2.2 a (carry_not_r L hn a am) (notLower a am)).trans (hc a am)
  have len := BalancedCleanup.widths L.toLayout hw
  have one (t : List Bool) := DiagonalCarry5.correct EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower ctl L.parity nd
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) c t clean
  have pc : cAt L 248≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have pr : L.rmsb≠L.parity := fun e =>
    flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
  have host (t : List Bool) :
      run (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)) t c=
        run (EntryHalf5.parityCarry L ctl) t c := by
    apply rebind_swap_run _ _ _ c t c248 rz
    · exact ((one t).2.1 _ pc).trans c248
    · exact ((one t).2.1 _ pr).trans rz
  have pm := (EntryHalf5.prepare_counts L).2
  have rc := renameProgram_counts (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L ctl)
  rw [positiveParityF,EntryHalf5.positiveParity,run_append,run_append (EntryHalf5.prepareMagnitude L),
    pm,List.take_zero,List.drop_zero,run_append,run_append (EntryHalf5.parityCarry L ctl),rc.2,host]

theorem recoverParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParityF L J) m s=run (EntryHalf5.recoverParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have uz : u.basis L.lower=false := by
    rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq =>
    (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq)
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  have cnt := (positiveParityF_counts L J).2
  have e := context_eq [.X J] (EntryHalf5.positiveParity L J) (positiveParityF L J) [.X J] 0 s m rfl
    (by rw [cnt,Nat.zero_add])
    (by
      intro r
      rw [first,List.drop_zero]
      exact positiveParityF_eq L hw hn J hJ R hr u r sameR uz uc)
  rw [recoverParityF,EntryHalf5.recoverParity,e,List.drop_zero,cnt,List.take_append_drop]

theorem clearParityF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hz : s.basis L.lower=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParityF L J) m s=run (clearParity L J) m s := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have uz : u.basis L.lower=false := by simpa [u,writeBit,lp] using hz
  have uc : ∀q∈L.carry,u.basis q=false := fun q hq => by
    simpa [u,writeBit,away q (by simp [hq])] using hc q hq
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := by simp [run,u]
  rw [clearParityF,clearParity,run_append,run_append,
    show measurementCount [Instr.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,List.take_zero,List.drop_zero,first]
  exact recoverParityF_eq L hw hn J hJ R hr u m ur uz uc

/-- `clearParity` with carry #4 on `one`, carry #254 on `sign` and carry #248 on `rmsb`. -/
def clearF (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (cHi L) L.sign) (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J))

theorem clearF_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (ho : s.basis L.one=false) (hs : s.basis L.sign=false) :
    run (clearF L J) m s=run (clearParity L J) m s := by
  have dist := hosts_distinct L hw hn
  have lo : cLo L∈L.carry := carry_mem L hw 4 (by decide)
  have hi : cHi L∈L.carry := carry_mem L hw 254 (by decide)
  have base := clearParityF_eq L hw hn J hJ R hr s m hR hl hc
  have cx := clear_xor L hw hn J hJ R hr s m hR hl hc
  have same (q : Wire) (hq : q≠L.parity) : (run (clearParityF L J) m s).basis q=s.basis q := by
    rw [base,cx]; simp [writeBit,hq]
  have innerEq : run (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J)) m s=
      run (clearParityF L J) m s :=
    rebind_swap_run _ _ _ s m (hc _ lo) ho
      ((same _ (Ne.symm dist.2.2.1)).trans (hc _ lo))
      ((same _ (Ne.symm dist.2.2.2.2.2.2.1)).trans ho)
  rw [clearF,rebind_swap_run _ _ _ s m (hc _ hi) hs
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.1)).trans (hc _ hi))
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.2.2.2.2)).trans hs),innerEq,base]

end ECDSAAdd.Entrant.JointForward1588

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines RecordedQuantum

/-- Exact syntax slots of a literal carry chain: three per bit, four more per set literal bit. -/
theorem chain_slotsF (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    gateSlots (DiagonalCarry5.chain bs xs cs cin ctl target)=3*bs.length+4*bs.count true+1 := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [DiagonalCarry5.chain,ex,ec,gateSlots,instructionSlots]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have r := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell : gateSlots (mappedMajority (DiagonalCarry5.bit b) x cin c)+
            gateSlots (mappedEraseCarry (DiagonalCarry5.bit b) x cin c)=3+4*(if b then 1 else 0) := by
          cases b <;> norm_num [DiagonalCarry5.bit,mappedMajority,mappedEraseCarry,gateSlots,instructionSlots]
        simp only [DiagonalCarry5.chain,gateSlots_append,List.length_cons,List.count_cons]
        cases b <;> simp at cell ⊢ <;> omega

theorem parityBits_countF : EntryHalf5.parityBits.count true=7 := by decide

theorem parityCarry_slotsF (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (EntryHalf5.parityCarry L J)=794 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := chain_slotsF EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  rw [parityBits_countF,EntryHalf5.parityBits,DiagonalCarry5.literal_length] at h
  exact h

end ECDSAAdd.Entrant.JointForward1588

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

/-- A renamed program avoids the first swapped site when the old program avoids the second. -/
theorem swap_free_leftF (a b : Wire) (P : Program) (hb : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  have back : x=b := by
    have h := congrArg (Equiv.swap a b) ex
    rwa [Equiv.swap_apply_self,Equiv.swap_apply_left] at h
  exact hb (back ▸ hx)

theorem prep_supportF (L : Layout) :
    wires (EntryHalf5.prepareMagnitude L)⊆(L.lower::L.r).toFinset := by
  intro q hq
  simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,Finset.mem_union] at hq
  rcases hq with h|h
  · have e : q=L.rmsb ∨ q=L.lower := by simpa [wires,Instr.wires] using h
    rcases e with rfl|rfl
    · simp [BalancedCleanup.Layout.r]
    · simp
  · have h' := signComplement_wires_subset L.lower L.r h
    simpa only [List.mem_toFinset,List.mem_cons] using h'

theorem chain_supportF (L : Layout) (hw : L.Widths) (J : Wire) :
    wires (EntryHalf5.parityCarry L J)⊆(J::L.parity::L.lower::(L.low++L.carry.take 255)).toFinset := by
  have len := BalancedCleanup.widths L.toLayout hw
  exact DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])

/-- The chain-hosted parity clear never touches `one`, `sign` or carry #248. -/
theorem clearParityF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (q : Wire) (hq : q=L.one ∨ q=L.sign ∨ q=cAt L 248) : q∉wires (clearParityF L J) := by
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rmem : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have sc := scalarND L hn
  have qw : q∈L.wires := by
    rcases hq with rfl|rfl|rfl
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · exact data_member L _ (by simp [m248])
  have qJ : q≠J := fun e => hJ (e ▸ qw)
  have qr : q∉L.r := by
    rcases hq with rfl|rfl|rfl
    · exact fun h => flagAway L hn L.one (by simp) (by simp [h])
    · exact fun h => flagAway L hn L.sign (by simp) (by simp [h])
    · exact carry_not_r L hn _ m248
  have qu : q≠lowY L := by
    rcases hq with rfl|rfl|rfl
    · exact fun e => flagAway L hn L.one (by simp) (by rw [e];simp [y0])
    · exact fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [y0])
    · exact fun e => y_not_carry L hn _ y0 (e ▸ m248)
  have qp : q≠L.parity := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.parity;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.parity (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have ql : q≠L.lower := by
    rcases hq with rfl|rfl|rfl
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · intro e;have h := List.nodup_iff_count.mp sc L.lower;rw [←e] at h;simp [List.count_cons] at h;omega
    · exact fun e => flagAway L hn L.lower (by simp) (by rw [←e];exact List.mem_append_right _ m248)
  have prepF : q∉wires (EntryHalf5.prepareMagnitude L) := by
    intro used
    have m := List.mem_toFinset.mp (prep_supportF L used)
    simp only [List.mem_cons] at m
    rcases m with e|h
    · exact ql e
    · exact qr h
  have lowR (x : Wire) (hx : x∈L.low) : x∈L.r := by simp [BalancedCleanup.Layout.r,hx]
  have chainF : q∉wires (renameProgram (Equiv.swap (cAt L 248) L.rmsb) (EntryHalf5.parityCarry L J)) := by
    rcases hq with rfl|rfl|rfl
    · apply swap_freeF _ _ _ _ _ (fun e => flagAway L hn L.one (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.one (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.one (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_freeF _ _ _ _ _ (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
        (fun e => flagAway L hn L.sign (by simp) (by rw [e];simp [rmem]))
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact qJ e
      · exact qp e
      · exact ql e
      · exact qr (lowR _ h)
      · exact flagAway L hn L.sign (by simp) (List.mem_append_right _ (List.mem_of_mem_take h))
    · apply swap_free_leftF
      intro used
      have m := List.mem_toFinset.mp (chain_supportF L hw J used)
      have rw' : L.rmsb∈L.wires := data_member L _ (by simp [rmem])
      have nr := EntryHalf5.target_nodup L hn
      simp only [List.mem_cons,List.mem_append] at m
      rcases m with e|e|e|h|h
      · exact hJ (e ▸ rw')
      · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [rmem])
      · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [rmem])
      · simp only [BalancedCleanup.Layout.r] at nr
        exact (List.nodup_append'.mp nr).2.2 h (by simp)
      · exact carry_not_r L hn _ (List.mem_of_mem_take h) rmem
  simp only [clearParityF,recoverParityF,positiveParityF,wires_append,wires_reverse,Finset.mem_union,not_or]
  refine ⟨?_,⟨⟨?_,prepF,chainF,prepF⟩,?_⟩⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      or_false,not_or]
    exact ⟨qu,qp⟩
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false]
    exact qJ

theorem clearParityF_support (L : Layout) (J : Wire) (W : Finset Wire)
    (hP : wires (clearParity L J)⊆W) (h248 : cAt L 248∈W) (hr : L.rmsb∈W) :
    wires (clearParityF L J)⊆W := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,wires_append,wires_reverse,
    Finset.union_subset_iff] at hP
  simp only [clearParityF,recoverParityF,positiveParityF,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,swap_supportF _ _ _ _ hP.2.1.2.2.1 h248 hr,hP.2.1.2.1⟩,hP.2.2⟩⟩

theorem clearParityF_physical (L : Layout) (J : Wire) (hP : GatePhysical (clearParity L J)) :
    GatePhysical (clearParityF L J) := by
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gatePhysical_append] at hP
  simp only [clearParityF,recoverParityF,positiveParityF,gatePhysical_append]
  exact ⟨hP.1,⟨⟨hP.2.1.1,hP.2.1.2.1,gatePhysical_rename _ (Equiv.swap _ _).injective _ hP.2.1.2.2.1,
    hP.2.1.2.2.2⟩,hP.2.2⟩⟩

theorem clearParityF_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (clearParityF L J)=256 ∧ measurementCount (clearParityF L J)=255 := by
  have p := positiveParityF_counts L J
  have c := clearParity_counts L hw J
  simp only [clearParity,EntryHalf5.recoverParity,toffoliCount_append,measurementCount_append] at c
  simp only [clearParityF,recoverParityF,toffoliCount_append,measurementCount_append,p.1,p.2]
  exact c

theorem clearParityF_slots (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (clearParityF L J)=1311 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have mag : gateSlots (EntryHalf5.prepareMagnitude L)=257 := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,signComplement_gateSlots,len.2.1]
  have ch := parityCarry_slotsF L hw J
  simp only [clearParityF,recoverParityF,positiveParityF,gateSlots_append,reverse_gateSlots,
    rename_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,mag,ch]

/-- The four extra carry-#1 instructions only touch source bit 1, `r1` and carries #0/#1. -/
theorem loanF_edge_support (L : Layout) :
    wires (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset ∧
    wires (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1))⊆
      ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset := by
  have b := Affine.local_support (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
    ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset
    (fun q hq => List.mem_toFinset.mpr (List.mem_append_left _ hq))
    (by simp) (by simp) (by simp)
  exact ⟨b.2.1,b.1⟩

theorem source1_sitesF (L : Layout) (q : Wire) (hq : q∈(source L 1).wires) : q=L.one ∨ q=L.sign := by
  simpa [source,Affine.Bit.wires] using hq

theorem loanF_slots (L : Layout) (J B : Wire) : gateSlots (loanF L J B)=gateSlots (inner L)+20 := by
  have a : gateSlots ([Instr.measureX L.sign [] [Correction.CZ L.lower (lowY L)],
      Instr.measureX (lowY L) [] [Correction.CZ J B]] : Program)=4 := rfl
  have b : gateSlots ([Instr.CCX J B (lowY L),Instr.CCX L.lower (lowY L) L.sign] : Program)=2 := rfl
  have ls := Affine.local_slots (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have t1 : (source L 1).terms.length=1 := by simp [source]
  simp only [loanF,loanW,gateSlots_append,rename_gateSlots,a,b,ls.1,ls.2.1,t1]
  omega

end ECDSAAdd.Entrant.JointForward1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.JointForward1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 JointInverse1588
attribute [local irreducible] run

/-- The forward addition with carry #4 on `lowY`, carry #254 on `sign` and (measured loan of carry #1)
carry #248 on carry #1's site inside source bits 4..255. -/
def arithH (L : Layout) (J B : Wire) : Program :=
  pre4 L++loanF L J B++post4 L

/-- `EntryRetained5.program` with the hosted carries (#4, #254, and #248 retired from its own site). -/
def programF (L : Layout) (J B : Wire) : Program :=
  prepare L J B++arithH L J B++eraseScalarsAt L J B++clearF L J

theorem pre4_keep (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (b : State) (q : Wire)
    (hc : ∀i,i<4 → q≠cAt L i) :
    (run (pre4 L) [] b).basis q=b.basis q ∧ (run (pre4 L) [] b).phase=b.phase := by
  have p := pre4_run L hw hn b []
  exact ⟨p.2 q (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide)),p.1⟩

/-- The final parity clear with carries #4 and #254 on the cleared `one` and `sign` (and carry #248 on
`rmsb`) runs as the record's `clearParity` on every state reached by the forward prefix and the scalar
erasure. -/
theorem tail_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (t1 t2 n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (clearF L J) n (run (eraseScalarsAt L J B) t2 (run (prefixProgram L J B) t1 s))=
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
  exact clearF_eq L hw hn J hJ _ rc c n cR ca cCarry cOne cSign

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
  let Q := loanF L J B
  let Post := post4 L++eraseScalarsAt L J B++clearF L J
  have shapeF : programF L J B=Pre++Q++Post := by
    simp only [programF,arithH,Pre,Q,Post,List.append_assoc]
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have pc := prepare_counts L hw J B
  have preRun : run Pre [] s=run (pre4 L) [] (run (prepare L J B) [] s) := by
    simp only [Pre,run_append,List.take_nil,List.drop_nil]
  have hpre : measurementCount Pre=0 := by
    simp only [Pre,measurementCount_append,pc.2,(pre4_counts L).2]
  have stepA := context_eq Pre (inner L) Q Post 3 s m hpre (loanF_counts L J B).2 (by
    intro r
    rw [preRun]
    exact loanF_run L hw hn J B hJ hB hJB _ r
      (by rw [prep.a,prep.u];exact prep.e)
      (by rw [prep.u,prep.j,prep.b])
      prep.carry)
  refine ⟨(m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeF,stepA]
  generalize (m.drop 3).take (measurementCount (inner L))++m.drop (measurementCount Q)=n
  have shape1 : Pre++inner L++Post=(prefixProgram L J B++eraseScalarsAt L J B)++clearF L J := by
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
    toffoliCount (programF L J B)=774 ∧ measurementCount (programF L J B)=517 := by
  have p:=prepare_counts L hw J B
  have i:=inner_counts L hw
  have w:=loanF_counts L J B
  have e:=eraseScalars_counts L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb
  have c:=clearParityF_counts L hw J
  have c1:=renameProgram_counts (Equiv.swap (cLo L) L.one) (clearParityF L J)
  have c2:=renameProgram_counts (Equiv.swap (cHi L) L.sign)
    (renameProgram (Equiv.swap (cLo L) L.one) (clearParityF L J))
  simp only [programF,arithH,clearF,eraseScalarsAt,toffoliCount_append,measurementCount_append,
    p.1,p.2,w.1,w.2,i.1,i.2,e.1,e.2,c.1,c.2,c1.1,c1.2,c2.1,c2.2,(pre4_counts L).1,(pre4_counts L).2,
    (post4_counts L).1,(post4_counts L).2]
  all_goals simp

theorem jointF_counts (L : Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (jointF L J G)=774 ∧ measurementCount (jointF L J G)=517 := by
  have h:=programF_counts L hw J G
  simpa only [jointF,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

theorem programF_slots (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (programF L J B)≤7975 := by
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParityF_slots L hw J
  have er : gateSlots (eraseScalarsAt L J B)=11 := rfl
  have split : gateSlots (pre4 L)+gateSlots (inner L)+gateSlots (post4 L)=4369 := by
    rw [←arith,show arithmetic L=pre4 L++inner L++post4 L from add_split L hw]
    simp only [gateSlots_append]
  have loanS := loanF_slots L J B
  simp only [programF,arithH,clearF,gateSlots_append,rename_gateSlots,er,loanS,par]
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
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
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
  have r1 : rAt L 1∈retSites L J B := by
    apply r
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : 1<L.r.length := by rw [len.2.1];decide
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have split := pre4_post4_support L hw
  have clearS : wires (clearF L J)⊆retSites L J B :=
    swap2_support _ _ _ _ _ _ (clearParityF_support L J _ parts.2 (carryIn 248 (by decide)) (r _ rh))
      (carryIn 4 (by decide)) hd (carryIn 254 (by decide)) he
  have edgeS : ((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset⊆retSites L J B := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with h|rfl|rfl|rfl
    · rcases source1_sitesF L q h with rfl|rfl
      · exact hd
      · exact he
    · exact r1
    · exact carryIn 0 (by decide)
    · exact carryIn 1 (by decide)
  have es := loanF_edge_support L
  have loan : wires (loanF L J B)⊆retSites L J B := by
    simp only [loanF,loanW,wires_append,Finset.union_subset_iff]
    refine ⟨es.1.trans edgeS,⟨⟨?_,swap2_support _ _ _ _ _ _
      (swap_supportF _ _ _ _ (split.2.1.trans parts.1.1.2) (carryIn 248 (by decide)) (carryIn 1 (by decide)))
      (carryIn 4 (by decide)) hu (carryIn 254 (by decide)) he⟩,?_⟩,es.2.trans edgeS⟩
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
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (programF L J B) := by
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have hd := hosts_distinct L hw hn
  have nd7 := dist.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd7
  rcases nd7 with ⟨⟨sl,su,sj,sb,slo,shi⟩,⟨⟨lu,lj,lb,llo,lhi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
  have qr : q∉L.r := carry_not_r L hn q qc
  have qy : q∉L.y := fun h => y_not_carry L hn q h qc
  have flagNe (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q≠f := fun e => flagAway L hn f hf (by rw [←e];simp [qc])
  have qJ : q≠J := fun e => hJ (e ▸ data_member L q (by simp [qc]))
  have qB : q≠B := fun e => hB (e ▸ data_member L q (by simp [qc]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have qu : q≠lowY L := fun e => qy (e ▸ y0)
  have qlow (i : Nat) (hi : i<4) : q≠cAt L i := by
    rcases hq with rfl|rfl|rfl
    · exact carry_index_ne L hw hn 4 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 254 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 248 i (by decide) (by omega) (by omega)
  have qsite (h : q∈Affine.sites (sources L)) : False := by
    have m := sources_sites L q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
  have rmem (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    have len := BalancedCleanup.widths L.toLayout hw
    have lt : i<L.r.length := by rw [len.2.1];omega
    simp only [rAt,List.getD_eq_getElem _ _ lt]
    exact List.getElem_mem lt
  have edge (P : Program) (hP : wires P⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,
      lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset) : q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
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
  have c248lo : cAt L 248≠cLo L := carry_index_ne L hw hn 248 4 (by decide) (by decide) (by decide)
  have c248hi : cAt L 248≠cHi L := carry_index_ne L hw hn 248 254 (by decide) (by decide) (by decide)
  have clearFr : q∉wires (clearF L J) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityF L J)
        (clearParityF_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityF_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inl h)
    · exact swap2_free (cLo L) L.one (cHi L) L.sign (clearParityF L J)
        (clearParityF_free L hw hn J hJ L.one (Or.inl rfl))
        (clearParityF_free L hw hn J hJ L.sign (Or.inr (Or.inl rfl)))
        hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q (Or.inr h)
    · rw [h] at flagNe
      rw [h]
      exact swap_freeF _ _ _ _ (swap_freeF _ _ _ _
        (clearParityF_free L hw hn J hJ _ (Or.inr (Or.inr rfl))) c248lo (flagNe L.one (by simp)))
        c248hi (flagNe L.sign (by simp))
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
  have sc := scalarND L hn
  have uIn : lowY L∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
  have eIn : L.sign∉wires (inner L) := inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
  have m248 : cAt L 248∈L.carry := carry_mem L hw 248 (by decide)
  have m1 : cAt L 1∈L.carry := carry_mem L hw 1 (by decide)
  have uP : lowY L∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_freeF _ _ _ _ uIn (fun e => y_not_carry L hn _ y0 (e ▸ m248)) (fun e => y_not_carry L hn _ y0 (e ▸ m1))
  have eP : L.sign∉wires (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)) :=
    swap_freeF _ _ _ _ eIn (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m248))
      (fun e => flagAway L hn L.sign (by simp) (by rw [e];exact List.mem_append_right _ m1))
  have innerF : q∉wires (renameProgram (Equiv.swap (cHi L) L.sign)
      (renameProgram (Equiv.swap (cLo L) (lowY L))
        (renameProgram (Equiv.swap (cAt L 248) (cAt L 1)) (inner L)))) := by
    rcases hq with h|h|h
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inl h)
    · exact swap2_free (cLo L) (lowY L) (cHi L) L.sign _ uP eP hd.2.2.2.2.2.1 (Ne.symm slo) su q (Or.inr h)
    · rw [h] at flagNe qu
      rw [h]
      exact swap_freeF _ _ _ _ (swap_freeF _ _ _ _ (swap_free_leftF _ _ _ ((low_inner_freeF L hw hn).1 1 (by decide)))
        c248lo qu) c248hi (flagNe L.sign (by simp))
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
  have ls := loanF_edge_support L
  have edge1 (P : Program) (hP : wires P⊆((source L 1).wires++[rAt L 1,cAt L 0,cAt L 1]).toFinset) :
      q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with h|e|e|e
    · rcases source1_sitesF L q h with e|e
      · exact flagNe L.one (by simp) e
      · exact flagNe L.sign (by simp) e
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
  have loanFr : q∉wires (loanF L J B) := by
    simp only [loanF,loanW,wires_append,Finset.mem_union,not_or]
    exact ⟨edge1 _ ls.1,⟨⟨fun h => edgeF (edgeSub (Finset.mem_union_left _ h)),innerF⟩,
      fun h => edgeF (edgeSub (Finset.mem_union_right _ h))⟩,edge1 _ ls.2⟩
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
  exact ⟨⟨⟨prepF,⟨⟨edge _ es.1,loanFr⟩,edge _ es.2⟩⟩,eraseF⟩,clearFr⟩

theorem jointF_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L ∨ q=cAt L 248) : q∉wires (jointF L J G) := by
  have core := programF_free L hw hn J G hJ hG hJG q hq
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
    · exact carry_mem L hw 248 (by decide)
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
  have clear : GatePhysical (clearF L J) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ (clearParityF_physical L J parts.2))
  have e1 : GatePhysical (Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.2.2
    simp only [post4,gatePhysical_append] at h
    exact h.1.1.1.2
  have m1 : GatePhysical (Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)) := by
    have h := arith.1
    simp only [pre4,gatePhysical_append] at h
    exact h.1.1.2
  have loan : GatePhysical (loanF L J B) := by
    simp only [loanF,loanW,gatePhysical_append]
    refine ⟨e1,⟨⟨?_,gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ (Equiv.swap _ _).injective _ arith.2.1))⟩,?_⟩,m1⟩
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

/-- Carry #248 is virtual `760`, the retired pool wire. -/
theorem c248_eq : cAt portsJ 248=base 760 := by
  simp [cAt,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

/-- Record-length padding: 506 empty-correction erasures of the clean carry `base 512` (the
replaced first selector swap has 1 and the G1 half window 1022 records; the kernel has 517, one
of them the measured loan of carry #1 that retires virtual `760`). -/
def padding : Program := List.replicate 506 (Instr.measureX (base 512) [] [])

def padded : Program := kernel++padding

theorem padding_counts : toffoliCount padding=0 ∧ measurementCount padding=506 := by
  have h (n : Nat) : toffoliCount (List.replicate n (Instr.measureX (base 512) [] []))=0 ∧
      measurementCount (List.replicate n (Instr.measureX (base 512) [] []))=n := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      rw [List.replicate_succ]
      simp [toffoliCount,measurementCount,ih.1,ih.2,Nat.add_comm]
  exact h 506

theorem padded_counts : toffoliCount padded=774 ∧ measurementCount padded=1023 := by
  have j := jointF_counts portsJ portsJ_widths (base 1028) (base 1)
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032)) (jointF portsJ (base 1028) (base 1))
  have p := padding_counts
  simp only [padded,kernel,toffoliCount_append,measurementCount_append,r.1,r.2,j.1,j.2,p.1,p.2]
  all_goals simp

theorem padded_slots : gateSlots padded≤8484 := by
  have j := jointF_slots portsJ portsJ_widths (base 1028) (base 1)
  have p : gateSlots padding=506 := by
    have h (n : Nat) : gateSlots (List.replicate n (Instr.measureX (base 512) [] []))=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ,gateSlots_cons,ih]
        simp [instructionSlots]
        omega
    exact h 506
  simp only [padded,kernel,gateSlots_append,rename_gateSlots,p]
  omega

theorem padded_physical : GatePhysical padded := by
  have j := jointF_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  have p : GatePhysical padding := by
    intro i hi
    rw [padding,List.mem_replicate] at hi
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
  rw [cLo_eq,cHi_eq,c248_eq] at lo
  have keep (q : Wire) (hq : q∈wires (jointF portsJ (base 1028) (base 1))) : q∈kernelSites := by
    have m := List.mem_toFinset.mp (sup hq)
    have q1541 : q≠base 1541 := fun e => lo _ (Or.inr (Or.inl e)) hq
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
  · have e : q=base 512 := Finset.mem_singleton.mp (pad_wires (base 512) 506 hq)
    subst e
    have m : base 512∈wireBlock base 512 253 :=
      List.mem_map.mpr ⟨512,by simp [List.mem_range'_1],rfl⟩
    simp only [kernelSites,List.mem_toFinset,List.mem_append,portsJ_take254]
    exact Or.inl (Or.inr (Or.inl m))

theorem padded_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires padded := by
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
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
            | exact lo _ (Or.inr (Or.inl rfl)) ha
    · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
      rw [base_injective.eq_iff] at e
      omega

/-- Virtual wire `760` (carry #248, the retired pool wire) never occurs in the padded forward joint. -/
theorem padded_760_free : base 760∉wires padded := by
  have lo := jointF_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq,c248_eq] at lo
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
        exact lo _ (Or.inr (Or.inr rfl)) ha
  · have e := Finset.mem_singleton.mp (pad_wires (base 512) 506 used)
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
    rw [padded,run_append,k,padding]
    exact pad_run (base 512) 506 _ _ o512
  rw [shape]
  exact out

/-- Toffoli saving of the S1 (divide) first body: the 256-T first selector swap and the 765-T
comparator-free G1 half window become the 774-T padded forward joint (773 + the measured loan of
carry #1 that retires virtual `760`). -/
def saving (divide : Bool) : Nat := if divide then 247 else 0

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
