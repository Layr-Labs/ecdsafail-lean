import ECDSAAdd.Submission.Entrant.FrontierEntryPrefix
import ECDSAAdd.Submission.Entrant.FrontierEntryErase

/-! Final frame composition for the retained-site joint entry. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

/-- The copied low source bit and the copied high source bits reconstruct Y. -/
theorem encoded_parity_decomposition (Y : Int) (hy : Centered Y) :
    (originalParity Y).toNat + 2 * (encodeWord 256 Y / 2) = encodeWord 256 Y := by
  have hc := constants
  have signed := decode_encodeWord 256 (by decide) Y (by
    unfold Centered at hy
    norm_num only [Nat.reduceSub]
    omega)
  have low := signedDecode_mod_two 256 (encodeWord 256 Y) (by decide)
  rw [signed] at low
  have rem : encodeWord 256 Y % 2 = (originalParity Y).toNat := by
    have cast : ((encodeWord 256 Y % 2 : Nat) : Int) = Y % 2 := by
      simpa only [Int.natCast_emod, Nat.cast_ofNat] using low.symm
    cases hp : originalParity Y
    · have hz : Y % 2 = 0 := by simpa only [originalParity, decide_eq_false_iff_not,
        not_not] using hp
      simp only [hp, Bool.toNat_false]
      omega
    · have hz : Y % 2 ≠ 0 := by simpa only [originalParity, decide_eq_true_eq] using hp
      simp only [hp, Bool.toNat_true]
      omega
  have h := Nat.mod_add_div (encodeWord 256 Y) 2
  rwa [rem] at h

/-- This is the source value after deferred bit0 is filled. -/
theorem source_value_after_fill (J : Bool) (Y : Int) (hy : Centered Y) :
    (J && originalParity Y).toNat +
      2 * (if J then encodeWord 256 Y / 2 else 0) =
        encodeWord 256 (if J then Y else 0) := by
  cases J
  · simp [encodeWord]
  · simpa only [Bool.true_and, if_true] using encoded_parity_decomposition Y hy

/-- A numeric pending-source value determines the unchanged high source word. -/
theorem pending_source_high (L : Layout) (hw : L.Widths) (s : BasisState)
    (U : Bool) (high : Nat) (hU : s (L.ylow.getD 0 0) = U)
    (hvalue : regValue L.y s = U.toNat + 2*high) :
    regValue (L.ylow.drop 1 ++ [L.ymsb]) s = high := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    have low : s a = U := by simpa only [hy, List.getD_cons_zero] using hU
    simp only [BalancedCleanup.Layout.y, hy, List.cons_append] at hvalue
    change regValue (as ++ [L.ymsb]) s = high
    change (if s a then 1 else 0) + 2*regValue (as ++ [L.ymsb]) s = _ at hvalue
    rw [low] at hvalue
    cases U <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
      if_false, if_true] at hvalue <;> omega

/-- Final source reconstruction needs only its head and high-word values. -/
theorem source_frame_of_parts (L : Layout) (hw : L.Widths) (s : BasisState)
    (J : Bool) (Y : Int) (hy : Centered Y)
    (hlow : s (L.ylow.getD 0 0) = (J && originalParity Y))
    (hhigh : regValue (L.ylow.drop 1 ++ [L.ymsb]) s =
      if J then encodeWord 256 Y / 2 else 0) :
    regValue L.y s = encodeWord 256 (if J then Y else 0) := by
  cases hys : L.ylow with
  | nil => have h := hw.2.1; simp [hys] at h
  | cons a as =>
    have low : s a = (J && originalParity Y) := by
      simpa only [hys, List.getD_cons_zero] using hlow
    have high : regValue (as ++ [L.ymsb]) s =
        if J then encodeWord 256 Y / 2 else 0 := by
      simpa only [hys, List.drop_succ_cons, List.drop_zero] using hhigh
    simp only [BalancedCleanup.Layout.y, hys, List.cons_append]
    change (if s a then 1 else 0) + 2*regValue (as ++ [L.ymsb]) s = _
    rw [low, high]
    simpa only [Bool.toNat, Bool.cond_eq_ite] using source_value_after_fill J Y hy

/-- Read the new sign from the checked centered target value. -/
theorem target_sign_of_value (L : Layout) (hw : L.Widths) (R : Int)
    (hr : Centered R) (s : BasisState) (hR : regValue L.r s = encodeWord 256 R) :
    s L.rmsb = negative R := by
  have hc := constants
  have signed : signedRegValue L.r s = R := by
    unfold signedRegValue
    rw [(BalancedCleanup.widths L.toLayout hw).2.1, hR]
    apply decode_encodeWord 256 (by decide)
    unfold Centered at hr
    norm_num only [Nat.reduceSub]
    omega
  exact word_sign L.low L.rmsb s R signed

/-- The new sign supplies the measured old-sign-product correction. -/
theorem scalar_erase_relation (L : Layout) (hw : L.Widths)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : BasisState)
    (hR : regValue L.r s = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s L.parity = originalParity Y)
    (hA : s L.lower = (originalParity Y && negative Y))
    (hD : s L.one = (originalParity Y && (Jv && Bv))) :
    s L.lower = ((s L.parity && s L.rmsb) ^^ s L.parity ^^ s L.one) := by
  have bounds := signedY_bounds (Jv && Bv) Y hy
  have hc := constants
  have hr := (halfResult_spec (signedY (Jv && Bv) Y)
    (by unfold Centered at bounds; omega)).1
  have sign := target_sign_of_value L hw _ hr s hR
  rw [hA, hP, hD, sign]
  exact oldSign_product (Jv && Bv) Y hy

private theorem source_head_member (L : Layout) (hw : L.Widths) :
    L.ylow.getD 0 0 ∈ L.y := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as => simp [BalancedCleanup.Layout.y, hy]

private theorem source_head_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.ylow.getD 0 0 ∉ L.r ++ L.carry := by
  have nd : (L.r ++ (L.y ++ L.carry)).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (allND L hn)).2.1
  have rsep := (List.nodup_append'.mp nd).2.2
  have ysep := (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.2
  intro h
  rcases List.mem_append.mp h with hr | hc
  · exact List.disjoint_left.mp rsep hr (List.mem_append_left _ (source_head_member L hw))
  · exact List.disjoint_left.mp ysep (source_head_member L hw) hc

private theorem erased_data_keep (L : Layout) (hn : L.wires.Nodup)
    (J : Wire) (s : BasisState) (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
    (hu : q ≠ L.ylow.getD 0 0) :
    erasedBasis L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J s q = s q := by
  have away (v : Wire) (hv : v ∈ [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q ≠ v := fun e => flagAway L hn v hv (e ▸ hq)
  simp only [erasedBasis, writeBit, Function.update_of_ne hu,
    Function.update_of_ne (away L.one (by simp)),
    Function.update_of_ne (away L.lower (by simp)),
    Function.update_of_ne (away L.sign (by simp))]

/-- Compose the two checked measured cleanup blocks on abstract States. -/
theorem finish_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false) :
    run (eraseScalarsAt L J B ++ clearParity L J) m s =
      ⟨s.phase, writeBit (erasedBasis L.parity L.lower L.one L.sign
        (L.ylow.getD 0 0) J s.basis) L.parity false⟩ := by
  let t : State := ⟨s.phase, erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis⟩
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have ha := scalar_erase_relation L hw Jv Bv Y hy s.basis hR hP hA
    (by simpa only [hP,hU,hJv,hBv] using hD)
  have erase := eraseScalarsAt_run L hw hn J B hJ hB hJB s
    (m.take (measurementCount (eraseScalarsAt L J B))) hE ha hD hU
  have keep (q : Wire) (hq : q ∈ L.r ++ L.carry) : t.basis q = s.basis q := by
    apply erased_data_keep L hn J s.basis q
    · rcases List.mem_append.mp hq with hr | hc
      · exact List.mem_append_left _ (List.mem_append_left _ hr)
      · exact List.mem_append_right _ hc
    · exact fun e => source_head_away L hw hn (e ▸ hq)
  have tr : regValue L.r t.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (List.mem_append_left _ hq))).trans hR
  have tp : t.basis L.parity = originalParity Y := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne pU,
      Function.update_of_ne pD,Function.update_of_ne pA,Function.update_of_ne pE] using hP
  have tu : t.basis (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [t,erasedBasis,writeBit,Function.update_self,hJv,hP]
  have tj : t.basis J = Jv := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne (Ne.symm uJ),
      Function.update_of_ne (Ne.symm dJ),Function.update_of_ne (Ne.symm aJ),
      Function.update_of_ne (Ne.symm eJ)] using hJv
  have ta : t.basis L.lower = false := by
    simp only [t,erasedBasis,writeBit,Function.update_of_ne aU,
      Function.update_of_ne aD,Function.update_self]
  have tc (q : Wire) (hq : q ∈ L.carry) : t.basis q = false :=
    (keep q (List.mem_append_right _ hq)).trans (hc q hq)
  have parity := clearParity_run L hw hn J hJ Jv Bv Y hy t
    (m.drop (measurementCount (eraseScalarsAt L J B))) tr tp tu tj ta tc
  rw [run_append, erase]
  exact parity

private theorem source_high_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q ∈ L.ylow.drop 1 ++ [L.ymsb]) :
    q ∈ L.y ∧ q ≠ L.ylow.getD 0 0 := by
  have nd := (List.nodup_append'.mp (allND L hn)).2.1
  have ny : L.y.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    have tail : q ∈ as ++ [L.ymsb] := by simpa only [hy, List.drop_succ_cons, List.drop_zero] using hq
    have na : a ∉ as ++ [L.ymsb] := by
      have yn : (a :: (as ++ [L.ymsb])).Nodup := by
        simpa only [BalancedCleanup.Layout.y, hy, List.cons_append] using ny
      exact (List.nodup_cons.mp yn).1
    exact ⟨by simp [BalancedCleanup.Layout.y,hy,tail], by
      simpa only [hy,List.getD_cons_zero] using (fun e => na (e ▸ tail) : q ≠ a)⟩

/-- Close the two-word frame after the arithmetic prefix. Only its four live
scalar products are excluded from the prefix's outside-bit frame. -/
theorem finish_pair_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (before s : State) (m : List Bool)
    (phase : s.phase = before.phase)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hYS : regValue L.y s.basis = (Jv && Bv).toNat +
      2*(if Jv then encodeWord 256 Y / 2 else 0))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false)
    (clean : ∀ q ∈ [L.parity,L.lower,L.one,L.sign], before.basis q = false)
    (outside : ∀ q, q ∉ L.r → q ∉ L.y → q ≠ L.parity → q ≠ L.lower →
      q ≠ L.one → q ≠ L.sign → s.basis q = before.basis q) :
    let out := run (eraseScalarsAt L J B ++ clearParity L J) m s
    out.phase = before.phase ∧ PairFrame L.r L.y before.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let bits := writeBit (erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis) L.parity false
  have result := finish_run L hw hn J B hJ hB hJB Jv Bv Y hy s m hR hP hA hD hE hU hJv hBv hc
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have data_keep (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
      (hu : q ≠ L.ylow.getD 0 0) : bits q = s.basis q := by
    have qp : q ≠ L.parity := fun e => flagAway L hn _ (by simp) (e ▸ hq)
    simpa only [bits,writeBit,Function.update_of_ne qp] using erased_data_keep L hn J s.basis q hq hu
  have rkeep (q : Wire) (hq : q ∈ L.r) : bits q = s.basis q := by
    apply data_keep q (List.mem_append_left _ (List.mem_append_left _ hq))
    exact fun e => source_head_away L hw hn (e ▸ List.mem_append_left _ hq)
  have low : bits (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pU),
      Function.update_self,hJv,hP]
  have high : regValue (L.ylow.drop 1 ++ [L.ymsb]) bits =
      if Jv then encodeWord 256 Y / 2 else 0 := by
    have old := pending_source_high L hw s.basis (Jv && Bv)
      (if Jv then encodeWord 256 Y / 2 else 0) (by rw [hU,hJv,hBv]) hYS
    apply Eq.trans (regValue_congr _ _ _ ?_) old
    intro q hq
    have away := source_high_away L hw hn q hq
    exact data_keep q (List.mem_append_left _ (List.mem_append_right _ away.1)) away.2
  have source := source_frame_of_parts L hw bits Jv Y hy low high
  dsimp only
  rw [result]
  refine ⟨phase, (regValue_congr _ _ _ rkeep).trans hR, source, ?_⟩
  intro q hr hys
  change bits q = before.basis q
  by_cases qp : q = L.parity
  · subst q
    simp only [bits,writeBit,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qa : q = L.lower
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pA),
      Function.update_of_ne aU,Function.update_of_ne aD,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qd : q = L.one
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pD),
      Function.update_of_ne dU,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qe : q = L.sign
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pE),
      Function.update_of_ne eU,Function.update_of_ne (Ne.symm dE),
      Function.update_of_ne (Ne.symm aE),Function.update_self]
    exact (clean _ (by simp)).symm
  have qu : q ≠ L.ylow.getD 0 0 := fun e => hys (e ▸ source_head_member L hw)
  have same : bits q = s.basis q := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne qp,Function.update_of_ne qu,
      Function.update_of_ne qd,Function.update_of_ne qa,Function.update_of_ne qe]
  exact same.trans (outside q hr hys qp qa qd qe)

/-- Complete-State frame of the retained-site entry for every record tape. -/
theorem program_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y) (hY : regValue L.y s.basis = 0)
    (hclean : ∀ q ∈ BalancedCircuit.work L, s.basis q = false)
    (hSign : s.basis L.sign = false) (hJv : s.basis J = Jv) (hBv : s.basis B = Bv) :
    let out := run (program L J B) m s
    out.phase = s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let t := run (prefixProgram L J B) (m.take (measurementCount (prefixProgram L J B))) s
  have result := prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s
    (m.take (measurementCount (prefixProgram L J B))) hR hY hclean hSign hJv hBv
  change PrefixResult L J B Jv Bv Y s t at result
  have clean (q : Wire) (hq : q ∈ [L.parity,L.lower,L.one,L.sign]) : s.basis q = false := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hSign
  have d : t.basis L.one = (t.basis L.parity && t.basis (L.ylow.getD 0 0)) := by
    simpa only [result.parity,show t.basis (L.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.d
  have e : t.basis L.sign = (t.basis L.lower && t.basis (L.ylow.getD 0 0)) := by
    simpa only [result.a,show t.basis (L.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.e
  have u : t.basis (L.ylow.getD 0 0) = (t.basis J && t.basis B) := by
    rw [result.j,result.b]
    exact result.u
  have outside (q : Wire) (hr : q ∉ L.r) (hy : q ∉ L.y) (qp : q ≠ L.parity)
      (qa : q ≠ L.lower) (qd : q ≠ L.one) (qe : q ≠ L.sign) : t.basis q = s.basis q :=
    result.outside q (by simp [hr,hy,qp,qa,qd,qe])
  have finish := finish_pair_frame L hw hn J B hJ hB hJB Jv Bv Y hy s t
    (m.drop (measurementCount (prefixProgram L J B))) result.phase result.target result.source
    result.parity result.a d e u result.j result.b result.carry clean outside
  dsimp only
  rw [program,List.append_assoc,run_append]
  exact finish

end ECDSAAdd.Entrant.EntryRetained5
