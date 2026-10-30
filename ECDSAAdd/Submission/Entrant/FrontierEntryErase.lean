import ECDSAAdd.Submission.Entrant.FrontierEntryParity

/-! Phase-correct erasure for the retained-site entry scalars. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

theorem eraseXorAnd (p h d a : Wire) (hp : p≠a) (hh : h≠a) (hd : d≠a)
    (s : State) (m : List Bool)
    (ha : s.basis a=(s.basis p ^^ (s.basis p && s.basis h) ^^ s.basis d)) :
    run [.measureX a [] [.Z p,.CZ p h,.Z d]] m s=
      ⟨s.phase,writeBit s.basis a false⟩ := by
  cases hr : m.head?.getD false <;>
    simp [run,measureAndCorrect,correct,writeBit,hp,hh,hd,ha,hr,
      Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem fillZero (j p u : Wire) (s : State) (m : List Bool)
    (hu : s.basis u=false) :
    run [.CCX j p u] m s=⟨s.phase,writeBit s.basis u (s.basis j && s.basis p)⟩ := by
  simp [run,hu]

def eraseScalars (p a d e u j b h : Wire) : Program :=
  [.measureX e [] [.CZ a u],
   .measureX a [] [.Z p,.CZ p h,.Z d],
   .measureX d [] [.CZ p u],
   .measureX u [] [.CZ j b],
   .CCX j p u]

def erasedBasis (p a d e u j : Wire) (s : BasisState) : BasisState :=
  writeBit (writeBit (writeBit (writeBit s e false) a false) d false)
    u (s j && s p)

theorem erasedBasis_frame (p a d e u j : Wire) (s : BasisState) (q : Wire)
    (hq : q∉[a,d,e,u]) : erasedBasis p a d e u j s q=s q := by
  simp only [List.mem_cons,List.mem_singleton,not_or] at hq
  simp [erasedBasis,writeBit,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2]

theorem eraseScalars_counts (p a d e u j b h : Wire) :
    toffoliCount (eraseScalars p a d e u j b h)=1 ∧
      measurementCount (eraseScalars p a d e u j b h)=4 := by
  simp [eraseScalars,toffoliCount,measurementCount]

theorem eraseScalars_run (p a d e u j b h : Wire)
    (hn : [p,a,d,e,u,j,b,h].Nodup) (s : State) (m : List Bool)
    (he : s.basis e=(s.basis a && s.basis u))
    (ha : s.basis a=((s.basis p && s.basis h) ^^ s.basis p ^^ s.basis d))
    (hd : s.basis d=(s.basis p && s.basis u))
    (hu : s.basis u=(s.basis j && s.basis b)) :
    run (eraseScalars p a d e u j b h) m s=
      ⟨s.phase,erasedBasis p a d e u j s.basis⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨n01,n02,n03,n04,n05,n06,n07⟩,
    ⟨⟨n12,n13,n14,n15,n16,n17⟩,
    ⟨⟨n23,n24,n25,n26,n27⟩,
    ⟨⟨n34,n35,n36,n37⟩,
    ⟨⟨n45,n46,n47⟩,⟨⟨n56,n57⟩,n67⟩⟩⟩⟩⟩⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n40 := Ne.symm n04
  have n50 := Ne.symm n05
  have n60 := Ne.symm n06
  have n70 := Ne.symm n07
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n41 := Ne.symm n14
  have n51 := Ne.symm n15
  have n61 := Ne.symm n16
  have n71 := Ne.symm n17
  have n32 := Ne.symm n23
  have n42 := Ne.symm n24
  have n52 := Ne.symm n25
  have n62 := Ne.symm n26
  have n72 := Ne.symm n27
  have n43 := Ne.symm n34
  have n53 := Ne.symm n35
  have n63 := Ne.symm n36
  have n73 := Ne.symm n37
  have n54 := Ne.symm n45
  have n64 := Ne.symm n46
  have n74 := Ne.symm n47
  have n65 := Ne.symm n56
  have n75 := Ne.symm n57
  have n76 := Ne.symm n67
  have first := EntryHalf5.eraseAnd a u e n13 n43 s m he
  let s₁ : State := ⟨s.phase,writeBit s.basis e false⟩
  have second := eraseXorAnd p h d a n01 n71 n21 s₁ m.tail (by
    simpa [s₁,writeBit,n03,n73,n23,n13,Bool.xor_comm,Bool.xor_left_comm] using ha)
  let s₂ : State := ⟨s.phase,writeBit s₁.basis a false⟩
  have third := EntryHalf5.eraseAnd p u d n02 n42 s₂ m.tail.tail (by
    simpa [s₂,s₁,writeBit,n01,n03,n41,n43,n21,n23] using hd)
  let s₃ : State := ⟨s.phase,writeBit s₂.basis d false⟩
  have fourth := EntryHalf5.eraseAnd j b u n54 n64 s₃ m.tail.tail.tail (by
    simpa [s₃,s₂,s₁,writeBit,n52,n51,n53,n62,n61,n63,n42,n41,n43] using hu)
  let s₄ : State := ⟨s.phase,writeBit s₃.basis u false⟩
  have fill := fillZero j p u s₄ m.tail.tail.tail.tail (by simp [s₄,writeBit])
  change run [.measureX a [] [.Z p,.CZ p h,.Z d],
    .measureX d [] [.CZ p u],.measureX u [] [.CZ j b],.CCX j p u]
    m.tail (run [.measureX e [] [.CZ a u]] m s)=_
  rw [first]
  change run [.measureX d [] [.CZ p u],.measureX u [] [.CZ j b],.CCX j p u]
    m.tail.tail (run [.measureX a [] [.Z p,.CZ p h,.Z d]] m.tail s₁)=_
  rw [second]
  change run [.measureX u [] [.CZ j b],.CCX j p u]
    m.tail.tail.tail (run [.measureX d [] [.CZ p u]] m.tail.tail s₂)=_
  rw [third]
  change run [.CCX j p u] m.tail.tail.tail.tail
    (run [.measureX u [] [.CZ j b]] m.tail.tail.tail s₃)=_
  rw [fourth]
  change run [.CCX j p u] m.tail.tail.tail.tail s₄=_
  rw [fill]
  simp [s₄,s₃,s₂,s₁,erasedBasis,writeBit,n54,n52,n51,n53,n04,n02,n01,n03]

def eraseScalarsAt (L : Layout) (J B : Wire) : Program :=
  eraseScalars L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb

theorem erasePorts_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    [L.parity,L.lower,L.one,L.sign,L.ylow.getD 0 0,J,B,L.rmsb].Nodup := by
  have jnb : J≠B := by simpa using hJB
  have nd : (J::B::L.wires).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hJ,jnb],List.nodup_cons.mpr ⟨hB,hn⟩⟩
  cases hy : L.ylow with
  | nil => have h := hw.2.1;simp [hy] at h
  | cons y ys =>
    apply List.nodup_iff_count.mpr
    intro q
    have c := List.nodup_iff_count.mp nd q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,hy,List.getD_cons_zero,
      List.count_append,List.count_cons,List.count_nil] at c ⊢
    omega

theorem eraseScalarsAt_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (s : State) (m : List Bool)
    (he : s.basis L.sign=(s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (ha : s.basis L.lower=((s.basis L.parity && s.basis L.rmsb) ^^
      s.basis L.parity ^^ s.basis L.one))
    (hd : s.basis L.one=(s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hu : s.basis (L.ylow.getD 0 0)=(s.basis J && s.basis B)) :
    run (eraseScalarsAt L J B) m s=⟨s.phase,
      erasedBasis L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J s.basis⟩ :=
  eraseScalars_run _ _ _ _ _ _ _ _ (erasePorts_nodup L hw hn J B hJ hB hJB)
    s m he ha hd hu

theorem signedY_parity (U : Bool) (Y : Int) :
    originalParity (signedY U Y)=originalParity Y := by
  cases U
  · rfl
  · change decide ((-Y)%2≠0)=decide (Y%2≠0)
    apply decide_eq_decide.mpr
    omega

/-- The old sign product needs no retained old-sign bit. -/
theorem oldSign_product (U : Bool) (Y : Int) (hy : Centered Y) :
    (originalParity Y && negative Y)=
      ((originalParity Y && negative (halfResult (signedY U Y))) ^^ originalParity Y ^^
        (originalParity Y && U)) := by
  have ht := signedY_bounds U Y hy
  have hc := constants
  have hs := halfResult_sign (signedY U Y) (by unfold Centered at ht;omega)
  change negative (halfResult (signedY U Y))=
    (negative (signedY U Y) ^^ originalParity (signedY U Y)) at hs
  rw [signedY_parity] at hs
  by_cases hp : originalParity Y=false
  · simp [hp]
  · have hp : originalParity Y=true := by cases h : originalParity Y <;> simp_all
    have yn : Y≠0 := by
      intro e
      subst Y
      simp [originalParity] at hp
    have ns : negative (signedY U Y)=(negative Y ^^ U) := by
      cases U
      · simp [signedY]
      · by_cases h : Y<0
        · have pos : ¬0<Y := by omega
          simp [signedY,negative,h,pos]
        · have pos : 0<Y := by omega
          simp [signedY,negative,h,pos]
    rw [ns,hp] at hs
    cases U <;> cases hn : negative Y <;> simp_all

def clearParity (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++EntryHalf5.recoverParity L J

theorem clearParity_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (clearParity L J)=256 ∧ measurementCount (clearParity L J)=255 := by
  simpa only [clearParity,toffoliCount_append,measurementCount_append,toffoliCount,
    measurementCount,Nat.zero_add] using EntryHalf5.recoverParity_counts L hw J

theorem clearParity_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (Jv Bv : Bool) (Y : Int) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity=originalParity Y)
    (hU : s.basis (L.ylow.getD 0 0)=(Jv && originalParity Y))
    (hS : s.basis J=Jv) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  let R := halfResult (signedY (Jv && Bv) Y)
  let u : State := ⟨s.phase,writeBit s.basis L.parity
    (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity :=
    fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro eq
    simp [eq,List.count_cons] at nd
    omega
  have jp : J≠L.parity := fun e => hJ (by
    simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have same (q : Wire) (hq : q≠L.parity) : u.basis q=s.basis q := by
    simp [u,writeBit,hq]
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr L.r u.basis s.basis (fun q hq =>
      same q (away q (by simp [hq])))) hR
  have bounds := signedY_bounds (Jv && Bv) Y hy
  have constants := BalancedField.constants
  have rb : Centered R :=
    (halfResult_spec (signedY (Jv && Bv) Y) (by unfold Centered at bounds;omega)).1
  have predicate : decide (EntryHalf5.threshold<R.natAbs)=originalParity Y := by
    rw [←EntryHalf5.half_parity (signedY (Jv && Bv) Y) bounds,signedY_parity]
  have core := EntryHalf5.recoverParity_xor L hw hn J hJ Jv R rb u m ur
    ((same J jp).trans hS) ((same L.lower lp).trans hl)
    (fun q hq => (same q (away q (by simp [hq]))).trans (hc q hq))
  have zero : (u.basis L.parity ^^ ((!Jv) && decide (EntryHalf5.threshold<R.natAbs)))=false := by
    rw [predicate]
    simp only [u,writeBit,Function.update_self,hP,hU]
    cases Jv <;> simp
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := rfl
  rw [clearParity,run_append,show measurementCount [.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,
    List.take_zero,List.drop_zero,first,core,zero]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp [writeBit]
    · simp [u,writeBit,qp]

end ECDSAAdd.Entrant.EntryRetained5
