import ECDSAAdd.Arithmetic.MappedCompressedControlledSpec
import ECDSAAdd.Arithmetic.SkywalkDirectPointLayout
import ECDSAAdd.Framework.WireRenamePool
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 ControlledPointLayout DirectSkywalk
attribute [local irreducible] run controlled

/-- Wiring and lease facts only; arithmetic correctness is supplied by
the already proved actual controlled circuit, never as a placement oracle. -/
structure PointArithmeticPlacement (L : ControlledPointLayout) (f : Wire → Wire) : Prop where
  injectiveOnSlots : ∀a∈slots.toFinset,∀b∈slots.toFinset,f a=f b → a=b
  divisorMap : (wireBlock base 770 256).map f=L.point.x
  numeratorMap : (wireBlock base 2056 256).map f=L.point.y
  controlMap : f (base 2400)=L.core.generic
  sharedWork : ∀q∈skywalkSharedWires base,q∈slots.toFinset →
    q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool
  selectorG : f (base 2409)∈L.dialogPool
  selectorS : f (base 2410)∈L.dialogPool
  zeroFlag : f (base 2411)∈L.dialogPool

def logicalInput (domain : Finset Wire) (f : Wire → Wire) (s : State) : State :=
  ⟨s.phase,fun q => if q∈domain then s.basis (f q) else false⟩

private theorem divisor_sites : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))
private theorem numerator_sites : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
private theorem control_site : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

private theorem reg_map_agree (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- Transfer the original strong point-arithmetic port contract to physical
wires, using only finite-support injectivity. Logical unused ghost sites are
completed with zero and never impose a condition on physical outsiders. -/
private theorem pointTransfer_core (L : ControlledPointLayout) (f : Wire → Wire)
    (domain : Finset Wire) (divide : Bool)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (zeroFlag : f (base 2411)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (bSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (B : Bool) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      (X=0 → t.basis (base 2400)=false) →
      t.basis (base 2411)=false → t.basis (base 2409)=false → t.basis (base 2410)=false →
      DirectSkywalkArithmeticStrong divide base (base 2400) X Y t (run P records t)) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let t := logicalInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,logicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [reg_map_agree f _ t.basis s.basis (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,logicalInput,if_neg used]
  have control : t.basis (base 2400)=B := by
    rw [inputBits _ bSite,controlMap,hb]
  have zeroBranch : X=0 → t.basis (base 2400)=false := by
    intro eq
    rw [control]
    cases B
    · rfl
    · exact False.elim ((hx0 rfl) eq)
  have strong := P_spec t m input zeroBranch
    (zero _ zeroFlag) (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective
    P programSites m t s rfl inputBits
  unfold DirectSkywalkArithmeticStrong at strong
  rw [control] at strong
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (reg_map_agree f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q outside
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have away : a∉skywalkArithmeticNumerator base := by
        intro mem
        apply outside
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2 a away).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P
        programSites m s q image



/-- Transfer the original strong point-arithmetic port contract to physical
wires, using only finite-support injectivity. Logical unused ghost sites are
completed with zero and never impose a condition on physical outsiders. -/
theorem pointTransfer_spec (L : ControlledPointLayout) (f : Wire → Wire)
    (placement : PointArithmeticPlacement L f) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hx : X<p) (hx0 : B=true → X≠0)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) :
    let out := run (renameProgram f (controlled divide)) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,selectorG,selectorS,zeroFlag⟩
  exact pointTransfer_core L f slots.toFinset divide injective divisorMap numeratorMap controlMap
    sharedWork selectorG selectorS zeroFlag divisor_sites numerator_sites control_site
    X Y B hx0 s m hb hX hY clean
    (controlled divide) (controlled_support divide)
    (fun t records input zeroBranch hflag hg hs =>
      controlled_spec divide hn hlo ho hf X Y hx t records input zeroBranch hflag hg hs)

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointTransfer_spec
