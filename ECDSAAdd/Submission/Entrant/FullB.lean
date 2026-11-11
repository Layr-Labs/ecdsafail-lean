import ECDSAAdd.Submission.Entrant.FullLogic
import ECDSAAdd.Submission.Entrant.MainPart04

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
open ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.WholePadConcrete

 def oldCachedBuild := buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry

 def newCachedBuild := buildCached (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry

 def oldCachedUnbuild := unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry

 def newCachedUnbuild := unbuildConsumed (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry

 theorem cached_build_counts : SeedPadDevelop.Counts newCachedBuild oldCachedBuild := by unfold SeedPadDevelop.Counts; decide +kernel

 theorem cached_unbuild_counts : SeedPadDevelop.Counts newCachedUnbuild oldCachedUnbuild := by unfold SeedPadDevelop.Counts; decide +kernel

end ECDSAAdd.Entrant.WholePadConcrete

namespace ECDSAAdd.Entrant.FullBMeta

 def MetricReady (L:CuccaroStreamedSquareWideLayout):Prop :=
 SeedPadDevelop.Counts
  (buildCached (accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry) ∧
 SeedPadDevelop.Counts
  (unbuildConsumed (accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
  (unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)

 instance (L:CuccaroStreamedSquareWideLayout):Decidable (MetricReady L):=by
  unfold MetricReady SeedPadDevelop.Counts
  infer_instance

 theorem actual_metric : MetricReady Baselines.layout.dialogStreamedSquareWide :=
  ⟨WholePadConcrete.cached_build_counts, WholePadConcrete.cached_unbuild_counts⟩

 def supportDomain (L:CuccaroStreamedSquareWideLayout):List Wire :=
  BThreeTemp.hostP L::BThreeTemp.hostR L::L.core.sumCarry::L.core.cin::(hiReg L++accReg L++FullPadDevelop.pad L++accBank L)

 def SupportReady (L:CuccaroStreamedSquareWideLayout) (c:Wire):Prop :=
  ∀w∈supportDomain L,hasWire (ParkCarry10Develop.body L c) w=true

 instance (L:CuccaroStreamedSquareWideLayout) (c:Wire):Decidable (SupportReady L c):=by
  unfold SupportReady
  infer_instance

 def L := Baselines.layout.dialogStreamedSquareWide

 def c := Baselines.layout.core.generic

 theorem used0 : ∀w∈((supportDomain L).drop 0).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used1 : ∀w∈((supportDomain L).drop 80).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used2 : ∀w∈((supportDomain L).drop 160).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used3 : ∀w∈((supportDomain L).drop 240).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used4 : ∀w∈((supportDomain L).drop 320).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used5 : ∀w∈((supportDomain L).drop 400).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem used6 : ∀w∈((supportDomain L).drop 480).take 80,hasWire (ParkCarry10Develop.body L c) w=true := by decide +kernel

 theorem domain_split : supportDomain L = ((supportDomain L).drop 0).take 80 ++ ((supportDomain L).drop 80).take 80 ++ ((supportDomain L).drop 160).take 80 ++ ((supportDomain L).drop 240).take 80 ++ ((supportDomain L).drop 320).take 80 ++ ((supportDomain L).drop 400).take 80 ++ ((supportDomain L).drop 480).take 80 := by decide +kernel

 theorem actual_support_ready : SupportReady L c := by
  unfold SupportReady
  rw [domain_split]
  simp only [List.mem_append,or_imp,forall_and]
  exact ⟨⟨⟨⟨⟨⟨used0, used1⟩, used2⟩, used3⟩, used4⟩, used5⟩, used6⟩

end ECDSAAdd.Entrant.FullBMeta

namespace ECDSAAdd.Entrant.FullBTemp

def hostR := BThreeTemp.hostR

def hostP := BThreeTemp.hostP

def pad (L : CuccaroStreamedSquareWideLayout) : List Wire := FullPadDevelop.pad L

def loans (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 (L.core.work.drop 173).take 19 ++ (L.core.work.drop 193).take 3 ++ (L.core.work.drop 255).take 1 ++ (L.core.work.drop 227).take 28 ++ (L.core.work.drop 201).take 11 ++ (L.core.work.drop 213).take 14 ++ (L.core.work.drop 212).take 1 ++ (L.core.work.drop 196).take 5

def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := hostR L::hostP L::loans L

def middle := BThreeTemp.middle

def LoanReadyTrim (L : CuccaroStreamedSquareWideLayout) (g u : Wire) : Prop :=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ True

def HostReady (L : CuccaroStreamedSquareWideLayout) (c x : Wire) : Prop :=
 LoanReadyTrim L c x ∧ x∉mR L ∧ x≠w192 L ∧ x≠c ∧ hasWire (ParkCarry10Develop.body L c) x=true

def PadReady (L:CuccaroStreamedSquareWideLayout) (c:Wire):Prop :=
 FullBMeta.MetricReady L ∧ FullFitReady.Ready L ∧ FullBMeta.SupportReady L c

def Ready (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Prop :=
 (loans L).length=82 ∧ (L.core.sumCarry::hosts L).Nodup ∧ (∀x∈hosts L,HostReady L c x) ∧ PadReady L c

instance (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Decidable (Ready L c) := by
 unfold Ready HostReady LoanReadyTrim PadReady
 unfold pad
 infer_instance

def oldLoop := BThreeTemp.oldLoop

theorem middle_subset_old (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (middle L c) ⊆ wires (ParkCarry10Develop.body L c) := by
 intro q member
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,wires_append,Finset.mem_union]
 exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl member)))))

theorem pad_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : 5≤(pad L).length := by
 rw [pad,FullPadDevelop.pad_length L hw]
 decide

 theorem terms_fits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (accReg L) (pad L) (accBank L) L.core.cin 163 f :=
 FullPadDevelop.terms_fits L hw hn

def prefixP (L : CuccaroStreamedSquareWideLayout) : Program :=
  measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++ eAddLo L)

def suffixP (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  ParkCarryDevelop.program (eU L) L.core.sumCarry ++
    (eSubK L ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L))

theorem oldBody_shape (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    ParkCarry10Develop.body L c = prefixP L ++ (oldLoop L c ++ suffixP L c) := by
  simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,oldLoop,BThreeTemp.oldLoop,middle,BThreeTemp.middle,prefixP,suffixP,List.append_assoc]

end ECDSAAdd.Entrant.FullBTemp

namespace ECDSAAdd.Entrant.FullBReady
open ECDSAAdd.Entrant.FullBTemp

def L := BThreeStaged301.L

def c := BThreeStaged301.c

theorem onePass_input_eq : BData301.p0=middle L c := BThreeStaged301.input_eq

theorem geometry : (loans L).length=82 ∧ (L.core.sumCarry::hosts L).Nodup ∧
 ∀x∈hosts L,LoanReadyTrim L c x ∧ x∉mR L ∧ x≠w192 L ∧ x≠c := by
 unfold LoanReadyTrim
 decide +kernel

theorem used_data : ∀x∈hosts L,FourthASavedCarryDevelop.hasWire BData301.p0 x=true := by decide +kernel

private theorem hasWire_transport (p q:Program) (e:p=q) (x:Wire)
 (h:FourthASavedCarryDevelop.hasWire p x=true):FourthASavedCarryDevelop.hasWire q x=true := e ▸ h

private theorem hasWire_middle_to_body (K:CuccaroStreamedSquareWideLayout) (g x:Wire)
 (h:FourthASavedCarryDevelop.hasWire (middle K g) x=true):
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body K g) x=true := by
 exact (FourthASavedCarryDevelop.hasWire_iff _ _).mpr
  (middle_subset_old K g ((FourthASavedCarryDevelop.hasWire_iff _ _).mp h))

private theorem used_to_body (x:Wire) (h:FourthASavedCarryDevelop.hasWire BData301.p0 x=true):
 FourthASavedCarryDevelop.hasWire (ParkCarry10Develop.body L c) x=true :=
 hasWire_middle_to_body L c x (hasWire_transport _ _ BThreeStaged301.input_eq x h)

theorem actual_ready : Ready L c := by
 refine ⟨geometry.1,geometry.2.1,?_,FullBMeta.actual_metric,FullFitReady.actual,FullBMeta.actual_support_ready⟩
 intro x hx
 have g:=geometry.2.2 x hx
 exact ⟨g.1,g.2.1,g.2.2.1,g.2.2.2,used_to_body x (used_data x hx)⟩

end ECDSAAdd.Entrant.FullBReady

namespace FastGuardResearch

def wideEq : DecidableEq CuccaroStreamedSquareWideLayout := by
 intro a b
 rcases a with ⟨ac,ap⟩
 rcases b with ⟨bc,bp⟩
 cases ac
 cases bc
 simp only [CuccaroStreamedSquareWideLayout.mk.injEq,CuccaroStreamedSquareLayout.mk.injEq]
 infer_instance

end FastGuardResearch

namespace ECDSAAdd.Entrant.FullBOptTemp

def actualLayout : CuccaroStreamedSquareWideLayout := Baselines.layout.dialogStreamedSquareWide

def actualControl : Wire := Baselines.layout.core.generic

def actualExt : List Wire := OwnDiagAll12Square.kext Baselines.layout

def actualFoldPerm : Equiv.Perm Wire := LowZero18Square.foldPerm actualLayout actualExt

def actualHostedLayout : CuccaroStreamedSquareWideLayout := ParkCarryDevelop.hostLayout actualLayout actualFoldPerm

theorem actualHostedLayout_eq : actualHostedLayout = actualLayout := by
 apply ParkCarryDevelop.host_eq
 have hw := Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths
 have nd : actualLayout.wires.Nodup := by
  change Baselines.layout.dialogStreamedSquareWide.wires.Nodup
  have full := Baselines.layout.streamedSquare_control_nodup Baselines.layout_widths Baselines.layout_nodup
  exact (List.nodup_cons.mp (List.nodup_cons.mp full).2).2
 have he := OwnDiagAll12Square.kext_ok Baselines.layout Baselines.layout_widths Baselines.layout_nodup
 exact ParkCarryDevelop.fold_fixes_sumCarry actualLayout hw nd actualExt he.len
  (fun q hq h => he.away q hq (List.mem_cons_of_mem actualControl h))

end ECDSAAdd.Entrant.FullBOptTemp
