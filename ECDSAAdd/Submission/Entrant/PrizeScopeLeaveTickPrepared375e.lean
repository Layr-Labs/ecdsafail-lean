import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit IntegerHigh

set_option maxHeartbeats 1500000

theorem allSites (p : Ports) (far u : Wire) (inv : Bool) (ops : List Op) (sw : Nat→Wire)
    (layout : Layout 1560 sw tags 0 15) (apart : ∀i<15,sw i≠1559 ∧ sw i≠1560)
    (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (fa : far≠1559) (fb : far≠1560) (a : s.basis 1559=false) (b : s.basis 1560=false)
    (k : Mode) (mode : k=farMode (s.basis far) (s.basis u) small)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before p inv k q).read v)
    (exchanges : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k))
    :
    run (withHits far u inv sw (ops.map Op.enter)) m s=
      ⟨s.phase,fun q=>(sim ops (start p inv k) q).read v⟩ := by
  let fp := (flagOps far u inv).map Op.enter
  let hp := putAll 1560 sw tags 0 15
  let t := run fp m s
  let m' := m.drop (measurementCount fp)
  let r := run hp m' t
  let m'' := m'.drop (measurementCount hp)
  have init := initialized p inv far u s v m small fa fb a b (mode ▸ input)
  change t.phase=s.phase ∧ ∀q,t.basis q=(before p inv (farMode _ _ _) q).read v at init
  rw [←mode] at init
  have ex (on : right k=true) (i : Nat) (hi : i<15) (early : i≤key k) :
      t.basis (sw i)=decide (i=key k) := by
    obtain ⟨l,w⟩:=apart i hi
    dsimp only [t,fp]
    rw [flag_prepare _ _ _ _ _ fa fb a b]
    simpa [flagUpdate,l,w] using exchanges on i hi early
  have hh:=hits_ready p inv k sw layout t v m' init.2 ex
  have words := interpreted v ops (start p inv k)
  have bases : (fun q => (start p inv k q).read v)=r.basis := (funext hh.2).symm
  rw [bases] at words
  simp only [withHits,run_append,run_take]
  change run (ops.map Op.enter) m'' r=_
  rw [enter_run]
  exact congrArg₂ State.mk (hh.1.trans init.1) words.symm

end ECDSAAdd.Entrant.StairPacket.LeaveSelector


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem preparedState (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1721) (s.basis 1722) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPrefix inv) m s = ⟨s.phase,fun q=>(sim (if inv then prepareInv else prepare) (LeaveSelector.start ports inv k) q).read v⟩ := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact allSites ports 1721 1722 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange

theorem tagCertificate : ∀k:Mode, ∀i:Fin 16,
    sim prepare (LeaveSelector.start ports false k) (Leave225Join.tags.getD i 0) = .bit (enabled k && decide (i.val=key k)) := by decide +kernel

theorem selected (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1721) (s.basis 1722) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports false k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) (i:Fin 16) :
    (run (fullPrefix false) m s).basis (Leave225Join.tags.getD i 0)=
      (enabled k && decide (i.val=key k)) := by
  rw [preparedState false s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate k i)

end ECDSAAdd.Entrant.StairPacket.Leave225Selector


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem preparedState (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1713) (s.basis 1714) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPrefix inv) m s = ⟨s.phase,fun q=>(sim (if inv then prepareInv else prepare) (LeaveSelector.start ports inv k) q).read v⟩ := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact allSites ports 1713 1714 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange

theorem tagCertificate : ∀k:Mode, ∀i:Fin 16,
    sim prepare (LeaveSelector.start ports false k) (Leave240Join.tags.getD i 0) = .bit (enabled k && decide (i.val=key k)) := by decide +kernel

theorem selected (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1713) (s.basis 1714) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports false k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) (i:Fin 16) :
    (run (fullPrefix false) m s).basis (Leave240Join.tags.getD i 0)=
      (enabled k && decide (i.val=key k)) := by
  rw [preparedState false s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate k i)

end ECDSAAdd.Entrant.StairPacket.Leave240Selector


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem preparedState (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1706) (s.basis 1707) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPrefix inv) m s = ⟨s.phase,fun q=>(sim (if inv then prepareInv else prepare) (LeaveSelector.start ports inv k) q).read v⟩ := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact allSites ports 1706 1707 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange

theorem tagCertificate : ∀k:Mode, ∀i:Fin 16,
    sim prepare (LeaveSelector.start ports false k) (Leave255Join.tags.getD i 0) = .bit (enabled k && decide (i.val=key k)) := by decide +kernel

theorem selected (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1706) (s.basis 1707) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports false k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) (i:Fin 16) :
    (run (fullPrefix false) m s).basis (Leave255Join.tags.getD i 0)=
      (enabled k && decide (i.val=key k)) := by
  rw [preparedState false s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate k i)

end ECDSAAdd.Entrant.StairPacket.Leave255Selector


end
