import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPrepared375e

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic

def refs : Expr → List Wire
  | .bit _ => []
  | .wire w => [w]
  | .both a b | .xor a b => refs a++refs b

theorem readAgree (e:Expr) (u v:BasisState) (agree:∀q∈refs e,u q=v q) : e.read u=e.read v := by
  induction e with
  | bit => rfl
  | wire w => exact agree _ (by simp [refs])
  | both a b ih jh =>
    exact congrArg₂ Bool.and (ih (fun q h=>agree q (List.mem_append_left _ h))) (jh (fun q h=>agree q (List.mem_append_right _ h)))
  | xor a b ih jh =>
    exact congrArg₂ Bool.xor (ih (fun q h=>agree q (List.mem_append_left _ h))) (jh (fun q h=>agree q (List.mem_append_right _ h)))

theorem simOutside (os:List Op) (v:Sym) (q:Nat) (off:q∉os.map Op.dst) : sim os v q=v q := by
  induction os generalizing v with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at off
    change sim os (symbolic o v) q=_
    rw [ih _ off.2]
    simp [symbolic,off.1]

theorem postOutside (p:Ports) (os:List Op) (k:Mode) (q:Nat)
    (free:q<1559 ∨ 1597<q) (off:q≠p.crossing → q≠p.near → q∉os.map Op.dst) :
    post p os false k q=.wire q := by
  by_cases flags : q=p.crossing ∨ q=p.near
  · simp [post,flags]
  · have both := not_or.mp flags
    have h0:q≠1559:=by omega
    have h1:q≠1560:=by omega
    have h2:¬(1561≤q ∧ q≤1575):=by omega
    have h3:¬(1576≤q ∧ q≤1597):=by omega
    simp [post,show q≠1597 by omega,simOutside _ _ _ (off both.1 both.2),start,h0,h1,h2,h3,both.1,both.2]

def cleared (v:BasisState) (q:Nat) := if 1559≤q ∧ q≤1597 then false else v q

theorem retiredBasis (p:Ports) (k:Mode) (v:BasisState)
    (far1:1597<p.crossing) (far2:1597<p.near) :
    clearKey (fun q=>(restored p false k q).read v)=cleared v := by
  funext q
  change Nat at q
  by_cases lo : 1559≤q ∧ q≤1575
  · simp [cleared,clearKey,lo,show 1559≤q ∧ q≤1597 by omega]
  by_cases hi : 1576≤q ∧ q≤1597
  · simp [cleared,clearKey,restored,start,hi,show 1559≤q ∧ q≤1597 by omega,
      show q≠1559 by omega,show q≠1560 by omega,show ¬(1561≤q ∧ q≤1575) by omega,
      (Nat.lt_of_le_of_lt hi.2 far1).ne,(Nat.lt_of_le_of_lt hi.2 far2).ne,Expr.read]
  · by_cases flags:q=p.crossing ∨ q=p.near
    · simp [cleared,clearKey,lo,restored,flags,show ¬(1559≤q ∧ q≤1597) by omega,Expr.read]
    · have both:=not_or.mp flags
      simp [cleared,clearKey,lo,restored,start,hi,show ¬(1559≤q ∧ q≤1597) by omega,
        show q≠1559 by omega,show q≠1560 by omega,show ¬(1561≤q ∧ q≤1575) by omega,both.1,both.2,Expr.read]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RetireActual
open Arithmetic LeaveSelector Leave225Selector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def paritySites := List.range' 241 15
def prior (k:Mode) := sim prepare (LeaveSelector.start ports false k)

theorem controls : ∀k:Mode,∀j:Fin 38,
    post ports prepare false k (1559+j.val)=prior k (1559+j.val) ∧
    ∀q∈refs (prior k (1559+j.val)),q∈paritySites := by decide +kernel
theorem signed : ∀k:Mode,∀q∈refs (signExpr ports k),q∈paritySites := by decide +kernel

theorem result (k:Mode) (v:BasisState) (s:State) (m:List Bool)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read v)
    (history:∀q∈paritySites,v q=s.basis q)
    (product:s.basis 1597=(s.basis 1724 && (signExpr ports k).read v))
    (l:left k=(s.basis 1721 && s.basis 1722)) (r:right k=(s.basis 1721 && !s.basis 1722))
    (exchange:right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPostfix false) m s=⟨s.phase,cleared s.basis⟩ := by
  have input (q:Nat) : s.basis q=(post ports prepare false k q).read s.basis := by
    by_cases mid : 1559≤q ∧ q<1597
    · let j:Fin 38:=⟨q-1559,by omega⟩
      have id:1559+j.val=q:=by dsimp [j];omega
      rw [←id,(controls k j).1]
      exact (bits j).trans (readAgree _ _ _ (fun a h=> history _ ((controls k j).2 _ h)))
    by_cases exactSite:q=1597
    · subst q
      have sign:=(readAgree (signExpr ports k) v s.basis (fun a h=>history _ (signed k _ h)))
      have form : post ports prepare false k 1597=conj (.wire 1724) (signExpr ports k) := rfl
      rw [form,read_conj,←sign];exact product
    · have outside:q<1559 ∨ 1597<q:=by omega
      have plain:post ports prepare false k q=.wire q := by
        apply postOutside _ _ _ _ outside
        intro cx nr member
        have cover:∀t∈prepare.map Op.dst,(1559≤t ∧ t≤1597) ∨ t=ports.crossing ∨ t=ports.near := by decide +kernel
        rcases cover q member with h|h|h
        · change 1559 ≤ q ∧ q ≤ 1597 at h;omega
        · exact cx h
        · exact nr h
      rw [plain];rfl
  rw [retiredFull false k s m s.basis input l r exchange,retiredBasis _ _ _ (by decide) (by decide)]

end ECDSAAdd.Entrant.StairPacket.Leave225RetireActual


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RetireActual
open Arithmetic LeaveSelector Leave240Selector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def paritySites := List.range' 256 15
def prior (k:Mode) := sim prepare (LeaveSelector.start ports false k)

theorem controls : ∀k:Mode,∀j:Fin 38,
    post ports prepare false k (1559+j.val)=prior k (1559+j.val) ∧
    ∀q∈refs (prior k (1559+j.val)),q∈paritySites := by decide +kernel
theorem signed : ∀k:Mode,∀q∈refs (signExpr ports k),q∈paritySites := by decide +kernel

theorem result (k:Mode) (v:BasisState) (s:State) (m:List Bool)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read v)
    (history:∀q∈paritySites,v q=s.basis q)
    (product:s.basis 1597=(s.basis 1716 && (signExpr ports k).read v))
    (l:left k=(s.basis 1713 && s.basis 1714)) (r:right k=(s.basis 1713 && !s.basis 1714))
    (exchange:right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPostfix false) m s=⟨s.phase,cleared s.basis⟩ := by
  have input (q:Nat) : s.basis q=(post ports prepare false k q).read s.basis := by
    by_cases mid : 1559≤q ∧ q<1597
    · let j:Fin 38:=⟨q-1559,by omega⟩
      have id:1559+j.val=q:=by dsimp [j];omega
      rw [←id,(controls k j).1]
      exact (bits j).trans (readAgree _ _ _ (fun a h=> history _ ((controls k j).2 _ h)))
    by_cases exactSite:q=1597
    · subst q
      have sign:=(readAgree (signExpr ports k) v s.basis (fun a h=>history _ (signed k _ h)))
      have form : post ports prepare false k 1597=conj (.wire 1716) (signExpr ports k) := rfl
      rw [form,read_conj,←sign];exact product
    · have outside:q<1559 ∨ 1597<q:=by omega
      have plain:post ports prepare false k q=.wire q := by
        apply postOutside _ _ _ _ outside
        intro cx nr member
        have cover:∀t∈prepare.map Op.dst,(1559≤t ∧ t≤1597) ∨ t=ports.crossing ∨ t=ports.near := by decide +kernel
        rcases cover q member with h|h|h
        · change 1559 ≤ q ∧ q ≤ 1597 at h;omega
        · exact cx h
        · exact nr h
      rw [plain];rfl
  rw [retiredFull false k s m s.basis input l r exchange,retiredBasis _ _ _ (by decide) (by decide)]

end ECDSAAdd.Entrant.StairPacket.Leave240RetireActual


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RetireActual
open Arithmetic LeaveSelector Leave255Selector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def paritySites := List.range' 271 15
def prior (k:Mode) := sim prepare (LeaveSelector.start ports false k)

theorem controls : ∀k:Mode,∀j:Fin 38,
    post ports prepare false k (1559+j.val)=prior k (1559+j.val) ∧
    ∀q∈refs (prior k (1559+j.val)),q∈paritySites := by decide +kernel
theorem signed : ∀k:Mode,∀q∈refs (signExpr ports k),q∈paritySites := by decide +kernel

theorem result (k:Mode) (v:BasisState) (s:State) (m:List Bool)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read v)
    (history:∀q∈paritySites,v q=s.basis q)
    (product:s.basis 1597=(s.basis 1709 && (signExpr ports k).read v))
    (l:left k=(s.basis 1706 && s.basis 1707)) (r:right k=(s.basis 1706 && !s.basis 1707))
    (exchange:right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPostfix false) m s=⟨s.phase,cleared s.basis⟩ := by
  have input (q:Nat) : s.basis q=(post ports prepare false k q).read s.basis := by
    by_cases mid : 1559≤q ∧ q<1597
    · let j:Fin 38:=⟨q-1559,by omega⟩
      have id:1559+j.val=q:=by dsimp [j];omega
      rw [←id,(controls k j).1]
      exact (bits j).trans (readAgree _ _ _ (fun a h=> history _ ((controls k j).2 _ h)))
    by_cases exactSite:q=1597
    · subst q
      have sign:=(readAgree (signExpr ports k) v s.basis (fun a h=>history _ (signed k _ h)))
      have form : post ports prepare false k 1597=conj (.wire 1709) (signExpr ports k) := rfl
      rw [form,read_conj,←sign];exact product
    · have outside:q<1559 ∨ 1597<q:=by omega
      have plain:post ports prepare false k q=.wire q := by
        apply postOutside _ _ _ _ outside
        intro cx nr member
        have cover:∀t∈prepare.map Op.dst,(1559≤t ∧ t≤1597) ∨ t=ports.crossing ∨ t=ports.near := by decide +kernel
        rcases cover q member with h|h|h
        · change 1559 ≤ q ∧ q ≤ 1597 at h;omega
        · exact cx h
        · exact nr h
      rw [plain];rfl
  rw [retiredFull false k s m s.basis input l r exchange,retiredBasis _ _ _ (by decide) (by decide)]

end ECDSAAdd.Entrant.StairPacket.Leave255RetireActual


end
