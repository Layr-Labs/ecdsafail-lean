import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Arithmetic.Registers
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Arithmetic.Shift
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.ValueBodyPhysical
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeStair44PointMap486a9e3
import ECDSAAdd.Submission.Entrant.QTop

section

namespace ECDSAAdd.Entrant.HighBankFirstHit
open Arithmetic RecordedQuantum

def putHit (waiting swap hit : Wire) : Program := [.CCX waiting swap hit,.CX hit waiting]
def dropHit (waiting swap hit : Wire) : Program := [.CX hit waiting,.measureX hit [] [.CZ waiting swap]]

def putAll (w : Wire) (sw hit : Nat → Wire) (p : Nat) : Nat → Program
  | 0 => []
  | n+1 => putHit w (sw p) (hit p) ++ putAll w sw hit (p+1) n

def dropAll (w : Wire) (sw hit : Nat → Wire) (p : Nat) : Nat → Program
  | 0 => []
  | n+1 => dropAll w sw hit (p+1) n ++ dropHit w (sw p) (hit p)

structure Layout (w : Wire) (sw hit : Nat → Wire) (p n : Nat) : Prop where
  row : ∀ i : Nat, p ≤ i → i < p+n → [w,sw i,hit i].Nodup
  newHit : ∀ i : Nat, p ≤ i → i < p+n → ∀ j : Nat, i < j → j < p+n → hit j≠hit i ∧ sw j≠hit i

private theorem apart {w a h : Wire} (hn : [w,a,h].Nodup) : w≠a ∧ w≠h ∧ a≠h := by simpa [and_assoc] using hn

private theorem Layout.tail {w sw hit p n} (L : Layout w sw hit p (n+1)) :
    Layout w sw hit (p+1) n :=
  ⟨fun i a b => L.row i (by omega) (by omega),
   fun i a b j c d => L.newHit i (by omega) (by omega) j c (by omega)⟩

theorem counts (w : Wire) (sw hit : Nat → Wire) (p n : Nat) :
    toffoliCount (putAll w sw hit p n)=n ∧ measurementCount (putAll w sw hit p n)=0 ∧
    toffoliCount (dropAll w sw hit p n)=0 ∧ measurementCount (dropAll w sw hit p n)=n := by
  induction n generalizing p with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,b,c,d⟩ := ih (p+1)
    simp only [putAll,dropAll,toffoliCount_append,measurementCount_append,a,b,c,d]
    change 1+n=_ ∧ 0+0=_ ∧ 0+0=_ ∧ n+1=_
    omega

theorem put_run (w a h : Wire) (hn : [w,a,h].Nodup) (s : State) (m : List Bool)
    (hz : s.basis h=false) :
    let t := run (putHit w a h) m s
    t.phase=s.phase ∧ t.basis h=(s.basis w && s.basis a) ∧ t.basis w=(s.basis w && !s.basis a) ∧
    ∀ q,q≠w → q≠h → t.basis q=s.basis q := by
  obtain ⟨wa,wh,ah⟩ : w≠a ∧ w≠h ∧ a≠h := by simpa [and_assoc] using hn
  cases hw : s.basis w <;> cases ha : s.basis a <;>
    simp [putHit,run,writeBit,Function.update,hz,wh,Ne.symm wh,hw,ha] <;>
    intro q qw qh <;> simp [qw,qh]

theorem undo_hit (w a h : Wire) (hn : [w,a,h].Nodup) (s : State) (m f : List Bool)
    (hz : s.basis h=false) : run (dropHit w a h) m (run (putHit w a h) f s)=s := by
  obtain ⟨wa,wh,ah⟩ : w≠a ∧ w≠h ∧ a≠h := by simpa [and_assoc] using hn
  have first : run ([.CX h w] : Program) m (run (putHit w a h) f s)=
      ⟨s.phase,writeBit s.basis h (s.basis w && s.basis a)⟩ := by
    apply congrArg₂ State.mk rfl
    funext q
    by_cases qw : q=w <;> by_cases qh : q=h <;>
      simp_all [putHit,run,writeBit,Function.update,Ne.symm wh]
  change run ([.measureX h [] [.CZ w a]] : Program) m
      (run ([.CX h w] : Program) m (run (putHit w a h) f s))=s
  rw [first]
  simp only [run]
  cases hm : m.headD false <;> simp [measureAndCorrect,correct,writeBit,Function.update,wh,ah] <;> apply congrArg₂ State.mk rfl <;> simpa using hz

private theorem front (w : Wire) (sw hit : Nat → Wire) (p n : Nat) (s : State) (m : List Bool) :
    run (putAll w sw hit p (n+1)) m s=
      run (putAll w sw hit (p+1) n) m (run (putHit w (sw p) (hit p)) m s) := by
  rw [putAll,run_append,run_take]
  rfl

theorem undo_all {w sw hit p n} (L : Layout w sw hit p n) (s : State) (m f : List Bool)
    (clean : ∀ i : Nat, p ≤ i → i < p+n → s.basis (hit i)=false) :
    run (dropAll w sw hit p n) m (run (putAll w sw hit p n) f s)=s := by
  induction n generalizing s p m with
  | zero => rfl
  | succ n ih =>
    have row := L.row p (by omega) (by omega)
    have hz := clean p (by omega) (by omega)
    rw [front,dropAll,run_append,run_take]
    rw [ih L.tail _ _ (fun j lo hi => by
      have r := L.row j (by omega) (by omega)
      have wh : w≠hit j := by simp_all [List.nodup_cons]
      have dis := L.newHit p (by omega) (by omega) j (by omega) (by omega)
      exact ((put_run _ _ _ row s f hz).2.2.2 _ (Ne.symm wh) dis.1).trans (clean _ (by omega) (by omega)))]
    exact undo_hit _ _ _ row s _ f hz

theorem put_frame {w sw hit p n} (L : Layout w sw hit p n) (s : State) (m : List Bool)
    (clean : ∀ i : Nat, p ≤ i → i < p+n → s.basis (hit i)=false) :
    let out := run (putAll w sw hit p n) m s
    out.phase=s.phase ∧ ∀ q, q≠w → (∀ i : Nat, p ≤ i → i < p+n → q≠hit i) → out.basis q=s.basis q := by
  induction n generalizing p s with
  | zero => exact ⟨rfl,fun _ _ _ => rfl⟩
  | succ n ih =>
    dsimp only
    rw [front]
    obtain ⟨hp,_,_,same⟩ := put_run _ _ _ (L.row p (by omega) (by omega)) s m (clean _ (by omega) (by omega))
    obtain ⟨tp,ts⟩ := ih L.tail _ (fun j lo hi => by
      have nd := L.row j (by omega) (by omega)
      have nw : hit j≠w := Ne.symm (apart nd).2.1
      exact (same _ nw (L.newHit p (by omega) (by omega) j (by omega) (by omega)).1).trans
          (clean _ (by omega) (by omega)))
    exact ⟨tp.trans hp,fun q qw outside =>
      (ts q qw (fun i lo hi => outside i (by omega) (by omega))).trans
      (same q qw (outside _ (by omega) (by omega)))⟩

/-- t is the first exchange, or the end sentinel. Later swap bits are arbitrary.
Every hit site is set to its own comparison with t; waiting survives precisely
when no exchange in the half-open interval consumed it. -/
theorem one_hot {w sw hit p n} (L : Layout w sw hit p n) (s : State) (m : List Bool)
    (t : Nat) (waiting : s.basis w=decide (p ≤ t))
    (clean : ∀ i : Nat, p ≤ i → i < p+n → s.basis (hit i)=false)
    (raw : ∀ i : Nat, p ≤ i → i < p+n → i ≤ t → s.basis (sw i)=decide (i=t)) :
    let out := run (putAll w sw hit p n) m s
    out.basis w=decide (p+n ≤ t) ∧
      ∀ i : Nat, p ≤ i → i < p+n → out.basis (hit i)=decide (i=t) := by
  induction n generalizing p s with
  | zero => exact ⟨by simpa using waiting,fun i lo hi => by omega⟩
  | succ n ih =>
    dsimp only
    rw [front]
    let a := run (putHit w (sw p) (hit p)) m s
    have hr := L.row p (by omega) (by omega)
    obtain ⟨_,tag,flag,same⟩ := put_run _ _ _ hr s m (clean _ (by omega) (by omega))
    have hh : a.basis (hit p)=decide (p=t) ∧ a.basis w=decide (p+1 ≤ t) := by
      change _ = _ ∧ _ = _
      by_cases before : p ≤ t
      · have bit := raw p (by omega) (by omega) before
        by_cases eq : p=t
        · subst p; simp only [decide_true] at bit; simpa [a,waiting,bit] using And.intro tag flag
        · simpa [a,waiting,before,eq,bit,show p+1 ≤ t by omega] using And.intro tag flag
      · have eq : p≠t := by omega
        simpa [a,waiting,before,eq,show ¬p+1 ≤ t by omega] using And.intro tag flag
    have clean' (i : Nat) (lo : p+1 ≤ i) (hi : i < p+1+n) : a.basis (hit i)=false := by
      have nd := L.row i (by omega) (by omega)
      have nw : hit i≠w := Ne.symm (apart nd).2.1
      exact (same _ nw (L.newHit p (by omega) (by omega) i (by omega) (by omega)).1).trans
        (clean i (by omega) (by omega))
    obtain ⟨wEnd,hits⟩ := ih L.tail a hh.2 clean' (fun i lo hi small => by
      have nd := L.row i (by omega) (by omega)
      have nw : sw i≠w := Ne.symm (apart nd).1
      exact (same _ nw (L.newHit p (by omega) (by omega) i (by omega) (by omega)).2).trans
        (raw i (by omega) (by omega) small))
    refine ⟨by simpa [Nat.add_assoc,Nat.add_comm 1] using wEnd,fun i lo hi => ?_⟩
    by_cases eq : i=p
    · subst i
      have nw : hit p≠w := Ne.symm (apart hr).2.1
      exact ((put_frame L.tail a m clean').2 _ nw (fun j lj uj =>
        Ne.symm (L.newHit p (by omega) (by omega) j (by omega) (by omega)).1)).trans hh.1
    exact hits i (by omega) (by omega)

theorem inactive {w sw hit p n} (L : Layout w sw hit p n) (s : State) (m : List Bool)
    (off : s.basis w=false) (clean : ∀ i : Nat, p ≤ i → i < p+n → s.basis (hit i)=false) :
    run (putAll w sw hit p n) m s=s := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [front]
    obtain ⟨ph,tag,flag,same⟩ := put_run _ _ _ (L.row p (by omega) (by omega)) s m
      (clean p (by omega) (by omega))
    have eq : run (putHit w (sw p) (hit p)) m s=s := by
      apply congrArg₂ State.mk ph
      funext q
      change (run (putHit w (sw p) (hit p)) m s).basis q=s.basis q
      by_cases qw : q=w
      · subst q; simpa [off] using flag
      by_cases qh : q=hit p
      · subst q; simpa [off,clean p (by omega) (by omega)] using tag
      exact same q qw qh
    rw [eq]
    exact ih L.tail (fun i lo hi => clean i (by omega) (by omega))

theorem physical {w sw hit p n} (L : Layout w sw hit p n) :
    GatePhysical (putAll w sw hit p n) ∧ GatePhysical (dropAll w sw hit p n) := by
  induction n generalizing p with
  | zero => simp [putAll,dropAll,GatePhysical]
  | succ n ih =>
    obtain ⟨pf,pb⟩ := ih L.tail
    obtain ⟨wa,wh,ah⟩ := apart (L.row p (by omega) (by omega))
    simp only [putAll,dropAll,gatePhysical_append,pf,pb,and_true,true_and]
    simp_all [putHit,dropHit,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

end ECDSAAdd.Entrant.HighBankFirstHit

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic RecordedQuantum

def target (inverted:Bool) (enable:Option Wire) (a out:Wire) : Program :=
  match enable with
  | none => if inverted then [.CX a out,.X out] else [.CX a out]
  | some e => if inverted then [.CX e out,.CCX e a out] else [.CCX e a out]

def active (enable:Option Wire) (b:BasisState) := enable.elim true b

def chain (inverted:Bool) (enable:Option Wire) (out a:Wire) : List (Wire×Wire) → Program
  | []=>target inverted enable a out
  | (x,t)::rest=>[.CCX a x t]++chain inverted enable out t rest++[.measureX t [] [.CZ a x]]

def cut (a:Wire) (pairs:List (Wire×Wire)) (b:BasisState) :=
  b a && pairs.all (fun p=>b p.1)

def sites (pairs:List (Wire×Wire)) := pairs.flatMap (fun p=>[p.1,p.2])

theorem run_chain (inverted:Bool) (e:Option Wire) (out a:Wire) (pairs:List (Wire×Wire))
    (hn : (out::a::sites pairs).Nodup) (he:∀c∈e,c∉out::a::sites pairs)
    (m:List Bool) (s:State) (hc:∀p∈pairs,s.basis p.2=false) :
    run (chain inverted e out a pairs) m s=
    ⟨s.phase,writeBit s.basis out (s.basis out ^^ (active e s.basis && (inverted ^^ cut a pairs s.basis)))⟩ := by
  induction pairs generalizing a s m with
  | nil =>
    cases e with
    | none =>
      cases inverted <;> simp [chain,target,active,cut,run,writeBit]
    | some c =>
      have co:c≠out:=by have h:=he c (by simp); simp_all
      have ao:a≠out:=Ne.symm (by simpa [sites] using hn)
      cases inverted <;> cases sc:s.basis c <;> cases sa:s.basis a <;>
        simp [chain,target,active,cut,run,writeBit,Function.update,co,ao,sc,sa]
  | cons p rest ih =>
    obtain ⟨x,t⟩:=p
    change (out::a::x::t::sites rest).Nodup at hn
    obtain ⟨oA,oX,oT,oR,aX,aT,aR,xT,xR,tR,ns⟩ :
        out≠a ∧ out≠x ∧ out≠t ∧ out∉sites rest ∧ a≠x ∧ a≠t ∧ a∉sites rest ∧
          x≠t ∧ x∉sites rest ∧ t∉sites rest ∧ (sites rest).Nodup := by simpa [and_assoc] using hn
    have ht:s.basis t=false:=hc (x,t) (by simp)
    let v:State:=⟨s.phase,writeBit s.basis t (s.basis a && s.basis x)⟩
    have enter:run ([.CCX a x t]:Program) m s=v:= by simp [run,ht,v]
    have v_get (q:Wire) (hq:q≠t):v.basis q=s.basis q:=by simp [v,writeBit,hq]
    have vt:v.basis t=(s.basis a && s.basis x):=by simp [v,writeBit]
    have tailSites (p:Wire×Wire) (hp:p∈rest):p.1∈sites rest ∧ p.2∈sites rest := by
      constructor <;> exact List.mem_flatMap.mpr ⟨p,hp,by simp⟩
    have ec (c:Wire) (hc:c∈e) : c≠out ∧ c≠a ∧ c≠x ∧ c≠t ∧ c∉sites rest := by
      have h:=he c hc
      change c∉out::a::x::t::sites rest at h
      simpa [and_assoc] using h
    have next:=ih t (by simp [oT,oR,tR,ns]) (fun c h=>by
      obtain ⟨h0,_,_,h3,h4⟩:=ec c h; simp [h0,h3,h4]) m v (fun p hp=>by
      rw [v_get p.2 (fun h=>tR (h ▸ (tailSites _ hp).2))]
      exact hc p (by simp [hp]))
    have ve:active e v.basis=active e s.basis := by
      cases e with
      | none => rfl
      | some c => exact v_get c (ec c (by simp)).2.2.2.1
    have bits:rest.all (fun p=>v.basis p.1)=rest.all (fun p=>s.basis p.1):=by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h p hp
      · rw [←v_get p.1 (fun eq=>tR (eq ▸ (tailSites _ hp).1))]
        exact h p hp
      · rw [v_get p.1 (fun eq=>tR (eq ▸ (tailSites _ hp).1))]
        exact h p hp
    have answer:cut t rest v.basis=cut a ((x,t)::rest) s.basis:=by
      simp [cut,vt,bits,Bool.and_assoc]
    simp only [chain,run_append,run_take]
    rw [enter]
    change run ([.measureX t [] [.CZ a x]]:Program) _
      (run (chain inverted e out t rest) m v)=_
    rw [next,v_get out oT,ve,answer]
    generalize (s.basis out ^^ (active e s.basis && (inverted ^^ cut a ((x,t)::rest) s.basis)))=z
    simp only [run]
    generalize (List.drop _ m).headD false=measurementBit
    cases measurementBit <;> simp [v,correct,measureAndCorrect,writeBit,Function.update,oT.symm,
      oA.symm,oX.symm,aT,xT] <;>
      funext q <;> by_cases qt:q=t <;> by_cases qo:q=out <;>
        simp_all [Function.update,writeBit]
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalStatic

def good : Instr→Bool
  | .X _ => true
  | .CX c t => decide (c≠t)
  | .CCX a b t => decide (a≠t ∧ b≠t)
  | .measureX _ _ _ => false

theorem proper (p:Program) (h:p.all good=true):ProperProgram p:=by
  intro i hi
  have v:=List.all_eq_true.mp h i hi
  cases i <;> simp_all [good,ProperGate]

def inScan (neg:Wire) (i:Instr) := decide (∀q∈i.wires,q<1556 ∨ q=neg)

theorem separated (p:Program) (qs:List Wire) (neg:Wire) (h:p.all (inScan neg)=true)
    (g:∀q∈qs,1556≤q ∧ q≠neg) : ∀q∈qs,q∉wires p := by
  intro q hq
  have c:=g q hq
  induction p with
  | nil => simp [wires]
  | cons x p ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    simp only [wires,Finset.mem_union,not_or]
    have z:∀q∈x.wires,q<1556 ∨ q=neg:=of_decide_eq_true h.1
    exact ⟨fun member=>(z _ member).elim (fun l=>Nat.not_lt_of_ge c.1 l) c.2,ih h.2⟩
end ECDSAAdd.Entrant.StairPacket.PortalStatic

end

section

namespace ECDSAAdd.Entrant.StairPacket.RailPair
open Arithmetic

def sites (p : List (Wire×Wire)) := p.flatMap (fun t=>[t.1,t.2])
def exchange (c:Wire) (p : List (Wire×Wire)) := p.flatMap (fun t=>cswap c t.2 t.1)

private theorem inside {x : Wire×Wire} {p} (h:x∈p) : x.1∈sites p ∧ x.2∈sites p := by
  constructor
  · exact List.mem_flatMap.mpr ⟨x,h,by simp⟩
  · exact List.mem_flatMap.mpr ⟨x,h,by simp⟩

theorem exchange_run (c : Wire) (p : List (Wire×Wire)) (hn : (c::sites p).Nodup)
    (s : State) (m : List Bool) :
    (run (exchange c p) m s).phase=s.phase ∧
    (∀q,q∉sites p → (run (exchange c p) m s).basis q=s.basis q) ∧
    ∀t∈p, (run (exchange c p) m s).basis t.1=(if s.basis c then s.basis t.2 else s.basis t.1) ∧
          (run (exchange c p) m s).basis t.2=(if s.basis c then s.basis t.1 else s.basis t.2) := by
  induction p generalizing s m with
  | nil =>
    simp [exchange,sites,run]
  | cons pr rest ih =>
    obtain ⟨a,b⟩:=pr
    change (c::a::b::sites rest).Nodup at hn
    have p0:=List.nodup_cons.mp hn
    have p1:=List.nodup_cons.mp p0.2
    have p2:=List.nodup_cons.mp p1.2
    have split : c≠a ∧ c≠b ∧ c∉sites rest ∧ a≠b ∧ a∉sites rest ∧ b∉sites rest := by
      simpa [and_assoc] using And.intro p0.1 (And.intro p1.1 p2.1)
    obtain ⟨ca,cb,ct,ab,aa,bb⟩:=split
    have cw : [c,b,a].Nodup := by simp [ca,cb,ab.symm]
    let t:=run (cswap c b a) m s
    obtain ⟨ph,out,xb,xa⟩:=cswap_correct c b a cw s m
    have keep (q:Wire) (h:q∈sites rest):t.basis q=s.basis q := out q
      (fun e=>bb (e ▸ h)) (fun e=>aa (e ▸ h))
    have cc:t.basis c=s.basis c:=out _ cb ca
    obtain ⟨phase,save,active⟩:=ih (List.nodup_cons.mpr ⟨ct,p2.2⟩) t
      (m.drop (measurementCount (cswap c b a)))
    simp only [exchange,List.flatMap_cons,run_append,run_take]
    refine ⟨phase.trans ph,?_,?_⟩
    · intro q h
      change q∉a::b::sites rest at h
      simp only [List.mem_cons,not_or] at h
      exact (save _ h.2.2).trans (out _ h.2.1 h.1)
    · intro v hv
      rcases List.mem_cons.mp hv with rfl|tail
      · exact ⟨(save a aa).trans xa,(save b bb).trans xb⟩
      · obtain ⟨l,r⟩:=active _ tail
        obtain ⟨ql,qr⟩:=inside tail
        rw [cc,keep _ ql,keep _ qr] at l r
        exact ⟨l,r⟩

#print axioms exchange_run
end ECDSAAdd.Entrant.StairPacket.RailPair

end

section

namespace ECDSAAdd.Entrant.HighBankFirstHit
open Arithmetic

/-- Postcondition for retiring history tags, preserving the caller's updated
data bank, phase and all other unrelated state. -/
noncomputable def retireBasis (w : Wire) (hit : Nat → Wire) (n : Nat) (initial : Bool)
    (b : BasisState) (q : Wire) : Bool := by
  classical
  exact if q=w then initial else if ∃ i<n, q=hit i then false else b q

private theorem retire_hit {w sw hit n} (L : Layout w sw hit 0 n) (b : BasisState)
    (initial : Bool) (i : Nat) (hi : i<n) : retireBasis w hit n initial b (hit i)=false := by
  obtain ⟨_,wh,_⟩ : w≠sw i ∧ w≠hit i ∧ sw i≠hit i := by
    simpa [and_assoc] using L.row i (by omega) (by omega)
  simp [retireBasis,Ne.symm wh,show ∃ j<n, hit i=hit j from ⟨i,hi,rfl⟩]

theorem retire_selected {w sw hit n} (L : Layout w sw hit 0 n) (post : State) (m : List Bool)
    (source : ∀ i<n, ∀ j<n, sw i ≠ hit j) (t : Nat)
    (waiting : post.basis w=decide (n ≤ t))
    (tags : ∀ i<n, post.basis (hit i)=decide (i=t))
    (raw : ∀ i<n, i ≤ t → post.basis (sw i)=decide (i=t)) :
    run (dropAll w sw hit 0 n) m post=⟨post.phase,retireBasis w hit n true post.basis⟩ := by
  let before : State := ⟨post.phase,retireBasis w hit n true post.basis⟩
  have clean (i : Nat) (_ : 0 ≤ i) (hi : i<0+n) : before.basis (hit i)=false :=
    retire_hit L post.basis true i (by omega)
  have ready : before.basis w=decide (0 ≤ t) := by simp [before,retireBasis]
  have controls (i : Nat) (_ : 0 ≤ i) (hi : i<0+n) (it : i ≤ t) : before.basis (sw i)=decide (i=t) := by
    have row := L.row i (by omega) hi
    obtain ⟨wa,_,_⟩ : w≠sw i ∧ w≠hit i ∧ sw i≠hit i := by simpa [and_assoc] using row
    have aw := Ne.symm wa
    have outside : ¬∃ j<n, sw i=hit j := fun ⟨j,hj,eq⟩ => source i (by omega) j hj eq
    simpa [before,retireBasis,aw,outside] using raw i (by omega) it
  obtain ⟨flag,rec⟩ := one_hot L before [] t ready clean controls
  obtain ⟨ph,frame⟩ := put_frame L before [] clean
  have exactState : run (putAll w sw hit 0 n) [] before=post := by
    apply congrArg₂ State.mk ph
    funext q
    change (run (putAll w sw hit 0 n) [] before).basis q=post.basis q
    by_cases qw : q=w
    · subst q; simpa [waiting] using flag
    by_cases tag : ∃ i<n, q=hit i
    · obtain ⟨i,hi,eq⟩ := tag; subst q
      exact (rec i (by omega) (by omega)).trans (tags i hi).symm
    have h := frame q qw (fun i _ hi eq => tag ⟨i,by omega,eq⟩)
    simpa [before,retireBasis,qw,tag] using h
  have undone := undo_all L before m [] clean
  rw [exactState] at undone
  exact undone

theorem retire_inactive {w sw hit n} (L : Layout w sw hit 0 n) (post : State) (m : List Bool)
    (waiting : post.basis w=false) (tags : ∀ i<n, post.basis (hit i)=false) :
    run (dropAll w sw hit 0 n) m post=post := by
  have clean (i : Nat) (_ : 0 ≤ i) (hi : i<0+n) := tags i (by omega)
  have h := undo_all L post m [] clean
  rwa [inactive L post [] waiting clean] at h

end ECDSAAdd.Entrant.HighBankFirstHit

end

section

namespace ECDSAAdd.Entrant.StairPacket.RailPair
open Arithmetic

def transfer (inverse:Bool) (p:List (Wire×Wire)) : Program :=
  p.flatMap (fun ⟨a,b⟩=>if inverse then [.CX b a,.CX a b] else [.CX a b,.CX b a])

/-- The forward transfer clears a positive source after moving it onto
the already-cleared magnitude. The reverse transfer moves it back. -/
theorem transfer_run (inv:Bool) (p:List (Wire×Wire)) (hn:(sites p).Nodup)
    (m:List Bool) (s:State) (hc:∀w∈p,s.basis (if inv then w.1 else w.2)=false) :
    let t:=run (transfer inv p) m s
    t.phase=s.phase ∧ (∀q,q∉sites p → t.basis q=s.basis q) ∧
    ∀w∈p,t.basis w.1=s.basis w.2 ∧ t.basis w.2=s.basis w.1 := by
  induction p generalizing s m with
  | nil => simp [sites,transfer,run]
  | cons pr rest ih =>
    obtain ⟨a,b⟩:=pr
    change (a::b::sites rest).Nodup at hn
    have ⟨ab,ar,br,nt⟩:a≠b ∧ a∉sites rest ∧ b∉sites rest ∧ (sites rest).Nodup:=by simpa [and_assoc] using hn
    let v:State:=⟨s.phase,writeBit (writeBit s.basis a (s.basis b)) b (s.basis a)⟩
    have hv (q:Wire) (ha:q≠a) (hb:q≠b):v.basis q=s.basis q:=by simp [v,writeBit,ha,hb]
    have inside (x:Wire×Wire) (hx:x∈rest):x.1∈sites rest ∧ x.2∈sites rest:=by
      constructor <;> exact List.mem_flatMap.mpr ⟨x,hx,by simp⟩
    have vr (q:Wire) (hq:q∈sites rest):v.basis q=s.basis q:=hv q (fun eq=>ar (eq ▸ hq)) (fun eq=>br (eq ▸ hq))
    have head:=hc (a,b) (by simp)
    let first:Program:=if inv then [.CX b a,.CX a b] else [.CX a b,.CX b a]
    have action:run first m s=v:=by
      cases inv <;> simp only [Bool.false_eq_true,ite_false,ite_true] at head <;>
        simp [first,run,writeBit,Function.update,v,ab,ab.symm,head];
        funext q; by_cases q0:q=a <;> by_cases q1:q=b <;> simp_all [Function.update]
    have next:=ih nt (m.drop (measurementCount first)) v (fun w hw=>by
      rw [vr _ (by cases inv <;> simp [(inside w hw).1,(inside w hw).2])]
      exact hc w (List.mem_cons_of_mem _ hw))
    rw [show transfer inv ((a,b)::rest)=first++transfer inv rest from rfl]
    simp only [run_append,run_take,action]
    refine ⟨next.1,?_,?_⟩
    · intro q hq
      change q∉a::b::sites rest at hq
      simp only [List.mem_cons,not_or] at hq
      exact (next.2.1 q hq.2.2).trans (hv q hq.1 hq.2.1)
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|hr
      · exact ⟨(next.2.1 _ ar).trans (by simp [v,writeBit,ab]),(next.2.1 _ br).trans (by simp [v,writeBit])⟩
      · obtain ⟨x,y⟩:=next.2.2 w hr
        exact ⟨x.trans (vr _ (inside _ hr).2),y.trans (vr _ (inside _ hr).1)⟩
#print axioms transfer_run
end ECDSAAdd.Entrant.StairPacket.RailPair

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic
open List

def digits (a:Wire) (ps:List (Wire×Wire)) := a::ps.map Prod.fst
def latch (reverseOrder:Bool) (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire)) : Program :=
  let ds:=digits a ps
  notRegister ds ++ chain true e out a ps ++ notRegister (if reverseOrder then ds.reverse else ds)

private theorem items (ps:List (Wire×Wire)) : ps.map Prod.fst <+ sites ps ∧ ps.map Prod.snd <+ sites ps := by
  induction ps with
  | nil => exact ⟨.slnil,.slnil⟩
  | cons p rest ih =>
    change p.1 :: rest.map Prod.fst <+ p.1 :: p.2 :: sites rest ∧
      p.2 :: rest.map Prod.snd <+ p.1 :: p.2 :: sites rest
    exact ⟨(ih.1.cons _).cons₂ _,(ih.2.cons₂ _).cons _⟩

private theorem cross (ps:List (Wire×Wire)) (hn:(sites ps).Nodup) :
    ∀ p∈ps,p.2∉ps.map Prod.fst := by
  induction ps with
  | nil => simp
  | cons r rs ih =>
    change (r.1::r.2::sites rs).Nodup at hn
    have ⟨ab,ar,br,n⟩ : r.1≠r.2 ∧ r.1∉sites rs ∧ r.2∉sites rs ∧ (sites rs).Nodup := by simpa [and_assoc] using hn
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · simpa using And.intro ab.symm (fun h=>br ((items rs).1.subset h))
    · have hm:p.2∈sites rs := (items rs).2.subset (List.mem_map.mpr ⟨p,hp,rfl⟩)
      simpa using And.intro (fun (e:p.2=r.1)=>ar (e ▸ hm)) (ih n p hp)

theorem run_latch (rev:Bool) (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire))
    (hn:(out::a::sites ps).Nodup) (he:∀c∈e,c∉out::a::sites ps)
    (s:State) (m:List Bool) (clean:∀p∈ps,s.basis p.2=false) :
    run (latch rev e out a ps) m s=
      ⟨s.phase,writeBit s.basis out (s.basis out ^^ (active e s.basis && (digits a ps).any s.basis))⟩ := by
  have ds : digits a ps <+ a::sites ps := (items ps).1.cons₂ a
  have hp0:=List.nodup_cons.mp hn
  have ha:=List.nodup_cons.mp hp0.2
  have nd: (digits a ps).Nodup:=hp0.2.sublist ds
  have oo:out∉digits a ps:=fun h=>hp0.1 (ds.subset h)
  let b:BasisState:=fun q=>if q∈digits a ps then !s.basis q else s.basis q
  have tz (p:Wire×Wire) (hp:p∈ps) : b p.2=false := by
    have subset:p.2∈sites ps:=(items ps).2.subset (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have no:p.2∉digits a ps := by
      simpa [digits] using And.intro (fun (eq:p.2=a)=>ha.1 (eq ▸ subset)) (cross _ ha.2 p hp)
    simp [b,no,clean p hp]
  have ac:active e b=active e s.basis:=by
    cases e with
    | none => rfl
    | some v =>
      have h:v∉digits a ps:=fun mem=>he v (by simp) (List.mem_cons_of_mem _ (ds.subset mem))
      simp [active,b,h]
  have orCut:(!cut a ps b)=(digits a ps).any s.basis := by
    simp only [cut,digits,List.any_cons,Bool.not_and]
    have head : b a= !s.basis a:=by simp [b,digits]
    rw [head,Bool.not_not]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',List.all_eq_false,List.any_eq_true,List.mem_map]
    constructor
    · rintro ⟨p,hp,h⟩
      have inc:p.1∈digits a ps:=List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
      exact ⟨_,⟨p,hp,rfl⟩,by simpa [b,inc] using h⟩
    · rintro ⟨q,⟨p,hp,rfl⟩,h⟩
      have inc:p.1∈digits a ps:=List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
      exact ⟨p,hp,by simp [b,inc,h]⟩
  let v:State:=⟨s.phase,b⟩
  have middle:=run_chain true e out a ps hn he (m.drop (measurementCount (notRegister (digits a ps)))) v tz
  have ends:(if rev then (digits a ps).reverse else digits a ps).Nodup:=by cases rev <;> simp [nd]
  simp only [latch,run_append,run_take]
  rw [notRegister_correct _ nd]
  change run (notRegister _) _ (run (chain true e out a ps) _ v)=_
  rw [middle,notRegister_correct _ ends]
  apply congrArg (State.mk s.phase)
  funext q
  have ord : q∈(if rev then (digits a ps).reverse else digits a ps) ↔ q∈digits a ps := by cases rev <;> simp
  change (if q∈_ then !_ else _) = _
  rw [if_congr ord rfl rfl]
  have outVal : v.basis out=s.basis out := by simp [v,b,oo]
  simp only [Bool.true_xor,orCut,show v.basis=b by rfl,ac] at *
  by_cases qm:q∈digits a ps <;> by_cases qo:q=out <;>
    simp_all [v,b,writeBit,Function.update]
#print axioms run_latch
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket.RailPair
open Arithmetic

theorem flip_run (c:Wire) (xs:List Wire) (outside:c∉xs) (nd:xs.Nodup) (s:State) (m:List Bool) :
    run (signComplement c xs) m s=⟨s.phase,fun q=>if q∈xs then s.basis q ^^ s.basis c else s.basis q⟩ := by
  induction xs generalizing s m with
  | nil => simp [signComplement,run]
  | cons a r ih =>
    have ar: a∉r:=(List.nodup_cons.mp nd).1
    have ⟨ca,cr⟩:c≠a ∧ c∉r:=by simpa using outside
    let t:State:=⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis c)⟩
    change run (signComplement c r) m t=_
    rw [ih cr (List.nodup_cons.mp nd).2]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qa:q=a <;> by_cases qr:q∈r <;> simp_all [t,writeBit,Function.update]

def scan (aTop bTop g neg:Wire) (pairs:List (Wire×Wire)) : Program :=
  [.CX aTop neg,.CX bTop neg]++exchange g pairs++signComplement neg (pairs.map Prod.snd)

structure ScanGeometry (a b g neg:Wire) (p:List (Wire×Wire)) : Prop where
  unique : (neg::g::sites p).Nodup
  highs : (a,b)∈p
  right : (p.map Prod.snd).Nodup
  split : ∀v∈p,v.1∉p.map Prod.snd

theorem scan_run (a b g n:Wire) (p:List (Wire×Wire)) (loc:ScanGeometry a b g n p)
    (s:State) (m:List Bool) (clean:s.basis n=false) :
    let t:=run (scan a b g n p) m s
    let neg:=s.basis a ^^ s.basis b
    t.phase=s.phase ∧ t.basis n=neg ∧
    (∀q,q≠n → q∉sites p → t.basis q=s.basis q) ∧
    ∀v∈p,t.basis v.1=(if s.basis g then s.basis v.2 else s.basis v.1) ∧
      t.basis v.2=((if s.basis g then s.basis v.1 else s.basis v.2) ^^ neg) := by
  have ins (v:Wire×Wire) (h:v∈p):v.1∈sites p ∧ v.2∈sites p:=by constructor <;> exact List.mem_flatMap.mpr ⟨v,h,by simp⟩
  have right_sites (q:Wire) (hq:q∈p.map Prod.snd):q∈sites p:=by
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hq
    exact (ins _ hv).2
  obtain ⟨ng,ns,gp⟩ : n≠g ∧ n∉sites p ∧ (g::sites p).Nodup:=by
    have z:=List.nodup_cons.mp loc.unique
    simpa [and_assoc] using z
  have an:a≠n:=fun e=>ns (e ▸ (ins _ loc.highs).1)
  have bn:b≠n:=fun e=>ns (e ▸ (ins _ loc.highs).2)
  let flag:=s.basis a ^^ s.basis b
  let first:State:=⟨s.phase,writeBit s.basis n flag⟩
  have pre:run ([.CX a n,.CX b n]:Program) m s=first:=by
    simp [first,flag,run,writeBit,Function.update,bn,clean]
  have base (q:Wire) (h:q≠n):first.basis q=s.basis q:=by simp [first,writeBit,h]
  have fin (q:Wire) (h:q∈sites p):first.basis q=s.basis q:=base q (fun e=>ns (e ▸ h))
  let mid:=run (exchange g p) m first
  obtain ⟨ph,keep,xy⟩:=exchange_run g p gp first m
  have mn:mid.basis n=flag:=(keep n ns).trans (by simp [first,writeBit])
  have notR:n∉p.map Prod.snd:=fun h=>ns (right_sites _ h)
  have data (w:Wire×Wire) (hw:w∈p):mid.basis w.1=(if s.basis g then s.basis w.2 else s.basis w.1) ∧
      mid.basis w.2=(if s.basis g then s.basis w.1 else s.basis w.2):= by
    have h:=xy _ hw
    rw [base g ng.symm,fin _ (ins _ hw).1,fin _ (ins _ hw).2] at h
    exact h
  simp only [scan,run_append,run_take,pre]
  change _ ∧ _ ∧ _ ∧ _
  rw [show (run (exchange g p) (m.drop (measurementCount ([.CX a n,.CX b n]:Program))) first)=mid by rfl]
  rw [flip_run _ _ notR loc.right]
  refine ⟨ph,by simp [notR,mn,flag],?_,?_⟩
  · intro q qn hq
    have nr:q∉p.map Prod.snd:=fun h=>hq (right_sites _ h)
    simp only [if_neg nr]
    exact (keep _ hq).trans (base _ qn)
  · intro v hv
    have vr:v.2∈p.map Prod.snd:=List.mem_map.mpr ⟨v,hv,rfl⟩
    simp [loc.split v hv,vr,(data _ hv).1,(data _ hv).2,mn,flag]
#print axioms scan_run
end ECDSAAdd.Entrant.StairPacket.RailPair

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Hit
open Partial HighBankFirstHit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev swaps (i : Nat) := 1269+i
abbrev hits (i : Nat) := 1561+i

theorem sites : Layout 1560 swaps hits 0 15 := by
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by decide +kernel
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by decide +kernel
  exact ⟨fun i _ hi => rows ⟨i,hi⟩, fun i _ hi j lt hj => apart ⟨i,hi⟩ ⟨j,hj⟩ lt⟩

theorem written : ((leave225.drop 245).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retired : ((leave225Inv.drop 2917).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave225Hit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Hit
open Partial HighBankFirstHit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev swaps (i : Nat) := 1284+i
abbrev hits (i : Nat) := 1561+i

theorem sites : Layout 1560 swaps hits 0 15 := by
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by decide +kernel
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by decide +kernel
  exact ⟨fun i _ hi => rows ⟨i,hi⟩, fun i _ hi j lt hj => apart ⟨i,hi⟩ ⟨j,hj⟩ lt⟩

theorem written : ((leave240.drop 245).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retired : ((leave240Inv.drop 3115).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave240Hit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Hit
open Partial HighBankFirstHit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev swaps (i : Nat) := if i < 2 then 1299+i else 1814-i
abbrev hits (i : Nat) := 1561+i

theorem sites : Layout 1560 swaps hits 0 15 := by
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by decide +kernel
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by decide +kernel
  exact ⟨fun i _ hi => rows ⟨i,hi⟩, fun i _ hi j lt hj => apart ⟨i,hi⟩ ⟨j,hj⟩ lt⟩

theorem written : ((leave255.drop 245).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retired : ((leave255Inv.drop 3235).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave255Hit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(403, 1558), (404, 1559), (405, 1560), (406, 1561), (407, 1562), (408, 1563), (409, 1564), (410, 1565), (411, 1566), (412, 1567), (413, 1568), (414, 1569), (415, 1570), (416, 1571), (417, 1572), (418, 1573), (419, 1574), (420, 1575), (421, 1576), (422, 1577), (423, 1578), (424, 1579), (425, 1580), (426, 1581), (427, 1582), (428, 1583), (429, 1584), (430, 1585), (431, 1586), (432, 1587), (433, 1588), (434, 1589), (435, 1590), (436, 1591), (437, 1592), (438, 1593), (439, 1594), (440, 1595), (441, 1596), (442, 1597), (443, 1598), (444, 1599), (445, 1600), (446, 1601), (447, 1602), (448, 1603), (449, 1604), (450, 1605), (451, 1606), (452, 1607), (453, 1608), (454, 1609), (455, 1610), (456, 1611), (457, 1612), (458, 1613), (459, 1614), (460, 1615), (461, 1616), (462, 1617), (463, 1618), (464, 1619), (465, 1620), (466, 1621), (467, 1622), (468, 1623), (469, 1624), (470, 1625), (471, 1626), (472, 1627), (473, 1628), (474, 1629), (475, 1630), (476, 1631), (477, 1632), (478, 1633), (479, 1634), (480, 1635), (481, 1636), (482, 1637), (483, 1638), (484, 1639), (485, 1640), (486, 1641), (487, 1642), (488, 1643), (489, 1644), (490, 1645), (491, 1646), (492, 1647), (493, 1648), (494, 1649), (495, 1650), (496, 1651), (497, 1652)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by decide +kernel
theorem threshold_slice : ((Partial.portal225).drop 391).take 384=threshold := by decide +kernel
def orientationPairs : List (Wire×Wire) := [(947, 1556), (948, 1557), (949, 1558), (950, 1559), (951, 1560), (952, 1561), (953, 1562), (954, 1563), (955, 1564), (956, 1565), (957, 1566), (958, 1567), (959, 1568), (960, 1569), (961, 1570), (962, 1571), (963, 1572), (964, 1573), (965, 1574), (966, 1575), (967, 1576), (968, 1577), (969, 1578), (970, 1579), (971, 1580), (972, 1581), (973, 1582), (974, 1583), (975, 1584), (976, 1585), (977, 1586), (978, 1587), (979, 1588), (980, 1589), (981, 1590), (982, 1591), (983, 1592), (984, 1593), (985, 1594), (986, 1595), (987, 1596), (988, 1597), (989, 1598), (990, 1599), (991, 1600), (992, 1601), (993, 1602), (994, 1603), (995, 1604), (996, 1605), (997, 1606), (998, 1607), (999, 1608), (1000, 1609), (1001, 1610), (1002, 1611), (1003, 1612), (1004, 1613), (1005, 1614), (1006, 1615), (1007, 1616), (1008, 1617), (1009, 1618), (1010, 1619), (1011, 1620), (1012, 1621), (1013, 1622), (1014, 1623), (1015, 1624), (1016, 1625), (1017, 1626), (1018, 1627), (1019, 1628), (1020, 1629), (1021, 1630), (1022, 1631), (1023, 1632), (1024, 1633), (1025, 1634), (1026, 1635), (1027, 1636), (1028, 1637), (1029, 1638), (1030, 1639), (1031, 1640), (1032, 1641), (1033, 1642), (1034, 1643), (1035, 1644), (1036, 1645), (1037, 1646), (1038, 1647), (1039, 1648), (1040, 1649), (1041, 1650), (1042, 1651)]
def orientation := latch false (some 1721) 1722 946 orientationPairs
theorem orientation_layout : (1722::946::sites orientationPairs).Nodup := by decide +kernel
theorem orientation_slice : ((Partial.portal225).drop 778).take 388=orientation := by decide +kernel
theorem orientation_enable : 1721∉1722::946::sites orientationPairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(425, 1558), (426, 1559), (427, 1560), (428, 1561), (429, 1562), (430, 1563), (431, 1564), (432, 1565), (433, 1566), (434, 1567), (435, 1568), (436, 1569), (437, 1570), (438, 1571), (439, 1572), (440, 1573), (441, 1574), (442, 1575), (443, 1576), (444, 1577), (445, 1578), (446, 1579), (447, 1580), (448, 1581), (449, 1582), (450, 1583), (451, 1584), (452, 1585), (453, 1586), (454, 1587), (455, 1588), (456, 1589), (457, 1590), (458, 1591), (459, 1592), (460, 1593), (461, 1594), (462, 1595), (463, 1596), (464, 1597), (465, 1598), (466, 1599), (467, 1600), (468, 1601), (469, 1602), (470, 1603), (471, 1604), (472, 1605), (473, 1606), (474, 1607), (475, 1608), (476, 1609), (477, 1610), (478, 1611), (479, 1612), (480, 1613), (481, 1614), (482, 1615), (483, 1616), (484, 1617), (485, 1618), (486, 1619), (487, 1620), (488, 1621), (489, 1622), (490, 1623), (491, 1624), (492, 1625), (493, 1626), (494, 1627), (495, 1628), (496, 1629), (497, 1630), (498, 1631), (499, 1632), (500, 1633), (501, 1634), (502, 1635), (503, 1636), (504, 1637), (505, 1638), (506, 1639), (507, 1640), (508, 1641), (509, 1642), (510, 1643), (511, 1644), (512, 1645), (513, 1646), (514, 1647), (515, 1648), (516, 1649), (517, 1650), (518, 1651), (519, 1652), (520, 1653), (521, 1654), (522, 1655), (523, 1656), (524, 1657), (525, 1658), (526, 1659), (527, 1660), (528, 1661)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by decide +kernel
theorem threshold_slice : ((Partial.portal270).drop 427).take 420=threshold := by decide +kernel
def orientationPairs : List (Wire×Wire) := [(924, 1556), (925, 1557), (926, 1558), (927, 1559), (928, 1560), (929, 1561), (930, 1562), (931, 1563), (932, 1564), (933, 1565), (934, 1566), (935, 1567), (936, 1568), (937, 1569), (938, 1570), (939, 1571), (940, 1572), (941, 1573), (942, 1574), (943, 1575), (944, 1576), (945, 1577), (946, 1578), (947, 1579), (948, 1580), (949, 1581), (950, 1582), (951, 1583), (952, 1584), (953, 1585), (954, 1586), (955, 1587), (956, 1588), (957, 1589), (958, 1590), (959, 1591), (960, 1592), (961, 1593), (962, 1594), (963, 1595), (964, 1596), (965, 1597), (966, 1598), (967, 1599), (968, 1600), (969, 1601), (970, 1602), (971, 1603), (972, 1604), (973, 1605), (974, 1606), (975, 1607), (976, 1608), (977, 1609), (978, 1610), (979, 1611), (980, 1612), (981, 1613), (982, 1614), (983, 1615), (984, 1616), (985, 1617), (986, 1618), (987, 1619), (988, 1620), (989, 1621), (990, 1622), (991, 1623), (992, 1624), (993, 1625), (994, 1626), (995, 1627), (996, 1628), (997, 1629), (998, 1630), (999, 1631), (1000, 1632), (1001, 1633), (1002, 1634), (1003, 1635), (1004, 1636), (1005, 1637), (1006, 1638), (1007, 1639), (1008, 1640), (1009, 1641), (1010, 1642), (1011, 1643), (1012, 1644), (1013, 1645), (1014, 1646), (1015, 1647), (1016, 1648), (1017, 1649), (1018, 1650), (1019, 1651), (1020, 1652), (1021, 1653), (1022, 1654), (1023, 1655), (1024, 1656), (1025, 1657), (1026, 1658), (1027, 1659), (1028, 1660)]
def orientation := latch false (some 1698) 1699 923 orientationPairs
theorem orientation_layout : (1699::923::sites orientationPairs).Nodup := by decide +kernel
theorem orientation_slice : ((Partial.portal270).drop 850).take 424=orientation := by decide +kernel
theorem orientation_enable : 1698∉1699::923::sites orientationPairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic

def backward (e:Option Wire) (out a:Wire) : List (Wire×Wire) → Program
  | []=>(target true e a out).reverse
  | (x,t)::rest=>[.CCX a x t]++backward e out t rest++[.measureX t [] [.CZ a x]]

private theorem target_swap (e:Option Wire) (out a:Wire) (a0:a≠out)
    (e0:∀c∈e,c≠out) (m:List Bool) (s:State) :
    run ((target true e a out).reverse) m s=run (target true e a out) m s:=by
  cases e with
  | none =>
    cases v:s.basis a <;> cases w:s.basis out <;> simp [target,run,writeBit,Function.update,a0,v,w]
  | some c =>
    have ca:c≠out:=e0 c (by simp)
    cases v:s.basis a <;> cases w:s.basis out <;> cases k:s.basis c <;>
      simp [target,run,writeBit,Function.update,a0,ca,v,w,k]

theorem back_count (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire)):
    measurementCount (backward e out a ps)=measurementCount (chain true e out a ps):=by
  induction ps generalizing a with
  | nil => cases e <;> rfl
  | cons p rest ih =>
    cases p
    simp only [backward,chain,measurementCount_append,ih]

theorem back_is_chain (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire))
    (out0:out≠a) (outs:out∉sites ps) (en:∀c∈e,c≠out) (m:List Bool) (s:State) :
    run (backward e out a ps) m s=run (chain true e out a ps) m s:=by
  induction ps generalizing a m s with
  | nil => exact target_swap e out a out0.symm en m s
  | cons p rest ih =>
    obtain ⟨v,t⟩:=p
    change out∉v::t::sites rest at outs
    simp only [List.mem_cons,not_or] at outs
    simp only [backward,chain,run_append,run_take,measurementCount_append,back_count]
    rw [ih t outs.2.1 outs.2.2]

def backwardLatch (rev:Bool) (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire)) : Program :=
  let ds:=digits a ps
  notRegister (if rev then ds else ds.reverse) ++ backward e out a ps ++ notRegister ds.reverse

theorem backward_latch (rev:Bool) (e:Option Wire) (out a:Wire) (ps:List (Wire×Wire))
    (hn:(out::a::sites ps).Nodup) (he:∀c∈e,c∉out::a::sites ps)
    (s:State) (m:List Bool) (clean:∀p∈ps,s.basis p.2=false) :
    run (backwardLatch rev e out a ps) m s=
      ⟨s.phase,writeBit s.basis out (s.basis out ^^ (active e s.basis && (digits a ps).any s.basis))⟩ := by
  have hh:=run_latch true e out a ps hn he s m clean
  have ds:(digits a ps).Nodup := by
    have sub: (digits a ps).Sublist (a::sites ps):=by
      apply List.Sublist.cons₂
      clear hh clean he hn
      induction ps with
      | nil => exact .slnil
      | cons p r ih => exact (ih.cons _).cons₂ _
    exact (List.nodup_cons.mp hn).2.sublist sub
  have hnone:out≠a ∧ out∉sites ps:=by simpa using (List.nodup_cons.mp hn).1
  have en:∀c∈e,c≠out:=fun c h eq=>he c h (List.mem_cons.mpr (Or.inl eq))
  have swap (t:State) (tapeA tapeB:List Bool):run (notRegister (digits a ps).reverse) tapeA t=
      run (notRegister (digits a ps)) tapeB t:= by
    rw [notRegister_correct _ (by simpa using ds),notRegister_correct _ ds]
    simp only [List.mem_reverse]
  have quiet (xs:List Wire):measurementCount (notRegister xs)=0:=by
    induction xs with
    | nil => rfl
    | cons q r ih => exact ih
  cases rev <;> simp only [backwardLatch,latch,Bool.false_eq_true,ite_false,ite_true,run_append,run_take,
    measurementCount_append,quiet,Nat.zero_add,List.drop_zero,back_count] at hh ⊢
  · rw [back_is_chain _ _ _ _ hnone.1 hnone.2 en,swap s _ (List.take 0 (List.take (measurementCount (chain true e out a ps)) m)),run_take]
    exact hh
  · rw [back_is_chain _ _ _ _ hnone.1 hnone.2 en,run_take]
    exact hh
#print axioms backward_latch
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket.RailPair
open Arithmetic

def store (g n:Wire) (lo hi:List (Wire×Wire)):Program :=
  transfer false hi ++ signComplement n (lo.map Prod.snd) ++ exchange g lo

structure StoreGeometry (g n:Wire) (lo hi:List (Wire×Wire)) : Prop where
  lo_ok : (g::sites lo).Nodup
  hi_ok : (sites hi).Nodup
  ng : n≠g
  nh : n∉sites hi
  nl : n∉sites lo
  gh : g∉sites hi
  split : ∀ q∈sites lo,q∉sites hi
  rights : (lo.map Prod.snd).Nodup
  lr : ∀p∈lo,p.1∉lo.map Prod.snd

theorem store_run (g n:Wire) (lo hi:List (Wire×Wire)) (L:StoreGeometry g n lo hi)
    (s:State) (m:List Bool) (clear:∀p∈hi,s.basis p.2=false) :
    let t:=run (store g n lo hi) m s
    t.phase=s.phase ∧
    (∀q,q∉sites lo → q∉sites hi → t.basis q=s.basis q) ∧
    (∀p∈hi,t.basis p.1=false ∧ t.basis p.2=s.basis p.1) ∧
    (∀p∈lo,t.basis p.1=(if s.basis g then s.basis p.2 ^^ s.basis n else s.basis p.1) ∧
      t.basis p.2=(if s.basis g then s.basis p.1 else s.basis p.2 ^^ s.basis n)) := by
  have inside (p:Wire×Wire) (ps:List (Wire×Wire)) (h:p∈ps):p.1∈sites ps ∧ p.2∈sites ps:=by
    constructor <;> exact List.mem_flatMap.mpr ⟨p,h,by simp⟩
  have subR (q:Wire) (hq:q∈lo.map Prod.snd):q∈sites lo:=by
    obtain ⟨p,h,rfl⟩:=List.mem_map.mp hq;exact (inside _ _ h).2
  let u:=run (transfer false hi) m s
  have src:=transfer_run false hi L.hi_ok m s clear
  have up:u.phase=s.phase:=src.1
  have un:u.basis n=s.basis n:=src.2.1 _ L.nh
  have ug:u.basis g=s.basis g:=src.2.1 _ L.gh
  let v:=run (signComplement n (lo.map Prod.snd)) (m.drop (measurementCount (transfer false hi))) u
  have flip:v=⟨u.phase,fun q=>if q∈lo.map Prod.snd then u.basis q ^^ u.basis n else u.basis q⟩:=
    flip_run _ _ (fun h=>L.nl (subR _ h)) L.rights _ _
  have stay (q:Wire) (h:q∉sites lo):v.basis q=u.basis q:=by rw [flip];exact if_neg (fun hq=>h (subR _ hq))
  have gl:g∉sites lo:=(List.nodup_cons.mp L.lo_ok).1
  have vg:v.basis g=s.basis g:=(stay _ gl).trans ug
  have pair (p:Wire×Wire) (hp:p∈lo):v.basis p.1=s.basis p.1 ∧ v.basis p.2=(s.basis p.2 ^^ s.basis n):=by
    have r:p.2∈lo.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    have h:=inside _ _ hp
    rw [flip]
    simp [r,L.lr _ hp,src.2.1 _ (L.split _ h.1),src.2.1 _ (L.split _ h.2),un,u]
  let ms:=m.drop (measurementCount (transfer false hi ++ signComplement n (lo.map Prod.snd)))
  have final:=exchange_run g lo L.lo_ok v ms
  simp only [store,run_append,run_take]
  change (run _ ms v).phase=s.phase ∧ _ ∧ _ ∧ _
  refine ⟨final.1.trans ((congrArg State.phase flip).trans up),?_,?_,?_⟩
  · intro q l h
    exact ((final.2.1 q l).trans (stay q l)).trans (src.2.1 q h)
  · intro p hp
    have ⟨x,y⟩:=inside _ _ hp
    have no (q:Wire) (h:q∈sites hi):q∉sites lo:=fun ql=>L.split _ ql h
    have h:=src.2.2 _ hp
    exact ⟨((final.2.1 _ (no _ x)).trans (stay _ (no _ x))).trans (h.1.trans (clear _ hp)),
      ((final.2.1 _ (no _ y)).trans (stay _ (no _ y))).trans h.2⟩
  · intro p hp
    have h:=final.2.2 _ hp
    rw [vg,(pair _ hp).1,(pair _ hp).2] at h
    exact h
#print axioms store_run
end ECDSAAdd.Entrant.StairPacket.RailPair

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic RecordedQuantum

theorem measure_and (a b t:Wire) (s:State) (m:List Bool)
    (aa:a≠t) (bb:b≠t) (h:s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run]
  cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,aa,bb,h]

def threshold (a b t out:Wire) (rest:List (Wire×Wire)) : Program :=
  [.CCX a b t] ++ latch true none out t rest ++ [.measureX t [] [.CZ a b]]

theorem threshold_run (a b t out:Wire) (ps:List (Wire×Wire))
    (layout:(a::b::out::t::sites ps).Nodup) (s:State) (m:List Bool)
    (fresh:s.basis t=false) (clean:∀p∈ps,s.basis p.2=false) :
    run (threshold a b t out ps) m s = ⟨s.phase,writeBit s.basis out
      (s.basis out ^^ ((s.basis a && s.basis b) || (ps.map Prod.fst).any s.basis))⟩ := by
  obtain ⟨ab,ao,at0,_,bo,bt,_,ot,_,tr,_⟩ :
      a≠b ∧ a≠out ∧ a≠t ∧ a∉sites ps ∧ b≠out ∧ b≠t ∧ b∉sites ps ∧
      out≠t ∧ out∉sites ps ∧ t∉sites ps ∧ (sites ps).Nodup := by simpa [and_assoc] using layout
  have lay:(out::t::sites ps).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp layout).2).2
  let inside:State:=⟨s.phase,writeBit s.basis t (s.basis a && s.basis b)⟩
  have sc:run ([.CCX a b t]:Program) m s=inside:=by simp [run,inside,fresh]
  have atQ (q:Wire) (dif:q≠t):inside.basis q=s.basis q:=by simp [inside,writeBit,dif]
  have member (p:Wire×Wire) (mem:p∈ps):p.1∈sites ps ∧ p.2∈sites ps :=by
    constructor <;> exact List.mem_flatMap.mpr ⟨p,mem,by simp⟩
  have logic:=run_latch true none out t ps lay (by simp) inside m (fun p hp=>
    (atQ _ (fun same=>tr (same ▸ (member _ hp).2))).trans (clean _ hp))
  have any_cons : (digits t ps).any inside.basis=
      (s.basis a && s.basis b || (ps.map Prod.fst).any s.basis) :=by
    simp only [digits,List.any_cons]
    rw [show inside.basis t=(s.basis a && s.basis b) by simp [inside,writeBit]]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,List.mem_map]
    constructor <;> rintro ⟨q,⟨p,hp,rfl⟩,h⟩ <;> refine ⟨_,⟨p,hp,rfl⟩,?_⟩
    · rwa [atQ _ (fun same=>tr (same ▸ (member _ hp).1))] at h
    · rwa [atQ _ (fun same=>tr (same ▸ (member _ hp).1))]
  simp only [threshold,run_append,run_take,sc]
  change run ([.measureX t [] [.CZ a b]] : Program) _ (run (latch true none out t ps) m inside)=_
  rw [logic]
  simp only [active,Option.elim_none,Bool.true_and,any_cons,atQ _ ot]
  generalize (s.basis out ^^ (s.basis a && s.basis b || (ps.map Prod.fst).any s.basis))=z
  rw [measure_and (aa:=at0) (bb:=bt) (s:=⟨inside.phase,writeBit inside.basis out z⟩) (h:=by
    simp [inside,writeBit,ot.symm,ao,bo,at0,bt])]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases q0:q=t <;> by_cases q1:q=out <;> simp_all [inside,writeBit,Function.update]
#print axioms threshold_run
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem full (l:List Wire) (sign:Wire) (s:BasisState) (v:Int)
    (sv:signedRegValue (l++[sign]) s=v) :
    s sign=SkywalkRails.neg v ∧
    regValue (l++[sign]) (fun q=>s q ^^ s sign)=v.natAbs-(s sign).toNat := by
  refine ⟨(signedRegValue_sign _ _ _).trans (congrArg _ sv),?_⟩
  have val:=signedRegValue_msb l sign s
  rw [sv] at val
  have lim:=regValue_lt (l++[sign]) s
  simp only [List.length_append,List.length_singleton] at lim
  cases h:s sign with
  | false =>
    simp only [Bool.xor_false,Bool.toNat_false,Nat.sub_zero]
    rw [h] at val
    simp only [Bool.false_eq_true,ite_false,Int.sub_zero] at val
    rw [val,Int.natAbs_natCast]
  | true =>
    simp only [Bool.xor_true,Bool.toNat_true,regValue_complement,List.length_append,List.length_singleton]
    rw [h] at val
    simp only [ite_true] at val
    have neg:v<0:=by omega
    cases v with
    | ofNat k => omega
    | negSucc k =>
      change _=(k+1)-1
      change -((k: Int)+1)=(regValue (l++[sign]) s:Int)-((2^(l.length+1):Nat):Int) at val
      omega

theorem positive (l:List Wire) (sign:Wire) (s:BasisState) (v:Nat)
    (sv:signedRegValue (l++[sign]) s=v) : s sign=false ∧ regValue (l++[sign]) s=v := by
  obtain ⟨n,h⟩:=full l sign s _ sv
  have clear:s sign=false:=by simpa [SkywalkRails.neg] using n
  rw [clear] at h
  exact ⟨clear,by simpa using h⟩

theorem shiftedValue (r:List Wire) (k:Nat) (hk:k≤r.length) (s:BasisState) :
    regValue (r.drop k) s=regValue r s/2^k := by
  have split:=regValue_append (r.take k) (r.drop k) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at split
  have lo:regValue (r.take k) s<2^k:=by simpa only [List.length_take,Nat.min_eq_left hk] using regValue_lt (r.take k) s
  rw [split,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt lo,Nat.zero_add]

theorem paired (xs ys:List Wire) (a b:BasisState) (n:xs.length=ys.length)
    (hit:∀p∈xs.zip ys,a p.1=b p.2) : regValue xs a=regValue ys b := by
  induction xs generalizing ys with
  | nil => obtain rfl:ys=[]:=List.length_eq_zero_iff.mp n.symm; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at n
    | cons y ys =>
      have hxy:=hit (x,y) (by simp)
      have rest:=ih ys (by simpa using n) (fun p hp=>hit p (by simp [hp]))
      change (if a x then 1 else 0)+2*regValue xs a=(if b y then 1 else 0)+2*regValue ys b
      rw [rest]; change a x=b y at hxy;rw [hxy]
#print axioms full
#print axioms shiftedValue
end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.IntegerHigh
open SkywalkNat

def valueBits : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat + 2*valueBits bs

def lead : List Bool → Nat
  | [] => 0
  | false::bs => lead bs+1
  | true::_ => 0

theorem lead_le (bs : List Bool) : lead bs ≤ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [lead]; omega

theorem value_lt (bs : List Bool) : valueBits bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [valueBits,pow_succ] <;> omega

theorem all_ones (bs : List Bool) :
    bs.all id=true ↔ valueBits bs+1=2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [valueBits,pow_succ,ih] <;> omega

private theorem value_append (xs ys : List Bool) :
    valueBits (xs++ys)=valueBits xs+2^xs.length*valueBits ys := by
  induction xs with
  | nil => simp [valueBits]
  | cons b bs ih => simp only [List.cons_append,valueBits,List.length_cons,ih,pow_succ]; ring

private theorem low_positive (bs : List Bool) (n : Nat) (bound : lead bs < bs.length)
    (within : lead bs < n) : 0<valueBits (bs.take n) := by
  induction bs generalizing n with
  | nil => simp [lead] at bound
  | cons b bs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases b with
      | true => simp [valueBits]
      | false =>
        simp only [lead,List.length_cons] at bound within
        have := ih n (by omega) (by omega)
        simp [valueBits]; omega

/-- The branch taken by the suffix AND of the recorded parity bits. -/
def negative (bs : List Bool) := decide (0<lead bs) && (bs.drop (lead bs+lead bs)).all id

theorem selector (bs : List Bool) (nonempty : bs.length>0) :
    negative bs=true ↔ 2^bs.length < valueBits bs+2^(lead bs+lead bs) := by
  by_cases z : lead bs=0
  · simp [negative,z]; have := value_lt bs; omega
  let n := lead bs+lead bs
  have le := lead_le bs
  have nz : 0<lead bs := by omega
  have early : lead bs<n := by dsimp [n]; omega
  by_cases «over» : bs.length<n
  · have grow := Nat.pow_lt_pow_right (a:=2) (by decide : 1<2) «over»
    simp only [negative,decide_eq_true_eq.mpr nz,Bool.true_and]
    change (bs.drop n).all id=true ↔ _ < _+2^n
    rw [List.drop_eq_nil_of_le (Nat.le_of_lt «over»)]
    simp only [List.all_nil,true_iff]
    omega
  have hn : n≤bs.length := by omega
  let lo := bs.take n
  let hi := bs.drop n
  have ll : lo.length=n := by simp [lo,List.length_take,Nat.min_eq_left hn]
  have lh : hi.length=bs.length-n := by simp [hi]
  have split : valueBits bs=valueBits lo+2^n*valueBits hi := by
    have h := value_append lo hi
    simpa [lo,hi,ll,List.length_take,Nat.min_eq_left hn] using h
  have low := low_positive bs n (by omega) early
  have cap : valueBits lo<2^n := by simpa [ll] using value_lt lo
  have hcap := value_lt hi
  have exponent : 2^bs.length=2^n*2^hi.length := by rw [←pow_add]; congr 1; omega
  simp only [negative,decide_eq_true_eq.mpr nz,Bool.true_and]
  change hi.all id=true ↔ _ < _+2^n
  rw [all_ones,exponent,split]
  constructor
  · intro eq
    rw [←eq]; dsimp only [lo] at *; nlinarith
  · intro cmp
    by_contra! h
    have bound : valueBits hi+2 ≤ 2^hi.length := by omega
    have m := Nat.mul_le_mul_left (2^n) bound
    nlinarith

def oddBits (ls : List Nat) := ls.map (fun l => decide (l≠0))

theorem mask_bits (ls : List Nat) : valueBits (oddBits ls)=mask ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    by_cases z : l=0 <;> simp [oddBits,valueBits,mask,z,oddBits] at ih ⊢ <;> omega

theorem lead_wait (k B s : Nat) (ready : guard k s ≤ B) :
    lead (oddBits (letters k ⟨s,B⟩))=wait k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have hh : 2*guard k s+s ≤ B := by simpa [guard_succ] using ready
    have lo := guard_gt k s
    by_cases e : s%2=0
    · have st : step ⟨s,B⟩=⟨s/2,B⟩ := by
        by_cases z : s=0
        · subst s; rfl
        · simp [step,z,e]
      have gm := guard_mono k (a:=s/2) (b:=s) (by omega)
      have tail := ih (s/2) (by omega)
      simpa [letters,oddBits,letter,wait,e,st,lead] using congrArg Nat.succ tail
    · simp [letters,oddBits,letter,wait,e,show s<B by omega,lead]

theorem corrected_digit (k B s V : Nat) (hk : 0<k) (ready : guard k s ≤ B)
    (odd : B%2=1) (small : s<V) (low : 2*(2^k*V)≤B+s) (high : B+s<3*(2^k*V)) :
    let z : SkywalkNat.State := ⟨s,B⟩
    let out := step^[k] z
    let bits := oddBits (letters k z)
    let d := (out.u+out.v)/(2^(wait k s)*V)
    d = if d=2 then 2 else if negative bits then 1 else 3 := by
  dsimp only
  have len (n : Nat) (z : SkywalkNat.State) : (oddBits (letters n z)).length=n := by
    induction n generalizing z with
    | zero => rfl
    | succ n ih => simpa [oddBits,letters] using congrArg Nat.succ (ih (step z))
  have rule := selector (oddBits (letters k ⟨s,B⟩)) (by rwa [len])
  rw [len,mask_bits,lead_wait k B s ready] at rule
  obtain ⟨_,cross⟩ := right_digit k B s V ready odd small low high
  split
  next h => exact h
  next h =>
    specialize cross h
    split
    next neg => simpa only [if_pos (rule.mp neg)] using cross
    next pos => simpa only [if_neg (fun h => pos (rule.mpr h))] using cross

end ECDSAAdd.Entrant.IntegerHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalCut

/-- In far mode, the OR of the upper magnitude bits identifies the long
coordinate, including the negative representation M = u−1. -/
theorem orientation (b U u v e : Nat) (unit : 2*b≤U) (positive:0<b)
    (small:min u v<b) (en:e≤1) :
    (3*U≤u+v ∧ U≤u-e) ↔ (3*U≤u+v ∧ b≤u) := by
  omega

/-- The external portal computes this carry directly at the top retained bit
and thereby erases the duplicate magnitude bank on both sides of the guard. -/
theorem clear_value (b U u v e : Nat) (unit:2*b≤U) (positive:0<b)
    (small:min u v<b) (en:e≤1) (eu:e≤u) :
    let M:=u-e
    let X:=u+v
    let w:=if 4*U≤M%(8*U) ∧ X%(8*U)<4*U then 1 else 0
    M/(8*U)+w=if 3*U≤X ∧ b≤u then X/(8*U) else 0 := by
  dsimp only
  by_cases h:3*U≤u+v ∧ b≤u
  · rw [if_pos h]
    have g:v+e≤4*U:=by omega
    have z:=half_limb_borrow (4*U) (u-e) (v+e) (by omega) g
    rw [show u-e+(v+e)=u+v by omega,show 2*(4*U)=8*U by omega] at z
    exact z.symm
  · rw [if_neg h]
    have lo:u-e<4*U:=by omega
    rw [Nat.mod_eq_of_lt (show u-e<8*U by omega),Nat.div_eq_of_lt (show u-e<8*U by omega)]
    simp [show ¬ 4*U≤u-e by omega]

#print axioms orientation
#print axioms clear_value
end ECDSAAdd.Entrant.StairPacket.PortalCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic

def flags (a b low temp far long mag : Wire) (as bs : List (Wire×Wire)) : Program :=
  threshold a b low temp as ++ [.CX temp far,.CX far temp] ++ latch false (some far) long mag bs

def high (a b:Wire) (as:List (Wire×Wire)) (s:BasisState) :=
  (s a && s b) || (as.map Prod.fst).any s

theorem flags_run (a b low temp far long mag : Wire) (as bs : List (Wire×Wire))
    (lA:(a::b::temp::low::sites as).Nodup)
    (lB:(far::long::mag::sites bs).Nodup) (ft:far≠temp)
    (s:State) (m:List Bool) (hf:s.basis far=false) (ht:s.basis temp=false)
    (hl:s.basis low=false) (hj:s.basis long=false)
    (ca:∀p∈as,s.basis p.2=false) (cb:∀p∈bs,s.basis p.2=false) :
    let f:=high a b as s.basis
    let u:=f && (digits mag bs).any s.basis
    run (flags a b low temp far long mag as bs) m s=
      ⟨s.phase,writeBit (writeBit s.basis far f) long u⟩ := by
  let f:=high a b as s.basis
  let v:State:=⟨s.phase,writeBit s.basis far f⟩
  have first:=threshold_run a b low temp as lA s m hl ca
  rw [ht,Bool.false_xor] at first
  have copy (m':List Bool) : run [.CX temp far,.CX far temp] m'
      ⟨s.phase,writeBit s.basis temp f⟩=v:= by
    simp [run,writeBit,Function.update,v,ft,ft.symm,hf]
    funext q
    by_cases qt:q=temp <;> by_cases qf:q=far <;> simp_all [Function.update]
  obtain ⟨fl,fm,fr,n⟩ : far≠long ∧ far≠mag ∧ far∉sites bs ∧ (long::mag::sites bs).Nodup := by
    have c:=List.nodup_cons.mp lB
    simpa [and_assoc] using c
  have fresh (p:Wire×Wire) (hp:p∈bs): v.basis p.2=false:=by
    have inside:p.2∈sites bs:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
    have eq:p.2≠far:=fun e=>fr (e ▸ inside)
    simp [v,writeBit,eq,cb p hp]
  have away (q:Wire) (hq:q∈digits mag bs):q≠far:=by
    intro eq; subst q
    rcases List.mem_cons.mp hq with h|h
    · exact fm h
    · obtain ⟨p,hp,h⟩:=List.mem_map.mp h
      exact fr (h ▸ List.mem_flatMap.mpr ⟨p,hp,by simp⟩)
  have anyEq:(digits mag bs).any v.basis=(digits mag bs).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,hq,h⟩ <;> exact ⟨q,hq,by simpa [v,writeBit,away q hq] using h⟩
  simp only [flags,run_append,run_take,first]
  change run (latch false (some far) long mag bs) _ (run [.CX temp far,.CX far temp] _ ⟨s.phase,writeBit s.basis temp f⟩)=_
  rw [copy,run_latch _ _ _ _ _ n (by intro c h; obtain rfl:=Option.mem_some_iff.mp h;exact (List.nodup_cons.mp lB).1) _ _ fresh]
  rw [anyEq]
  simp [active,v,writeBit,fl.symm,hj,f]
#print axioms flags_run
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic RailPair

structure PackedCut (lo hi:List (Wire×Wire)) (g n f u:Wire) (neg far long:Bool) (origin result:State) : Prop where
  phase : result.phase=origin.phase
  sign : result.basis n=neg
  mode : result.basis f=far
  orientation : result.basis u=long
  low : ∀p∈lo,result.basis p.1=origin.basis p.1 ∧ result.basis p.2=origin.basis p.2
  upper : ∀p∈hi,result.basis p.1=false ∧
    result.basis p.2=(if origin.basis g then origin.basis p.2 else origin.basis p.1)
  frame : ∀q,q≠n→q≠f→q≠u→q∉sites lo→q∉sites hi→ result.basis q=origin.basis q

structure CutLayout (lo hi:List (Wire×Wire)) (g n f u:Wire) : Prop where
  store : StoreGeometry g n lo hi
  disjoint : [g,n,f,u].Nodup
  flags : ∀q∈sites (lo++hi),q≠f ∧ q≠u

theorem packed (lo hi:List (Wire×Wire)) (g n f u:Wire) (neg far long:Bool)
    (origin v w x result:State) (L:CutLayout lo hi g n f u)
    (scanPhase:v.phase=origin.phase) (scanSign:v.basis n=neg)
    (scanOutside:∀q,q≠n→q∉sites (lo++hi)→v.basis q=origin.basis q)
    (scanWords:∀p∈lo++hi,v.basis p.1=(if origin.basis g then origin.basis p.2 else origin.basis p.1) ∧
       v.basis p.2=((if origin.basis g then origin.basis p.1 else origin.basis p.2) ^^ neg))
    (flags:w=⟨v.phase,writeBit (writeBit v.basis f far) u long⟩)
    (erase:x.phase=w.phase ∧ (∀q,q∉hi.map Prod.snd→x.basis q=w.basis q) ∧ regValue (hi.map Prod.snd) x.basis=0)
    (storePhase:result.phase=x.phase)
    (storeOutside:∀q,q∉sites lo→q∉sites hi→ result.basis q=x.basis q)
    (storeUpper:∀p∈hi,result.basis p.1=false ∧ result.basis p.2=x.basis p.1)
    (storeLow:∀p∈lo,result.basis p.1=(if x.basis g then x.basis p.2 ^^ x.basis n else x.basis p.1) ∧
       result.basis p.2=(if x.basis g then x.basis p.1 else x.basis p.2 ^^ x.basis n))
    (exclusive:∀p∈hi,p.1∉hi.map Prod.snd) :
    PackedCut lo hi g n f u neg far long origin result := by
  obtain ⟨gn,gf,gu,nf,nu,fu⟩:g≠n ∧ g≠f ∧ g≠u ∧ n≠f ∧ n≠u ∧ f≠u:=by simpa [and_assoc] using L.disjoint
  have inside (p:Wire×Wire) (ps:List (Wire×Wire)) (hp:p∈ps):p.1∈sites ps ∧ p.2∈sites ps:=by
    constructor <;> exact List.mem_flatMap.mpr ⟨p,hp,by simp⟩
  have sub (q:Wire) (hq:q∈hi.map Prod.snd):q∈sites hi:=by
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hq;exact (inside _ _ hp).2
  have memb (q:Wire):q∈sites (lo++hi) ↔ q∈sites lo ∨ q∈sites hi:=by simp [sites]
  have stageW (q:Wire) (qf:q≠f) (qu:q≠u):w.basis q=v.basis q:=by simp [flags,writeBit,qf,qu]
  have wholeW (q:Wire) (hq:q∈sites (lo++hi)):w.basis q=v.basis q:=
    stageW _ (L.flags _ hq).1 (L.flags _ hq).2
  have stageX (q:Wire) (qh:q∉sites hi):x.basis q=w.basis q:=erase.2.1 q (fun h=>qh (sub _ h))
  have ns:x.basis n=neg:=((stageX n L.store.nh).trans (stageW _ nf nu)).trans scanSign
  have gl:g∉sites lo:=(List.nodup_cons.mp L.store.lo_ok).1
  have gs:x.basis g=origin.basis g:=((stageX g L.store.gh).trans (stageW _ gf gu)).trans
    (scanOutside g gn (fun h=>((memb _).mp h).elim gl L.store.gh))
  have fo:f∉sites (lo++hi):=fun h=>(L.flags f h).1 rfl
  have uo:u∉sites (lo++hi):=fun h=>(L.flags u h).2 rfl
  have projected (q:Wire) (out:q∉sites (lo++hi)):result.basis q=w.basis q:=by
    have l:q∉sites lo:=fun h=>out ((memb _).mpr (Or.inl h))
    have r:q∉sites hi:=fun h=>out ((memb _).mpr (Or.inr h))
    exact (storeOutside _ l r).trans (stageX _ r)
  refine ⟨storePhase.trans (erase.1.trans ((congrArg State.phase flags).trans scanPhase)),?_,?_,?_,?_,?_,?_⟩
  · exact (storeOutside _ L.store.nl L.store.nh).trans ns
  · rw [projected f fo,flags];simp [writeBit,fu]
  · rw [projected u uo,flags];simp [writeBit]
  · intro p hp
    have inc:=inside _ _ hp
    have ids (q:Wire) (inL:q∈sites lo):x.basis q=v.basis q:=
      (stageX q (L.store.split _ inL)).trans (wholeW _ ((memb _).mpr (Or.inl inL)))
    have h:=storeLow _ hp
    obtain ⟨va,vb⟩:=scanWords p (List.mem_append_left _ hp)
    rw [gs,ns,ids _ inc.1,ids _ inc.2,va,vb] at h
    cases hg:origin.basis g <;> simpa [hg] using h
  · intro p hp
    have h:=storeUpper _ hp
    obtain ⟨v0,_⟩:=scanWords _ (List.mem_append_right _ hp)
    exact ⟨h.1,h.2.trans ((erase.2.1 _ (exclusive _ hp)).trans ((wholeW _
      ((memb _).mpr (Or.inr (inside _ _ hp).1))).trans v0))⟩
  · intro q qn qf qu l h
    have out:q∉sites (lo++hi):=fun mem=>((memb _).mp mem).elim l h
    exact ((projected q out).trans (stageW _ qf qu)).trans (scanOutside q qn out)

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalUnitInverse
open Arithmetic

def emit : List Wire → List Wire → Wire → Program
  | y::z::ys,t::ts,c => [.CX c y,.CCX y c t] ++ emit (z::ys) ts t ++ [.measureX t [] [.CZ y c]]
  | [y],_,c => [.CX c y]
  | _,_,_ => []

private theorem cx_twice (a b:Wire) (ne:a≠b) (s:State) (m n:List Bool) :
    run [.CX a b] n (run [.CX a b] m s)=s := by
  simp [run,writeBit,Function.update,ne]

private theorem resume (y c t:Wire) (h:[y,c,t].Nodup) (s:State) (m n:List Bool)
    (ht:s.basis t=(s.basis y && s.basis c)) :
    run [.CX c y,.CCX y c t] n (run [.measureX t [] [.CZ y c],.CX c y] m s)=s := by
  obtain ⟨yc,yt,ct⟩:y≠c ∧ y≠t ∧ c≠t:=by simpa [and_assoc] using h
  change run [.CX c y,.CCX y c t] n (run [.CX c y] (m.drop 1) (run [.measureX t [] [.CZ y c]] m s))=_
  rw [PortalAnd.measure_and _ _ _ _ _ yt ct ht]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qy:q=y <;> by_cases qt:q=t <;>
    simp_all [run,writeBit,Function.update,yc.symm,yt.symm]

private theorem start (y c t:Wire) (h:[y,c,t].Nodup) (s:State) (m n:List Bool) (zero:s.basis t=false) :
    run [.measureX t [] [.CZ y c]] n (run [.CCX y c t] m s)=s := by
  obtain ⟨yc,yt,ct⟩:y≠c ∧ y≠t ∧ c≠t:=by simpa [and_assoc] using h
  rw [PortalAnd.measure_and _ _ _ _ _ yt ct (by simp [run,writeBit,zero,yt,ct])]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases eq:q=t <;> simp_all [run,writeBit,Function.update]

theorem undo (ys cs:List Wire) (c:Wire) (n:cs.length+1=ys.length) (nd:(c::(ys++cs)).Nodup)
    (s:State) (m tape:List Bool) (clean:∀q∈cs,s.basis q=false) :
    run (emit ys cs c) tape (run (HighBankUnit.add ys cs c) m s)=s := by
  induction ys generalizing cs c s m tape with
  | nil => simp at n
  | cons y rest ih =>
    cases rest with
    | nil =>
      exact cx_twice c y (fun h=>(List.nodup_cons.mp nd).1 (by simp [h])) s m tape
    | cons z ys =>
      cases cs with
      | nil => simp at n
      | cons t ts =>
        let rem:=z::ys
        have len:ts.length+1=rem.length:=by simp [rem] at *;omega
        have sub:(c::y::(rem++(t::ts))).Nodup:=nd
        have ⟨cy,cr,ct,cs',yr,yt,ys',rr⟩ : c≠y ∧ c∉rem ∧ c≠t ∧ c∉ts ∧
              y∉rem ∧ y≠t ∧ y∉ts ∧ (rem++t::ts).Nodup := by
          simpa [List.mem_append,and_assoc] using sub
        have h3:[y,c,t].Nodup:=by simp [cy.symm,yt,ct]
        have split:=List.nodup_append.mp rr
        have tr:t∉rem:=fun h=>split.2.2 _ h _ (by simp) rfl
        have nextND:(t::(rem++ts)).Nodup:=by
          have tt:=List.nodup_cons.mp split.2.1
          exact List.nodup_cons.mpr ⟨by simp [tr,tt.1],List.nodup_append.mpr
            ⟨split.1,tt.2,fun a ha b hb=>split.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩⟩
        let v:=run ([.CCX y c t]:Program) m s
        have zero:=clean t (by simp)
        have ht:v.basis t=(s.basis y && s.basis c):=by simp [v,run,writeBit,zero]
        have keep (q:Wire) (h:q≠t):v.basis q=s.basis q:=by simp [v,run,writeBit,h]
        have fresh:∀q∈ts,v.basis q=false:=by
          intro q h; rw [keep _ (fun e=>(List.nodup_cons.mp split.2.1).1 (e ▸ h))]
          exact clean _ (List.mem_cons_of_mem _ h)
        let w:=run (HighBankUnit.add rem ts t) m v
        have mid:=HighBankUnit.add_correct rem ts t nextND len v m fresh
        have bit:w.basis t=(w.basis y && w.basis c):=by
          change _=(_ && _)
          rw [show w.basis t=v.basis t from mid.2.1 t tr,show w.basis y=v.basis y from mid.2.1 y yr,
            show w.basis c=v.basis c from mid.2.1 c cr,ht,keep _ yt,keep _ ct]
        have body:HighBankUnit.add (y::z::ys) (t::ts) c=
          [.CCX y c t]++HighBankUnit.add rem ts t++[.measureX t [] [.CZ y c],.CX c y]:=by
          simp [HighBankUnit.add,HighBankUnit.zeros,rem,List.replicate_succ,mappedAdd,mappedMajority,mappedEraseCarry,mappedSum,List.append_assoc]
        rw [body,emit]
        simp only [run_append,run_take]
        change run [.measureX t [] [.CZ y c]] _
          (run (emit rem ts t) _ (run [.CX c y,.CCX y c t] tape (run [.measureX t [] [.CZ y c],.CX c y] _ w)))=s
        rw [resume _ _ _ h3 w _ _ bit,ih ts t len nextND v m _ fresh]
        exact start _ _ _ h3 s m _ zero

#print axioms undo
end ECDSAAdd.Entrant.StairPacket.PortalUnitInverse

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

/-- A retained AND is erased by an X-basis measurement with the same two controls. -/
inductive Op where
  | xor (control target : Wire)
  | mix (a b target : Wire)
  | save (a b target : Wire)
deriving DecidableEq, Repr

def Op.dst : Op → Wire
  | .xor _ t | .mix _ _ t | .save _ _ t => t

def Op.args : Op → List Wire
  | .xor a _ => [a]
  | .mix a b _ | .save a b _ => [a,b]

def Op.val (o : Op) (v : BasisState) : Bool :=
  match o with
  | .xor a _ => v a
  | .mix a b _ | .save a b _ => v a && v b

def Op.step (o : Op) (v : BasisState) := writeBit v o.dst (v o.dst ^^ o.val v)
def Op.enter : Op → Instr
  | .xor a t => .CX a t
  | .mix a b t | .save a b t => .CCX a b t
def Op.exit : Op → Instr
  | .save a b t => .measureX t [] [.CZ a b]
  | o => o.enter

def trace (ops : List Op) (v : BasisState) := ops.foldl (fun s o => o.step s) v

theorem enter_run (ops : List Op) (m : List Bool) (s : State) :
    run (ops.map Op.enter) m s=⟨s.phase,trace ops s.basis⟩ := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    cases o <;> exact ih _

def Op.safe (o : Op) (v : BasisState) : Prop :=
  o.dst ∉ o.args ∧ match o with
    | .save _ _ t => v t=false
    | _ => True

def Safe : List Op → BasisState → Prop
  | [], _ => True
  | o::os,v => o.safe v ∧ Safe os (o.step v)

theorem undo_op (o : Op) (s : State) (m : List Bool) (h : o.safe s.basis) :
    run [o.exit] m ⟨s.phase,o.step s.basis⟩=s := by
  cases o with
  | xor a t =>
    obtain ⟨at',_⟩ := h
    have at' : a≠t := Ne.symm (by simpa [Op.dst,Op.args] using at')
    simp [Op.exit,Op.enter,Op.step,Op.val,Op.dst,run,writeBit,Function.update,at']
  | mix a b t =>
    obtain ⟨abc,_⟩ := h
    obtain ⟨ta,tb⟩ : t≠a ∧ t≠b := by simpa [Op.dst,Op.args] using abc
    simp [Op.exit,Op.enter,Op.step,Op.val,Op.dst,run,writeBit,Function.update,ta.symm,tb.symm]
  | save a b t =>
    obtain ⟨abc,hz⟩ := h
    obtain ⟨ta,tb⟩ : t≠a ∧ t≠b := by simpa [Op.dst,Op.args] using abc
    change s.basis t=false at hz
    simp only [Op.exit,run]
    cases hm:m.headD false <;>
      simp [Op.step,Op.dst,Op.val,measureAndCorrect,correct,writeBit,Function.update,ta.symm,tb.symm,hz]
      <;> apply congrArg₂ State.mk rfl <;> simpa using hz

theorem exit_run (ops : List Op) (s : State) (m : List Bool) (h : Safe ops s.basis) :
    run (ops.reverse.map Op.exit) m ⟨s.phase,trace ops s.basis⟩=s := by
  induction ops generalizing s m with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨ho,hos⟩ := h
    rw [List.reverse_cons,List.map_append,run_append,run_take]
    change run [o.exit] _ (run _ m ⟨s.phase,trace os (o.step s.basis)⟩)=s
    rw [ih ⟨s.phase,o.step s.basis⟩ m hos]
    exact undo_op _ _ _ ho

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497]
def railB : List Wire := [946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 497 1723,.CX 1042 1723] ++
  RailPair.exchange 240 (railA.zip railB) ++ signComplement 1723 railB
def flags : Program := [.CCX 401 402 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 401 402],.CX 1556 1721,.CX 1721 1556] ++ orientation
def erase : Program := [.X 403,.CCX 948 403 1556] ++
  Companion.erase bulkA bulkB carry 1722 1556 ++
  [.measureX 1556 [] [.CZ 948 403],.X 403]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1723 (railB.take 3) ++ RailPair.exchange 240 ((railA.take 3).zip (railB.take 3))
theorem emitted : Partial.portal225=scan++flags++erase++store := by decide +kernel
theorem exchange_good : (240::RailPair.sites (railA.zip railB)).Nodup := by decide +kernel
theorem complement_good : railB.Nodup ∧ 1723∉railB := by decide +kernel
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by decide +kernel
theorem copy_good : Companion.Geometry bulkA bulkB carry 1722 1556 := by
  constructor <;> decide +kernel
#print axioms emitted
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528]
def railB : List Wire := [923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 528 1700,.CX 1028 1700] ++
  RailPair.exchange 285 (railA.zip railB) ++ signComplement 1700 railB
def flags : Program := [.CCX 423 424 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 423 424],.CX 1556 1698,.CX 1698 1556] ++ orientation
def erase : Program := [.X 425,.CCX 925 425 1556] ++
  Companion.erase bulkA bulkB carry 1699 1556 ++
  [.measureX 1556 [] [.CZ 925 425],.X 425]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1700 (railB.take 3) ++ RailPair.exchange 285 ((railA.take 3).zip (railB.take 3))
theorem emitted : Partial.portal270=scan++flags++erase++store := by decide +kernel
theorem exchange_good : (285::RailPair.sites (railA.zip railB)).Nodup := by decide +kernel
theorem complement_good : railB.Nodup ∧ 1700∉railB := by decide +kernel
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by decide +kernel
theorem copy_good : Companion.Geometry bulkA bulkB carry 1699 1556 := by
  constructor <;> decide +kernel
#print axioms emitted
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalBorrow
open Arithmetic

def wrap (a b t:Wire) (body:Program) : Program :=
  [.X a,.CCX b a t]++body++[.measureX t [] [.CZ b a],.X a]

def prep (a b t:Wire) (s:State) : State := ⟨s.phase,writeBit (writeBit s.basis a (!s.basis a)) t
  (s.basis b && !s.basis a)⟩

theorem outside {a b t:Wire} (s:State) (q:Wire) (qa:q≠a) (qt:q≠t) :
    (prep a b t s).basis q=s.basis q := by simp [prep,writeBit,qa,qt]

theorem erase_run (a b t long:Wire) (xs ys cs:List Wire) (s:State) (m:List Bool)
    (L:Companion.Geometry xs ys cs long t) (distinct:[a,b,t,long].Nodup)
    (noA:a∉xs ∧ a∉ys ∧ a∉cs) (noB:b∉ys) (noT:t∉xs ∧ t∉ys ∧ t∉cs)
    (fresh:s.basis t=false) (clean:∀q∈cs,s.basis q=false)
    (value:(regValue ys s.basis+(s.basis b && !s.basis a).toNat)%2^ys.length=
      copyValue (some long) s.basis (regValue xs s.basis)) :
    let r:=run (wrap a b t (Companion.erase xs ys cs long t)) m s
    r.phase=s.phase ∧ (∀q,q∉ys → r.basis q=s.basis q) ∧ regValue ys r.basis=0 := by
  have ⟨ab,at0,al,bt,bl,tl⟩:a≠b ∧ a≠t ∧ a≠long ∧ b≠t ∧ b≠long ∧ t≠long := by simpa [and_assoc] using distinct
  let v:=prep a b t s
  have start:run ([.X a,.CCX b a t]:Program) m s=v:=by
    simp [v,prep,run,writeBit,ab.symm,at0.symm,fresh]
  have aa:v.basis a= !s.basis a:=by simp [v,prep,writeBit,at0]
  have bb:v.basis b=s.basis b:=outside s _ ab.symm bt
  have tt:v.basis t=(s.basis b && !s.basis a):=by simp [v,prep,writeBit]
  have gc:∀q∈cs,v.basis q=false:=fun q h=>(outside (a:=a) (b:=b) (t:=t) s q (fun e=>noA.2.2 (e ▸ h))
    (fun e=>noT.2.2 (e ▸ h))).trans (clean _ h)
  have rg (rs:List Wire) (ha:a∉rs) (ht:t∉rs):regValue rs v.basis=regValue rs s.basis:=
    regValue_congr _ _ _ (fun q h=>outside (a:=a) (b:=b) (t:=t) s q (fun e=>ha (e ▸ h)) (fun e=>ht (e ▸ h)))
  have vv:(regValue ys v.basis+(v.basis t).toNat)%2^ys.length=
      copyValue (some long) v.basis (regValue xs v.basis):=by
    rw [rg ys noA.2.1 noT.2.1,tt,rg xs noA.1 noT.1]
    change _=if v.basis long then _ else _
    rw [outside s long al.symm tl.symm]
    exact value
  let mid:=run (Companion.erase xs ys cs long t) m v
  obtain ⟨ph,stay,zero⟩:=Companion.clear xs ys cs long t L v m gc vv
  have ta:mid.basis a= !s.basis a:=(stay _ noA.2.1).trans aa
  have tb:mid.basis b=s.basis b:=(stay _ noB).trans bb
  have tc:mid.basis t=(mid.basis b && mid.basis a):=by rw [ta,tb];exact (stay _ noT.2.1).trans tt
  have post (ms:List Bool):run ([.measureX t [] [.CZ b a],.X a]:Program) ms mid=
      ⟨mid.phase,writeBit (writeBit mid.basis t false) a (s.basis a)⟩:=by
    change run ([.X a]:Program) (ms.drop 1) (run ([.measureX t [] [.CZ b a]]:Program) ms mid)=_
    rw [PortalAnd.measure_and _ _ _ _ _ bt at0 tc]
    simp [run,writeBit,at0,ta]
  simp only [wrap,run_append,run_take,start]
  change (run _ _ mid).phase=_ ∧ (∀q,q∉ys → (run _ _ mid).basis q=_) ∧ regValue ys (run _ _ mid).basis=0
  rw [post]
  refine ⟨ph,?_,?_⟩
  · intro q h
    by_cases qa:q=a <;> by_cases qt:q=t
    · exact (at0 (qa.symm.trans qt)).elim
    · subst q; simp [writeBit]
    · subst q; simp [writeBit,at0.symm,fresh]
    · exact (show writeBit (writeBit mid.basis t false) a (s.basis a) q=mid.basis q by simp [writeBit,qa,qt]).trans
        ((stay q h).trans (outside s _ qa qt))
  · apply Eq.trans _ zero
    apply regValue_congr
    intro q h
    have ha:q≠a:=fun e=>noA.2.1 (e ▸ h)
    have ht:q≠t:=fun e=>noT.2.1 (e ▸ h)
    simp [writeBit,ha,ht,mid]
#print axioms erase_run
end ECDSAAdd.Entrant.StairPacket.PortalBorrow

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem nonzero (xs:List Wire) (b:BasisState) : xs.any b=decide (0<regValue xs b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (b x || xs.any b)=decide (0<(if b x then 1 else 0)+2*regValue xs b)
    rw [ih];cases b x <;> simp

theorem atLeastThree (a b:Wire) (rest:List Wire) (s:BasisState) :
    ((s a && s b) || rest.any s)=decide (3≤regValue (a::b::rest) s) := by
  rw [nonzero]
  change _=decide (3≤(if s a then 1 else 0)+2*((if s b then 1 else 0)+2*regValue rest s))
  cases s a <;> cases s b <;> simp <;> omega

theorem actual_flags (a b:Wire) (as bs:List (Wire×Wire)) (mag:Wire) (A B:List Wire)
    (aShape:a::b::as.map Prod.fst=A) (bShape:PortalAnd.digits mag bs=B)
    (s:BasisState) (U small u v e:Nat) (ub:2*small≤U) (bp:0<small)
    (sz:min u v<small) (en:e≤1) (x:regValue A s=(u+v)/U) (y:regValue B s=(u-e)/U) :
    PortalAnd.high a b as s=decide (3*U≤u+v) ∧
    (PortalAnd.high a b as s && (PortalAnd.digits mag bs).any s)=decide (3*U≤u+v ∧ small≤u) := by
  have up:0<U:=by omega
  have far:PortalAnd.high a b as s=decide (3*U≤u+v):=by
    rw [PortalAnd.high,atLeastThree,aShape,x]
    apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using (Nat.le_div_iff_mul_le up : 3≤(u+v)/U ↔ _)
  have longer:(PortalAnd.digits mag bs).any s=decide (U≤u-e):=by
    rw [bShape,nonzero,y]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      by_contra hh
      rw [Nat.div_eq_of_lt (by omega)] at h;omega
    · intro hh
      exact Nat.div_pos hh up
  refine ⟨far,?_⟩
  rw [far,longer]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,Bool.and_eq_true] using PortalCut.orientation small U u v e ub bp sz en
#print axioms actual_flags
end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic

def thresholdBack (a b t out:Wire) (ps:List (Wire×Wire)):Program :=
  [.CCX a b t]++backwardLatch true none out t ps++[.measureX t [] [.CZ a b]]

theorem threshold_back (a b t out:Wire) (ps:List (Wire×Wire))
    (layout:(a::b::out::t::sites ps).Nodup) (s:State) (m:List Bool)
    (fresh:s.basis t=false) (clean:∀p∈ps,s.basis p.2=false) :
    run (thresholdBack a b t out ps) m s = ⟨s.phase,writeBit s.basis out
      (s.basis out ^^ high a b ps s.basis)⟩ := by
  apply Eq.trans _ (threshold_run _ _ _ _ _ layout s m fresh clean)
  let v:=run ([.CCX a b t]:Program) m s
  have lay: (out::t::sites ps).Nodup:=(List.nodup_cons.mp (List.nodup_cons.mp layout).2).2
  have fresh':∀p∈ps,v.basis p.2=false:=by
    intro p hp
    have inc:p.2∈sites ps:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
    have dif:p.2≠t:=fun eq=>(List.nodup_cons.mp (List.nodup_cons.mp lay).2).1 (eq ▸ inc)
    simp [v,run,writeBit,dif,clean _ hp]
  have swap (ms:List Bool):run (backwardLatch true none out t ps) ms v=run (latch true none out t ps) ms v:=by
    rw [backward_latch _ _ _ _ _ lay (by simp) v ms fresh',run_latch _ _ _ _ _ lay (by simp) v ms fresh']
  have rows:measurementCount (backwardLatch true none out t ps)=measurementCount (latch true none out t ps):=by
    change measurementCount (notRegister _ ++ backward _ _ _ _ ++ notRegister _)=measurementCount (notRegister _ ++ chain _ _ _ _ _ ++ notRegister _)
    simp only [measurementCount_append,back_count,ite_true]
  simp only [thresholdBack,threshold,run_append,run_take,measurementCount_append,rows]
  change run [.measureX t [] [.CZ a b]] _ (run (backwardLatch true none out t ps) _ v)=
    run [.measureX t [] [.CZ a b]] _ (run (latch true none out t ps) _ v)
  rw [swap]

def flagsBack (a b low temp far long mag:Wire) (as bs:List (Wire×Wire)):Program :=
  backwardLatch false (some far) long mag bs ++ [.CX far temp,.CX temp far] ++ thresholdBack a b low temp as

theorem flags_undo (a b low temp far long mag : Wire) (as bs : List (Wire×Wire))
    (lA:(a::b::temp::low::sites as).Nodup)
    (lB:(far::long::mag::sites bs).Nodup) (ft:far≠temp)
    (s:State) (m tape:List Bool) (hf:s.basis far=false) (ht:s.basis temp=false)
    (hl:s.basis low=false) (hj:s.basis long=false)
    (ca:∀p∈as,s.basis p.2=false) (cb:∀p∈bs,s.basis p.2=false) :
    run (flagsBack a b low temp far long mag as bs) tape
      (run (flags a b low temp far long mag as bs) m s)=s := by
  let f:=high a b as s.basis
  let u:=f && (digits mag bs).any s.basis
  let v:State:=⟨s.phase,writeBit s.basis far f⟩
  let w:State:=⟨s.phase,writeBit v.basis long u⟩
  let k:State:=⟨s.phase,writeBit s.basis temp f⟩
  have input:run (flags a b low temp far long mag as bs) m s=w :=
    flags_run _ _ _ _ _ _ _ _ _ lA lB ft _ _ hf ht hl hj ca cb
  have detail (p:Wire×Wire) (ps:List (Wire×Wire)) (h:p∈ps) : p.1∈sites ps ∧ p.2∈sites ps:=by
    constructor <;> exact List.mem_flatMap.mpr ⟨p,h,by simp⟩
  obtain ⟨fl,fm,fr,lm,lr,mr,nb⟩:far≠long ∧ far≠mag ∧ far∉sites bs ∧ long≠mag ∧
      long∉sites bs ∧ mag∉sites bs ∧ (sites bs).Nodup:=by simpa [and_assoc] using lB
  obtain ⟨ab,at0,al,ar,bt,bl,br,tl,tr,lrA,na⟩:a≠b ∧ a≠temp ∧ a≠low ∧ a∉sites as ∧ b≠temp ∧ b≠low ∧ b∉sites as ∧
      temp≠low ∧ temp∉sites as ∧ low∉sites as ∧ (sites as).Nodup:=by simpa [and_assoc] using lA
  have stableW (q:Wire) (qf:q≠far) (ql:q≠long):w.basis q=s.basis q:=by simp [w,v,writeBit,qf,ql]
  have src (q:Wire) (hq:q∈digits mag bs):w.basis q=s.basis q:=by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact stableW _ fm.symm lm.symm
    · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hq
      exact stableW _ (fun eq=>fr (eq ▸ (detail _ _ hp).1)) (fun eq=>lr (eq ▸ (detail _ _ hp).1))
  have anyEq:(digits mag bs).any w.basis=(digits mag bs).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,h,hq⟩ <;> exact ⟨q,h,by simpa [src _ h] using hq⟩
  have cbw (p:Wire×Wire) (hp:p∈bs):w.basis p.2=false:=
    (stableW _ (fun eq=>fr (eq ▸ (detail _ _ hp).2)) (fun eq=>lr (eq ▸ (detail _ _ hp).2))).trans (cb _ hp)
  have reset (ms:List Bool):run (backwardLatch false (some far) long mag bs) ms w=v:=by
    rw [backward_latch _ _ _ _ _ (List.nodup_cons.mp lB).2 (by
      intro c hc; obtain rfl:=Option.mem_some_iff.mp hc; exact (List.nodup_cons.mp lB).1) _ _ cbw,anyEq]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qf:q=far <;> by_cases ql:q=long <;> simp_all [active,w,v,u,writeBit,Function.update]
  have exchange (ms:List Bool):run [.CX far temp,.CX temp far] ms v=k:=by
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qf:q=far <;> by_cases qt:q=temp <;> simp_all [v,writeBit,Function.update,ft.symm]
  have kskip (q:Wire) (ne:q≠temp):k.basis q=s.basis q:=by simp [k,writeBit,ne]
  have ka (q:Wire) (h:q∈as.map Prod.fst):k.basis q=s.basis q:=by
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
    exact kskip _ (fun eq=>tr (eq ▸ (detail _ _ hp).1))
  have anyA:(as.map Prod.fst).any k.basis=(as.map Prod.fst).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,h,hq⟩ <;> exact ⟨q,h,by simpa [ka _ h] using hq⟩
  have highK:high a b as k.basis=f:=by simp [high,f,kskip _ at0,kskip _ bt,anyA]
  have clearK (ms:List Bool):run (thresholdBack a b low temp as) ms k=s:=by
    rw [threshold_back _ _ _ _ _ lA k ms ((kskip _ tl.symm).trans hl) (fun p hp=>
       (kskip _ (fun eq=>tr (eq ▸ (detail _ _ hp).2))).trans (ca _ hp)),highK]
    apply congrArg (State.mk s.phase)
    funext q; by_cases qt:q=temp <;> simp_all [k,writeBit,Function.update]
  simp only [input,flagsBack,run_append,run_take,reset,exchange,clearK]
#print axioms flags_undo
end ECDSAAdd.Entrant.StairPacket.PortalAnd

end

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat IntegerHigh

def limb (b k : Nat) := 2^(b+k+1)
def high (b k : Nat) (z : SkywalkNat.State) := (z.u+z.v)/limb b k
def far (b k : Nat) (z : SkywalkNat.State) : Prop := 3≤high b k z
instance (b k : Nat) (z : SkywalkNat.State) : Decidable (far b k z) := inferInstanceAs (Decidable (3≤_))
def gap (b k : Nat) (z : SkywalkNat.State) := (high b k z-2)*limb b k
def reduced (b k : Nat) (z : SkywalkNat.State) : SkywalkNat.State :=
  if far b k z then
    if 2^b≤z.u then ⟨z.u-gap b k z,z.v⟩ else ⟨z.u,z.v-gap b k z⟩
  else z

theorem represented (b k : Nat) (z : SkywalkNat.State) (small : min z.u z.v < 2^b)
    (h : far b k z) :
    Rel k z (reduced b k z) ∧
    2*limb b k≤(reduced b k z).u+(reduced b k z).v ∧
    (reduced b k z).u+(reduced b k z).v<3*limb b k := by
  let U:=limb b k
  let H:=high b k z
  let R:=(z.u+z.v)%U
  have hu:0<U:=by simp [U,limb]
  have hr:R<U:=Nat.mod_lt _ hu
  have decomp:z.u+z.v=R+U*H:=(Nat.mod_add_div _ _).symm
  have hh:3≤H:=h
  have remove : U*H=gap b k z+2*U := by
    change U*H=(H-2)*U+2*U
    rw [←Nat.add_mul,show H-2+2=H by omega,Nat.mul_comm]
  have bound:2^b≤U:=by
    dsimp [U,limb]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have form:gap b k z=2^k*((H-2)*2^(b+1)) := by
    change (H-2)*2^(b+k+1)=_
    rw [show b+k+1=k+(b+1) by omega,pow_add]
    ring
  rw [reduced,if_pos h]
  split
  · rename_i big
    have hv:z.v<2^b:=by omega
    have gu:guard k z.v≤z.u-gap b k z:=
      (guard_small k z.v b hv).trans (by change U≤_;omega)
    have eq:z.u=(z.u-gap b k z)+2^k*((H-2)*2^(b+1)):=by omega
    constructor
    · conv_lhs => rw [show z=⟨(z.u-gap b k z)+2^k*((H-2)*2^(b+1)),z.v⟩
                           from by cases z; exact congrArg₂ SkywalkNat.State.mk eq rfl]
      exact .left _ _ _ gu
    · change 2*U≤z.u-gap b k z+z.v ∧ z.u-gap b k z+z.v<3*U
      omega
  · rename_i little
    have u:z.u<2^b:=by omega
    have gv:guard k z.u≤z.v-gap b k z:=
      (guard_small k z.u b u).trans (by change U≤_;omega)
    have eq:z.v=(z.v-gap b k z)+2^k*((H-2)*2^(b+1)):=by omega
    constructor
    · conv_lhs => rw [show z=⟨z.u,(z.v-gap b k z)+2^k*((H-2)*2^(b+1))⟩
                           from by cases z; exact congrArg₂ SkywalkNat.State.mk rfl eq]
      exact .right _ _ _ gv
    · change 2*U≤z.u+(z.v-gap b k z) ∧ z.u+(z.v-gap b k z)<3*U
      omega

#print axioms represented
end ECDSAAdd.Entrant.StairPacket.Shadow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowCosts
open Arithmetic MappedCompressed
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount
private def due (i : Nat) := if History5.packDue i then 1 else 0
private def step (i : Nat) (back measured : Bool) : Nat :=
  let pre := W.compactSkywalkTickPreWidth i - 1
  let post := W.compactSkywalkTickPostWidth i - 1
  if back then
    if measured then post + 2*due i
    else pre+post-1-(if W.trimTick i then 1 else 0)+11*due i
  else if measured then post+W.repairDue i+4*due i
  else pre+post-W.repairDue i-W.fwdDue i-TickRanges.due i+9*due i
private def total (i : Nat) (back measured : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => step i back measured + total (i+1) back measured n

private theorem codecs (d : Bool) (i : Nat) (lo : 6 ≤ i) :
    toffoliCount (Rolling1588.Integer.packFirst base d i)=9*due i ∧
    measurementCount (Rolling1588.Integer.packFirst base d i)=4*due i ∧
    toffoliCount (Rolling1588.unpackAtTick d i)=11*due i ∧
    measurementCount (Rolling1588.unpackAtTick d i)=2*due i := by
  have five : i ≠ 5 := by omega
  have nz : i-5 ≠ 0 := by omega
  have c := Rolling1588.code_counts d
  cases h : History5.packDue i <;>
    simp only [Rolling1588.Integer.packFirst, Rolling1588.Integer.packAfter,
      Rolling1588.Integer.encode, Rolling1588.encodeAt, Rolling1588.codeEncodeAt, Rolling1588.unpackAtTick,
      five,nz,if_false,h,Bool.false_eq_true,if_true,due,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,c.1,c.2.1,c.2.2.1,c.2.2.2] <;> simp [measurementCount,toffoliCount]

private theorem walks (d : Bool) (i n : Nat) (lo : 6 ≤ i) (hi : i+n ≤ 511) :
    toffoliCount (Rolling1588TickGap.forward d i n)=total i false false n ∧
    measurementCount (Rolling1588TickGap.forward d i n)=total i false true n ∧
    toffoliCount (Rolling1588.reverse d i n)=total i true false n ∧
    measurementCount (Rolling1588.reverse d i n)=total i true true n := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward,Rolling1588.reverse,total,toffoliCount,measurementCount]
  | succ n ih =>
    have tail := ih (i+1) (by omega) (by omega)
    have pack := codecs d i lo
    have ft := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have rt := W.repairedTick_counts base i (by omega) base_pool_nodup
    have st := W.compactSkywalkTick_counts base i (by omega) base_pool_nodup
    have bt := W.ReverseCarry.compactReceiverTick_counts base i (by omega) base_pool_nodup
    have ot := W.compactSkywalkReverseTick_counts base i (by omega) base_pool_nodup
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,toffoliCount_append,
      measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      tail.1,tail.2.1,tail.2.2.1,tail.2.2.2,pack.1,pack.2.1,pack.2.2.1,pack.2.2.2,
      total,step,if_true,if_false,Bool.false_eq_true]
    exact ⟨by omega,by omega,by omega,by omega⟩

theorem stock (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 225 46)=23355 ∧
    measurementCount (Rolling1588TickGap.forward d 225 46)=11712 ∧
    toffoliCount (Rolling1588.reverse d 225 46)=23376 ∧
    measurementCount (Rolling1588.reverse d 225 46)=11676 := by
  have h := walks d 225 46 (by decide) (by decide)
  exact ⟨h.1.trans (by decide +kernel), h.2.1.trans (by decide +kernel),
    h.2.2.1.trans (by decide +kernel), h.2.2.2.trans (by decide +kernel)⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Partial LeaveSelector HighBankFirstHit Leave225Hit
set_option maxRecDepth 50000

def far : List Op := [.xor 1559 1725, .xor 1561 1725, .xor 1562 1725, .xor 1563 1725, .xor 1564 1725, .xor 1565 1725]
def zero : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffix : List Op := [.save 254 255 1577, .save 253 1577 1578, .save 252 1578 1579, .save 251 1579 1580, .save 250 1580 1581, .save 249 1581 1582, .save 248 1582 1583, .save 247 1583 1584, .save 246 1584 1585, .save 245 1585 1586, .save 244 1586 1587, .save 243 1587 1588]
def select : List Op := [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593, .save 1567 1578 1594, .save 1568 255 1595]
def cross : List Op := [.mix 1576 401 1724, .mix 1562 402 1724, .mix 1563 403 1724, .mix 1564 404 1724, .mix 1565 405 1724, .mix 1566 406 1724, .mix 1567 407 1724, .mix 1568 408 1724, .mix 1569 409 1724, .mix 1570 410 1724, .mix 1571 411 1724, .mix 1572 412 1724, .mix 1573 413 1724, .mix 1574 414 1724, .mix 1575 415 1724, .mix 1560 416 1724]
def sign : List Op := [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596, .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596, .xor 1560 1596]
def product : List Op := [.save 1724 1596 1597]

def prepare := far ++ zero ++ suffix ++ select ++ cross ++ sign ++ product
def retire := (product.reverse ++ sign ++ select.reverse ++ suffix.reverse ++ zero)
def prepareInv := zero.reverse ++ suffix ++ select ++ sign.reverse ++ product
def retireInv := prepare.reverse

theorem prepared : ((leave225.drop 275).take 59) = prepare.map Op.enter := by rfl

theorem retired : ((leave225.drop 2190).take 37) = retire.map Op.exit := by rfl

theorem preparedInv : ((leave225Inv.drop 965).take 37) = prepareInv.map Op.enter := by rfl

theorem retiredInv : ((leave225Inv.drop 2858).take 59) = retireInv.map Op.exit := by rfl

theorem hitsInv : ((leave225Inv.drop 935).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retireHits : ((leave225.drop 2227).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Partial LeaveSelector HighBankFirstHit Leave240Hit
set_option maxRecDepth 50000

def far : List Op := [.xor 1559 1717, .xor 1561 1717, .xor 1562 1717, .xor 1563 1717, .xor 1564 1717, .xor 1565 1717]
def zero : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffix : List Op := [.save 269 270 1577, .save 268 1577 1578, .save 267 1578 1579, .save 266 1579 1580, .save 265 1580 1581, .save 264 1581 1582, .save 263 1582 1583, .save 262 1583 1584, .save 261 1584 1585, .save 260 1585 1586, .save 259 1586 1587, .save 258 1587 1588]
def select : List Op := [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593, .save 1567 1578 1594, .save 1568 270 1595]
def cross : List Op := [.mix 1576 408 1716, .mix 1562 409 1716, .mix 1563 410 1716, .mix 1564 411 1716, .mix 1565 412 1716, .mix 1566 413 1716, .mix 1567 414 1716, .mix 1568 415 1716, .mix 1569 416 1716, .mix 1570 417 1716, .mix 1571 418 1716, .mix 1572 419 1716, .mix 1573 420 1716, .mix 1574 421 1716, .mix 1575 422 1716, .mix 1560 423 1716]
def sign : List Op := [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596, .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596, .xor 1560 1596]
def product : List Op := [.save 1716 1596 1597]

def prepare := far ++ zero ++ suffix ++ select ++ cross ++ sign ++ product
def retire := (product.reverse ++ sign ++ select.reverse ++ suffix.reverse ++ zero)
def prepareInv := zero.reverse ++ suffix ++ select ++ sign.reverse ++ product
def retireInv := prepare.reverse

theorem prepared : ((leave240.drop 275).take 59) = prepare.map Op.enter := by rfl

theorem retired : ((leave240.drop 2325).take 37) = retire.map Op.exit := by rfl

theorem preparedInv : ((leave240Inv.drop 1028).take 37) = prepareInv.map Op.enter := by rfl

theorem retiredInv : ((leave240Inv.drop 3056).take 59) = retireInv.map Op.exit := by rfl

theorem hitsInv : ((leave240Inv.drop 998).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retireHits : ((leave240.drop 2362).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

/-- Symbols refer to initial physical wires. Constant folding is justified pointwise. -/
inductive Expr where
  | bit (v : Bool)
  | wire (w : Wire)
  | both (a b : Expr)
  | xor (a b : Expr)
deriving DecidableEq

def Expr.read (v : BasisState) : Expr → Bool
  | .bit b => b
  | .wire w => v w
  | .both a b => a.read v && b.read v
  | .xor a b => a.read v ^^ b.read v

def conj : Expr → Expr → Expr
  | .bit true,b => b
  | .bit false,_ => .bit false
  | a,.bit true => a
  | _,.bit false => .bit false
  | a,b => .both a b

private def xor0 : Expr → Expr → Expr
  | .bit false,b => b
  | a,.bit false => a
  | .bit a,.bit b => .bit (a ^^ b)
  | a,b => .xor a b

def xor (a b : Expr) := if a=b then .bit false else xor0 a b

theorem read_conj (v : BasisState) (a b : Expr) :
    (conj a b).read v=(a.read v && b.read v) := by
  cases a <;> cases b <;> simp [conj,Expr.read] <;> split <;> simp_all [Expr.read]
theorem read_xor (v : BasisState) (a b : Expr) :
    (xor a b).read v=(a.read v ^^ b.read v) := by
  unfold xor; split
  · subst b; simp [Expr.read]
  · cases a <;> cases b <;> simp [xor0,Expr.read] <;> split <;> simp_all [Expr.read]

def Sym := Wire → Expr
def symbolic (o : Op) (g : Sym) : Sym := fun q =>
  if q=o.dst then xor (g q) (match o with
    | .xor a _ => g a
    | .mix a b _ | .save a b _ => conj (g a) (g b)) else g q
def sim (os : List Op) (g : Sym) := os.foldl (fun a o => symbolic o a) g

theorem interpreted (v : BasisState) (os : List Op) (g : Sym) :
    (fun q => (sim os g q).read v)=trace os (fun q => (g q).read v) := by
  induction os generalizing g with
  | nil => rfl
  | cons o os ih =>
    change (fun q => (sim os (symbolic o g) q).read v)=trace os (o.step (fun q => (g q).read v))
    rw [ih]; congr 1
    funext q
    by_cases h:q=o.dst
    · subst q; cases o <;> simp [symbolic,Op.step,writeBit,read_xor,read_conj,Op.val,Op.dst]
    · simp [symbolic,Op.step,writeBit,h]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open Arithmetic RecordedQuantum

private theorem integer_ticks (L : SkywalkIntegerLayout) (hv : L.Valid) :
    GatePhysical (skywalkIntegerTick L) ∧ GatePhysical (skywalkIntegerUntick L) := by
  have enough : 1 ≤ L.half.length := by simp [SkywalkIntegerLayout.half]
  have narrow := narrowTicks_physical L 1 hv (by decide) enough
  simp only [narrowSkywalkTick, narrowSkywalkUntick, gatePhysical_append] at narrow
  obtain ⟨⟨⟨⟨route, half⟩, _⟩, prev⟩, ⟨⟨⟨⟨_, _⟩, _⟩, cx⟩, sw⟩⟩ := narrow
  have nd := L.record_nodup hv
  have fresh := (List.nodup_cons.mp nd).1
  have sx : L.ext ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.half]
  have sy : L.bSign ≠ L.history := by
    intro e
    apply fresh
    rw [← e]
    simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.bh]
  have toggle : GatePhysical (skywalkSignToggle L.ext L.bSign L.history) := by
    simp [skywalkSignToggle, GatePhysical, PhysicalInstr, ProperGate, sx, sy]
  have arithmetic := signedWords_physical L.history L.half L.b L.carry nd
  simp only [skywalkIntegerTick, skywalkIntegerUntick, signedRecord, signedUnrecord,
    gatePhysical_append]
  exact ⟨⟨⟨⟨route, half⟩, ⟨⟨toggle, arithmetic.1⟩, toggle⟩⟩, prev⟩,
    ⟨⟨⟨⟨prev, ⟨⟨toggle, arithmetic.2⟩, toggle⟩⟩, half⟩, cx⟩, sw⟩⟩

theorem route (j : Fin 23) (a n : Nat) (h : a+n ≤ 15) :
    GatePhysical (routed j a n) ∧ GatePhysical (unrouted j a n) := by
  induction n generalizing a with
  | zero => simp [routed, unrouted, GatePhysical]
  | succ n ih =>
    have ha : a < 15 := by omega
    have valid := IntegerPacket.ok (shape j) ⟨a, ha⟩
    have tick := integer_ticks (IntegerPacket.ports (shape j) a) valid
    have range := (shape j).rangeEnd
    change start j + 15 ≤ 510 at range
    have inj := OB5.sig_injective (start j+a) (by omega)
    have tail := ih (a+1) (by omega)
    exact ⟨(gatePhysical_append _ _).2 ⟨gatePhysical_rename _ inj _ tick.1, tail.1⟩,
      (gatePhysical_append _ _).2 ⟨tail.2, gatePhysical_rename _ inj _ tick.2⟩⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalBorrow
open Arithmetic

def restore (xs ys cs:List Wire) (long t:Wire) :=
  (copyRegister (some long) xs ys).reverse ++ PortalUnitInverse.emit ys cs t

private theorem wrap_back (a b t:Wire) (p r:Program) (s:State) (m tape:List Bool)
    (nd:[a,b,t].Nodup) (clean:s.basis t=false)
    (pres:∀ ms,(run p ms (prep a b t s)).basis t=
        ((run p ms (prep a b t s)).basis b && (run p ms (prep a b t s)).basis a))
    (undo:∀ x y,run r y (run p x (prep a b t s))=prep a b t s) :
    run (wrap a b t r) tape (run (wrap a b t p) m s)=s := by
  obtain ⟨ab,at0,bt⟩:a≠b ∧ a≠t ∧ b≠t:=by simpa [and_assoc] using nd
  let pre:Program:=[.X a,.CCX b a t]
  let post:Program:=[.measureX t [] [.CZ b a],.X a]
  have prepRun (x:List Bool):run pre x s=prep a b t s:=by
    simp [pre,prep,run,writeBit,ab.symm,at0.symm,clean]
  have decode (x y:List Bool) (v:State) (h:v.basis t=(v.basis b && v.basis a)):
      run pre y (run post x v)=v:=by
    change run [.X a,.CCX b a t] y (run [.X a] (x.drop 1) (run [.measureX t [] [.CZ b a]] x v))=_
    rw [PortalAnd.measure_and _ _ _ _ _ bt at0 h]
    apply congrArg (State.mk v.phase)
    funext q
    by_cases qa:q=a <;> by_cases qt:q=t <;> simp_all [run,writeBit,Function.update,ab.symm]
  have close (x:List Bool):run post x (prep a b t s)=s:=by
    change run [.X a] (x.drop 1) (run [.measureX t [] [.CZ b a]] x (prep a b t s))=_
    rw [PortalAnd.measure_and _ _ _ _ _ bt at0 (by simp [prep,writeBit,ab.symm,at0,bt])]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qa:q=a <;> by_cases qt:q=t <;> simp_all [prep,writeBit,Function.update]
  change run (pre++r++post) tape (run (pre++p++post) m s)=s
  simp only [run_append,run_take,prepRun]
  rw [decode _ _ _ (pres _),undo,close]

theorem erase_undo (a b t long:Wire) (xs ys cs:List Wire) (s:State) (m tape:List Bool)
    (L:Companion.Geometry xs ys cs long t) (distinct:[a,b,t,long].Nodup)
    (noA:a∉xs ∧ a∉ys ∧ a∉cs) (noB:b∉ys) (noT:t∉xs ∧ t∉ys ∧ t∉cs)
    (proper:ProperProgram (copyRegister (some long) xs ys))
    (fresh:s.basis t=false) (clean:∀q∈cs,s.basis q=false) :
    run (wrap a b t (restore xs ys cs long t)) tape (run (wrap a b t (Companion.erase xs ys cs long t)) m s)=s := by
  obtain ⟨ab,at0,al,bt,bl,tl⟩:a≠b ∧ a≠t ∧ a≠long ∧ b≠t ∧ b≠long ∧ t≠long := by simpa [and_assoc] using distinct
  let v:=prep a b t s
  have cv:∀q∈cs,v.basis q=false:=fun q h=>(outside (a:=a) (b:=b) (t:=t) s q (fun eq=>noA.2.2 (eq ▸ h))
    (fun eq=>noT.2.2 (eq ▸ h))).trans (clean _ h)
  apply wrap_back a b t _ _ s m tape (by simp [ab,at0,bt]) fresh
  · intro ms
    let w:=run (HighBankUnit.add ys cs t) ms v
    have mid:=HighBankUnit.add_correct ys cs t L.ripple L.carries v ms cv
    have cp:=copyRegister_correct (some long) xs ys L.limbs L.copy (by
      intro q h; obtain rfl:=Option.mem_some_iff.mp h; exact L.flag) w (ms.drop (measurementCount (HighBankUnit.add ys cs t)))
    simp only [Companion.erase,run_append,run_take]
    change (run _ _ w).basis t=((run _ _ w).basis b && (run _ _ w).basis a)
    rw [cp.2.1 t noT.2.1,cp.2.1 b noB,cp.2.1 a noA.2.1]
    change (run _ ms v).basis t=((run _ ms v).basis b && (run _ ms v).basis a)
    rw [mid.2.1 t noT.2.1,mid.2.1 b noB,mid.2.1 a noA.2.1]
    simp [v,prep,writeBit,at0,ab.symm,bt]
  · intro x y
    simp only [Companion.erase,restore,run_append,run_take]
    rw [run_reverse_proper _ proper]
    exact PortalUnitInverse.undo ys cs t L.carries L.ripple _ _ _ cv
#print axioms erase_undo
end ECDSAAdd.Entrant.StairPacket.PortalBorrow

end

section

namespace ECDSAAdd.Entrant.StairPacket
set_option exponentiation.threshold 1024
open Arithmetic MappedCompressed

private theorem input_congr (L:SkywalkIntegerLayout) (a b:Int) (g:Bool) (s t:BasisState)
    (eq:∀q∈L.wires,s q=t q) (input:SkywalkIntegerInput L a b g t) :
    SkywalkIntegerInput L a b g s := by
  have av : signedRegValue L.a s=signedRegValue L.a t := by
    unfold signedRegValue
    exact congrArg _ (regValue_congr _ _ _ (by
      intro q hq
      apply eq
      simp only [SkywalkIntegerLayout.a,List.mem_cons] at hq
      simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]; tauto))
  have bv : signedRegValue L.b s=signedRegValue L.b t := by
    unfold signedRegValue
    exact congrArg _ (regValue_congr _ _ _ (by
      intro q hq
      apply eq
      simp only [SkywalkIntegerLayout.b,List.mem_cons] at hq
      simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]; tauto))
  have cv : regValue L.carry s=regValue L.carry t := regValue_congr _ _ _ (by
    intro q hq; apply eq; simp [SkywalkIntegerLayout.wires,hq])
  obtain ⟨la,lb,prev,ext,hist,carry⟩:=input
  exact ⟨av.trans la,bv.trans lb,(eq _ (by simp [SkywalkIntegerLayout.wires])).trans prev,
    (eq _ (by simp [SkywalkIntegerLayout.wires])).trans ext,
    (eq _ (by simp [SkywalkIntegerLayout.wires])).trans hist,cv.trans carry⟩

/-- These physical *released-width* arithmetic registers are read in the genuine
stock rolling state, after all earlier ordinary transcript encodings. -/
theorem original_input (d : Bool) (x p i : Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1)
    (hp:p<2^256) (hq:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p) (hi:i<512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) :
    let z:=SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    SkywalkIntegerInput (W.compactSkywalkTickLayout base i) z.a z.b z.g s.basis := by
  obtain ⟨raw,hraw,hs⟩:=stage
  apply input_congr _ _ _ _ _ raw.basis
  · intro q hq
    rw [hs]
    have dis:=Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i i (le_refl _) hi
    exact run_preserves_outside _ [] raw q (fun h=>Finset.disjoint_left.mp dis h (List.mem_toFinset.mpr hq))
  · exact W.compactSkywalkStage_local_input base base_pool_nodup x p i hp0 hx0 hpo hp hq hx hc hi raw hraw

theorem true_small (x p i : Nat) (hx:x<2^256) (hp:p<2^256) (hi:i≤512) :
    let z:=SkywalkNat.step^[i] (SkywalkNat.init x p)
    min z.u z.v < 2^((513-i)/2) := by
  dsimp only
  apply IntegerHigh.min_bound _ _ i
  · apply lt_of_le_of_lt (SkywalkNat.iter_product_bound i (SkywalkNat.init x p))
    change x*p<2^512
    calc x*p ≤ x*(2^256) := Nat.mul_le_mul_left _ (Nat.le_of_lt hp)
         _ < 2^256*2^256 := Nat.mul_lt_mul_of_pos_right hx (by positivity)
         _ = 2^512 := (pow_add (2:Nat) 256 256).symm
  · omega

#print axioms original_input
#print axioms true_small
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

structure Ports where
  g : Wire
  u : Wire
  crossing : Wire
  near : Wire

/-- 0 is inactive, 1 is the left rail, and 2+t is the right rail at wait t. -/
abbrev Mode := Fin 18
def right (k : Mode) := decide (2≤k.val)
def left (k : Mode) := decide (k.val=1)
def key (k : Mode) := k.val-2
def enabled (k : Mode) := decide (k.val≠0)
def hot (k : Mode) (i : Nat) := right k && decide (key k=i)

def crossing (p : Ports) (k : Mode) : Expr :=
  if enabled k then .wire (p.u+key k) else .bit false
def nearby (k : Mode) := enabled k && decide (key k<5)
def suffixExpr (p : Ports) (i : Nat) : Expr :=
  ((List.range 15).drop i).foldr (fun j rest => conj (.wire (p.g+j)) rest) (.bit true)
def signExpr (p : Ports) (k : Mode) : Expr :=
  if right k && decide (0<key k) then suffixExpr p (key k+key k) else .bit false

def start (p : Ports) (inv : Bool) (k : Mode) (q : Wire) : Expr :=
  if q=1559 then .bit (left k)
  else if q=1560 then .bit (hot k 15)
  else if 1561≤q ∧ q≤1575 then .bit (hot k (q-1561))
  else if 1576≤q ∧ q≤1597 then .bit false
  else if q=p.crossing then if inv then crossing p k else .bit false
  else if q=p.near then .bit (inv && nearby k)
  else .wire q

def controls (p : Ports) (k : Mode) := [Expr.bit (nearby k),crossing p k,signExpr p k,conj (crossing p k) (signExpr p k)]

def reads (p : Ports) (g : Sym) := [g p.near,g p.crossing,g 1596,g 1597]

private theorem fold_suffix (xs : List Nat) (p : Ports) (v : BasisState) :
    (xs.foldr (fun j rest => conj (.wire (p.g+j)) rest) (.bit true)).read v =
      xs.all (fun j => v (p.g+j)) := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [Expr.read,read_conj,ih]

def parityBits (p : Ports) (v : BasisState) := (List.range 15).map (fun j => v (p.g+j))
theorem sign_value (p : Ports) (k : Mode) (v : BasisState)
    (h : right k=true → IntegerHigh.lead (parityBits p v)=key k) :
    (signExpr p k).read v = (right k && IntegerHigh.negative (parityBits p v)) := by
  by_cases r : right k=true
  · simp only [signExpr,r,Bool.true_and,IntegerHigh.negative,h r]
    by_cases z : 0<key k
    · simp only [z,decide_true,if_true,Bool.true_and,suffixExpr,fold_suffix]
      unfold parityBits
      rw [←List.map_drop]
      rw [List.all_map]; rfl
    · simp [z,Expr.read]
  · simp_all [signExpr,Expr.read]

theorem positive_value (p : Ports) (v : BasisState) :
    IntegerHigh.negative (parityBits p v)=true ↔
    2^15 < IntegerHigh.valueBits (parityBits p v)+
      2^(IntegerHigh.lead (parityBits p v)+IntegerHigh.lead (parityBits p v)) := by
  simpa [parityBits] using IntegerHigh.selector (parityBits p v) (by simp [parityBits])

theorem physical (p : Ports) (os : List Op) (inv : Bool) (k : Mode)
    (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(start p inv k q).read v)
    (cert : reads p (sim os (start p inv k))=controls p k) :
    let out := run (os.map Op.enter) m s
    out.phase=s.phase ∧ out.basis p.near=nearby k ∧
    out.basis p.crossing=(crossing p k).read v ∧ out.basis 1596=(signExpr p k).read v ∧
    out.basis 1597=((crossing p k).read v && (signExpr p k).read v) := by
  rw [enter_run]; dsimp only
  have b := interpreted v os (start p inv k)
  rw [←show (fun q => (start p inv k q).read v)=s.basis from (funext input).symm] at *
  unfold reads controls at cert
  simp only [List.cons.injEq,and_true] at cert
  obtain ⟨a,c,d,e⟩ := cert
  have eq (q : Wire) := congrFun b q
  exact ⟨rfl,(eq _).symm.trans (congrArg (Expr.read v) a),
    (eq _).symm.trans (congrArg (Expr.read v) c),(eq _).symm.trans (congrArg (Expr.read v) d),
    (eq _).symm.trans ((congrArg (Expr.read v) e).trans (read_conj _ _ _))⟩

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem part0 : GatePhysical (portal225) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part1 : GatePhysical (enter225) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part2 : GatePhysical (routed ⟨10,by decide⟩ 0 1) := by
  exact (route ⟨10, by decide⟩ 0 1 (by decide)).1

theorem part3 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.packAtTick false 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part4 : GatePhysical (routed ⟨10,by decide⟩ 1 14) := by
  exact (route ⟨10, by decide⟩ 1 14 (by decide)).1

theorem part5 : GatePhysical (leave225) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part6 : GatePhysical (enter240) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part7 : GatePhysical (routed ⟨11,by decide⟩ 0 1) := by
  exact (route ⟨11, by decide⟩ 0 1 (by decide)).1

theorem part8 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.packAtTick false 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part9 : GatePhysical (archiveLoad240 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part10 : GatePhysical (routed ⟨11,by decide⟩ 1 14) := by
  exact (route ⟨11, by decide⟩ 1 14 (by decide)).1

theorem part11 : GatePhysical (leave240) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part12 : GatePhysical (enter255) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part13 : GatePhysical (routed ⟨12,by decide⟩ 0 1) := by
  exact (route ⟨12, by decide⟩ 0 1 (by decide)).1

theorem part14 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.packAtTick false 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part15 : GatePhysical (archiveLoad255 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part16 : GatePhysical (routed ⟨12,by decide⟩ 1 14) := by
  exact (route ⟨12, by decide⟩ 1 14 (by decide)).1

theorem part17 : GatePhysical (leave255) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part18 : GatePhysical (park270) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part19 : GatePhysical (portal270Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem part20 : GatePhysical (renameProgram (OB5.sig 270) (TickRanges.tick base 270)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact TickRanges.tick_physical base 270 (by decide) base_pool_nodup

theorem part21 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.packAtTick false 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part22 : GatePhysical (archiveLoad270 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part23 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.packAtTick true 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part24 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.packAtTick true 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part25 : GatePhysical (archiveLoad240 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part26 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.packAtTick true 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part27 : GatePhysical (archiveLoad255 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part28 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.packAtTick true 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part29 : GatePhysical (archiveLoad270 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part30 : GatePhysical (archiveRestore270 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part31 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick false 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part32 : GatePhysical (renameProgram (OB5.sig 270) (W.ReverseCarry.compactReceiverTick base 270)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact W.ReverseCarry.compactReceiverTick_physical base 270 (by decide) base_pool_nodup

theorem part33 : GatePhysical (portal270) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part34 : GatePhysical (park270Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part35 : GatePhysical (leave255Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part36 : GatePhysical (unrouted ⟨12,by decide⟩ 1 14) := by
  exact (route ⟨12, by decide⟩ 1 14 (by decide)).2

theorem part37 : GatePhysical (archiveRestore255 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part38 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick false 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part39 : GatePhysical (unrouted ⟨12,by decide⟩ 0 1) := by
  exact (route ⟨12, by decide⟩ 0 1 (by decide)).2

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem part40 : GatePhysical (enter255Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part41 : GatePhysical (leave240Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part42 : GatePhysical (unrouted ⟨11,by decide⟩ 1 14) := by
  exact (route ⟨11, by decide⟩ 1 14 (by decide)).2

theorem part43 : GatePhysical (archiveRestore240 false) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part44 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick false 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part45 : GatePhysical (unrouted ⟨11,by decide⟩ 0 1) := by
  exact (route ⟨11, by decide⟩ 0 1 (by decide)).2

theorem part46 : GatePhysical (enter240Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part47 : GatePhysical (leave225Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part48 : GatePhysical (unrouted ⟨10,by decide⟩ 1 14) := by
  exact (route ⟨10, by decide⟩ 1 14 (by decide)).2

theorem part49 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick false 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part50 : GatePhysical (unrouted ⟨10,by decide⟩ 0 1) := by
  exact (route ⟨10, by decide⟩ 0 1 (by decide)).2

theorem part51 : GatePhysical (enter225Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part52 : GatePhysical (portal225Inv) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part53 : GatePhysical (archiveRestore270 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part54 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick true 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part55 : GatePhysical (archiveRestore255 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part56 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick true 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part57 : GatePhysical (archiveRestore240 true) := by
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part58 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick true 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

theorem part59 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick true 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 401 402 1557 1556 1721 1722 946 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 403 948 1556 (PortalBorrow.restore bulkA bulkB carry 1722 1556)
theorem emitted_back : Partial.portal225Inv=store.reverse++backErase++backFlags++scan.reverse := by decide +kernel
theorem flags_spec : flags=PortalAnd.flags 401 402 1557 1556 1721 1722 946 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 403 948 1556 (Companion.erase bulkA bulkB carry 1722 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by decide +kernel)
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by decide +kernel)
def activeScratch : List Wire := [1557,1556,1721,1722,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 423 424 1557 1556 1698 1699 923 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 425 925 1556 (PortalBorrow.restore bulkA bulkB carry 1699 1556)
theorem emitted_back : Partial.portal270Inv=store.reverse++backErase++backFlags++scan.reverse := by decide +kernel
theorem flags_spec : flags=PortalAnd.flags 423 424 1557 1556 1698 1699 923 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 425 925 1556 (Companion.erase bulkA bulkB carry 1699 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by decide +kernel)
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by decide +kernel)
def activeScratch : List Wire := [1557,1556,1698,1699,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part55 : gateSlots (archiveRestore255 true) ≤ 3542 := by
  have move : gateSlots moveRestore255 = 54 := by decide +kernel
  simp only [archiveRestore255,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,integer_restore0_gateSlots,move]
  decide

theorem part56 : gateSlots (Rolling1588.unpackAtTick true 245) ≤ 166 := by decide +kernel

theorem part57 : gateSlots (archiveRestore240 true) ≤ 3542 := by
  have move : gateSlots moveRestore240 = 54 := by decide +kernel
  simp only [archiveRestore240,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,integer_restore0_gateSlots,move]
  decide

theorem part58 : gateSlots (Rolling1588.unpackAtTick true 230) ≤ 166 := by decide +kernel

theorem part59 : gateSlots (Rolling1588.unpackAtTick true 225) ≤ 166 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part20 : gateSlots (TickRanges.tick base 270) ≤ 6004 := by
  have h := TickRanges.tick_slots base 270 (by decide) base_pool_nodup
  have r := W.repairedTick_slots base 270 (by decide) base_pool_nodup
  have c := (W.compactTick_gateSlots_le base 270 (by decide)).1
  omega

theorem part21 : gateSlots (Rolling1588.packAtTick false 260) ≤ 156 := by decide +kernel

theorem part22 : gateSlots (archiveLoad270 false) ≤ 3288 := by
  have move : gateSlots moveLoad270 = 33 := by decide +kernel
  simp only [archiveLoad270,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,integer_load1_gateSlots,move]
  decide

theorem part23 : gateSlots (Rolling1588.packAtTick true 225) ≤ 168 := by decide +kernel

theorem part24 : gateSlots (Rolling1588.packAtTick true 230) ≤ 168 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

def checkExit (g : Sym) : Op → Bool
  | .save a b t => decide (t≠a ∧ t≠b ∧ g t=conj (g a) (g b))
  | _ => true

def erase (o : Op) (g : Sym) : Sym :=
  match o with
  | .save _ _ t => fun q => if q=t then .bit false else g q
  | _ => symbolic o g

def validExit : List Op → Sym → Bool
  | [],_ => true
  | o::os,g => checkExit g o && validExit os (erase o g)

def erased (os : List Op) (g : Sym) := os.foldl (fun s o => erase o s) g

theorem erase_one (v : BasisState) (g : Sym) (o : Op) (phase : Bool) (m : List Bool)
    (h : checkExit g o=true) :
    run [o.exit] m ⟨phase,fun q => (g q).read v⟩=⟨phase,fun q => (erase o g q).read v⟩ := by
  cases o with
  | save a b t =>
    obtain ⟨ta,tb,e⟩ : t≠a ∧ t≠b ∧ g t=conj (g a) (g b) := by simpa [checkExit] using h
    simp only [Op.exit,run]
    cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,Function.update,ta.symm,tb.symm,e,read_conj]
      <;> funext q <;> by_cases eq:q=t <;> simp [erase,Function.update,eq,Expr.read]
  | xor a t =>
    change run ([(Op.xor a t)].map Op.enter) m _=_
    rw [enter_run]; congr 1
    exact (interpreted v [.xor a t] g).symm
  | mix a b t =>
    change run ([(Op.mix a b t)].map Op.enter) m _=_
    rw [enter_run]; congr 1
    exact (interpreted v [.mix a b t] g).symm

theorem retired_run (v : BasisState) (g : Sym) (ops : List Op) (phase : Bool) (m : List Bool)
    (h : validExit ops g=true) :
    run (ops.map Op.exit) m ⟨phase,fun q => (g q).read v⟩ =
      ⟨phase,fun q => (erased ops g q).read v⟩ := by
  induction ops generalizing g m with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨hc,ht⟩ : checkExit g o=true ∧ validExit os (erase o g)=true := by simpa [validExit] using h
    change run ([o.exit] ++ os.map Op.exit) m _=_
    rw [run_append,run_take,erase_one _ _ _ _ _ hc]
    exact ih _ _ ht

/-- At forward retirement the word may have overwritten every u digit. Crossing
and the approach flag are independent stored bits at this boundary. -/
def post (p : Ports) (forward : List Op) (inv : Bool) (k : Mode) : Sym := fun q =>
  if !inv && decide (q=p.crossing ∨ q=p.near) then .wire q
  else if !inv && decide (q=1597) then conj (.wire p.crossing) (signExpr p k)
  else sim forward (start p false k) q

def restored (p : Ports) (inv : Bool) (k : Mode) : Sym := fun q =>
  if !inv && decide (q=p.crossing ∨ q=p.near) then .wire q
  else start p false k q

def affected (p : Ports) := (List.range' 1576 22) ++ [p.crossing,p.near]
def targetCert (p : Ports) (forward retiring : List Op) (inv : Bool) (k : Mode) :=
  let w := post p forward inv k
  validExit retiring w && (affected p).all (fun q => decide (erased retiring w q=restored p inv k q))

theorem unmodified (v : BasisState) (os : List Op) (g : Sym) (q : Wire)
    (h : ∀o∈os, q≠o.dst) : (erased os g q).read v=(g q).read v := by
  induction os generalizing g with
  | nil => rfl
  | cons o os ih =>
    have ho:=h o (by simp)
    change (erased os (erase o g) q).read v=_
    rw [ih _ (fun a ha => h a (by simp [ha]))]
    cases o <;> simp_all [erase,symbolic,Op.dst]


theorem sim_outside (os : List Op) (g : Sym) (q : Wire)
    (h : ∀o∈os, q≠o.dst) : sim os g q=g q := by
  induction os generalizing g with
  | nil => rfl
  | cons o os ih =>
    change sim os (symbolic o g) q=_
    rw [ih _ (fun a ha => h a (by simp [ha]))]
    simp [symbolic,h o (by simp)]

theorem cleanup (p : Ports) (forward retiring : List Op) (inv : Bool) (k : Mode)
    (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post p forward inv k q).read v)
    (cert : targetCert p forward retiring inv k=true)
    (foot : ∀o∈forward++retiring,o.dst∈affected p) :
    run (retiring.map Op.exit) m s=⟨s.phase,fun q => (restored p inv k q).read v⟩ := by
  obtain ⟨ok,targets⟩ := Bool.and_eq_true_iff.mp cert
  have initial : s=⟨s.phase,fun q => (post p forward inv k q).read v⟩ := congrArg₂ State.mk rfl (funext input)
  conv_lhs => rw [initial,retired_run v _ _ _ _ ok]
  apply congrArg₂ State.mk rfl; funext q
  by_cases owned:q∈affected p
  · exact congrArg (Expr.read v) (of_decide_eq_true (List.all_eq_true.mp targets q owned))
  · have dis (o : Op) (ho:o∈forward++retiring) : q≠o.dst := fun e=>owned (e ▸ foot o ho)
    rw [unmodified _ _ _ _ (fun o ho=>dis o (List.mem_append_right _ ho))]
    have tail : q≠1597 := fun e=>owned (e ▸ List.mem_append_left _ (by decide : 1597∈List.range' 1576 22))
    simp only [post,restored,tail,decide_false,Bool.and_false,Bool.false_eq_true,if_false]
    rw [sim_outside _ _ _ (fun o ho=>dis o (List.mem_append_left _ ho))]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit

set_option maxRecDepth 8000

abbrev tags (i : Nat) : Wire := 1561+i
def before (p : Ports) (inv : Bool) (k : Mode) (q : Wire) :=
  if q=1560 then Expr.bit (right k)
  else if 1561≤q ∧ q≤1575 then Expr.bit false
  else start p inv k q

theorem hits_ready (p : Ports) (inv : Bool) (k : Mode) (sw : Nat → Wire)
    (layout : Layout 1560 sw tags 0 15) (s : State) (v : BasisState) (m : List Bool)
    (input : ∀q,s.basis q=(before p inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k)) :
    let out := run (putAll 1560 sw tags 0 15) m s
    out.phase=s.phase ∧ ∀q,out.basis q=(start p inv k q).read v := by
  have clean (i : Nat) (_ : 0 ≤ i) (hi : i<0+15) : s.basis (tags i)=false := by
    rw [input]; simp [before,tags,show 1561+i≠1560 by omega,show 1561+i≤1575 by omega,Expr.read]
  obtain ⟨ph,side⟩ := put_frame layout s m clean
  refine ⟨ph,?_⟩
  have wk : s.basis 1560=right k := by rw [input]; simp [before,Expr.read]
  have cap : key k≤15 := by have h:=k.isLt; unfold key; omega
  by_cases live:right k=true
  · obtain ⟨w,h⟩ := one_hot layout s m (key k) (by simp [wk,live]) clean
        (fun i _ hi it => exchange live i hi it)
    intro q; change Nat at q
    by_cases we:q=1560
    · subst q; simpa [start,Expr.read,hot,live,show (15 ≤ key k) = (key k=15) by apply propext; omega] using w
    by_cases z:1561≤q ∧ q≤1575
    · have eq:tags (q-1561)=q:=by change 1561+(q-1561)=q; omega
      have hh:=h (q-1561) (by omega) (by omega)
      rw [eq] at hh
      simp only [start,if_neg (show q≠1559 by omega),if_neg we,if_pos z,Expr.read,hot,live,Bool.true_and]; rw [hh]; exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact eq_comm)
    · rw [side _ we (fun i _ hi e => z (by change q=1561+i at e; omega))]
      simpa [before,we,z] using input q
  · have off:right k=false:=Bool.eq_false_iff.mpr live
    rw [inactive layout s m (wk.trans off) clean]
    intro q; change Nat at q; rw [input]; unfold before
    by_cases we:q=1560
    · subst q; simp [start,hot,off]
    by_cases z:1561≤q ∧ q≤1575
    · simp [we,z,start,show q≠1559 by omega,hot,off]
    · simp [we,z]

theorem hits_retired (k : Mode) (sw : Nat → Wire) (layout : Layout 1560 sw tags 0 15)
    (dis : ∀i<15,∀j<15,sw i≠tags j) (s : State) (m : List Bool)
    (waiting : s.basis 1560=hot k 15) (hs : ∀i<15,s.basis (tags i)=hot k i)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k)) :
    run (dropAll 1560 sw tags 0 15) m s =
      if right k then ⟨s.phase,retireBasis 1560 tags 15 true s.basis⟩ else s := by
  by_cases live:right k=true
  · simp only [live,if_true]; apply retire_selected layout _ _ dis (key k)
    · have cap : key k≤15 := by have h:=k.isLt; unfold key; omega
      simpa [hot,live,show (key k=15) = (15 ≤ key k) by apply propext; omega] using waiting
    · intro i hi; simpa [hot,live,eq_comm] using hs i hi
    · exact exchange live
  · have off:right k=false:=Bool.eq_false_iff.mpr live
    simp only [off,Bool.false_eq_true,if_false]
    exact retire_inactive layout _ _ (by simpa [hot,off] using waiting)
      (fun i hi=>by simpa [hot,off] using hs i hi)

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialPhysical
open Arithmetic MappedCompressed Partial

attribute [local irreducible] GatePhysical

theorem forward45plus1_physical (d : Bool) : GatePhysical (forward45plus1 d) := by
  cases d
  · simp only [forward45plus1, gatePhysical_append, and_assoc]
    exact ⟨part0, part1, part2, part3, part4, part5, part6, part7, part8, part9, part10, part11, part12, part13, part14, part15, part16, part17, part18, part19, part20, part21, part22⟩
  · simp only [forward45plus1, gatePhysical_append, and_assoc]
    exact ⟨part0, part1, part2, part23, part4, part5, part6, part7, part24, part25, part10, part11, part12, part13, part26, part27, part16, part17, part18, part19, part20, part28, part29⟩

theorem reverse45plus1_physical (d : Bool) : GatePhysical (reverse45plus1 d) := by
  cases d
  · simp only [reverse45plus1, gatePhysical_append, and_assoc]
    exact ⟨part30, part31, part32, part33, part34, part35, part36, part37, part38, part39, part40, part41, part42, part43, part44, part45, part46, part47, part48, part49, part50, part51, part52⟩
  · simp only [reverse45plus1, gatePhysical_append, and_assoc]
    exact ⟨part53, part54, part32, part33, part34, part35, part36, part55, part56, part39, part40, part41, part42, part57, part58, part45, part46, part47, part48, part59, part50, part51, part52⟩

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1723 (by decide +kernel) (by decide +kernel)
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 401 402 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 946 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1721 f) 1722 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags_run
  · decide +kernel
  · decide +kernel
  · decide
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags_undo
  · decide +kernel
  · decide +kernel
  · decide
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem erase_return (s:State) (m n:List Bool) (h:s.basis 1556=false ∧ ∀q∈carry,s.basis q=false) :
    run backErase n (run erase m s)=s := by
  rw [erase_spec]
  apply PortalBorrow.erase_undo
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PortalStatic.proper _ (by decide +kernel)
  · exact h.1
  · exact h.2
theorem portal_return (s:State) (m tape:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run Partial.portal225Inv tape (run Partial.portal225 m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1721 ∧ q≠1722 := by decide +kernel
    constructor
    · simpa [writeBit] using vh 1556 (by decide +kernel)
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]
#print axioms portal_return
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1700 (by decide +kernel) (by decide +kernel)
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 423 424 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 923 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1698 f) 1699 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags_run
  · decide +kernel
  · decide +kernel
  · decide
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags_undo
  · decide +kernel
  · decide +kernel
  · decide
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · exact h _ (by decide +kernel)
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem erase_return (s:State) (m n:List Bool) (h:s.basis 1556=false ∧ ∀q∈carry,s.basis q=false) :
    run backErase n (run erase m s)=s := by
  rw [erase_spec]
  apply PortalBorrow.erase_undo
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PortalStatic.proper _ (by decide +kernel)
  · exact h.1
  · exact h.2
theorem portal_return (s:State) (m tape:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run Partial.portal270Inv tape (run Partial.portal270 m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1698 ∧ q≠1699 := by decide +kernel
    constructor
    · simpa [writeBit] using vh 1556 (by decide +kernel)
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]
#print axioms portal_return
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem forward45plus1_false_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 2030 → x1 ≤ 93 → x2 ≤ 5000 → x3 ≤ 156 → x4 ≤ 70000 → x5 ≤ 3489 → x6 ≤ 93 → x7 ≤ 5000 → x8 ≤ 156 → x9 ≤ 3288 → x10 ≤ 70000 → x11 ≤ 3704 → x12 ≤ 93 → x13 ≤ 5000 → x14 ≤ 156 → x15 ≤ 3288 → x16 ≤ 70000 → x17 ≤ 3837 → x18 ≤ 9 → x19 ≤ 2219 → x20 ≤ 6004 → x21 ≤ 156 → x22 ≤ 3288 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 257059 := by omega

theorem forward45plus1_false : gateSlots (forward45plus1 false) ≤ 257059 := by
  simp only [forward45plus1,gateSlots_append,rename_gateSlots]
  exact forward45plus1_false_sum (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) part0 part1 part2 part3 part4 part5 part6 part7 part8 part9 part10 part11 part12 part13 part14 part15 part16 part17 part18 part19 part20 part21 part22

private theorem forward45plus1_true_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 2030 → x1 ≤ 93 → x2 ≤ 5000 → x3 ≤ 168 → x4 ≤ 70000 → x5 ≤ 3489 → x6 ≤ 93 → x7 ≤ 5000 → x8 ≤ 168 → x9 ≤ 3278 → x10 ≤ 70000 → x11 ≤ 3704 → x12 ≤ 93 → x13 ≤ 5000 → x14 ≤ 168 → x15 ≤ 3278 → x16 ≤ 70000 → x17 ≤ 3837 → x18 ≤ 9 → x19 ≤ 2219 → x20 ≤ 6004 → x21 ≤ 168 → x22 ≤ 3278 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 257077 := by omega

theorem forward45plus1_true : gateSlots (forward45plus1 true) ≤ 257077 := by
  simp only [forward45plus1,gateSlots_append,rename_gateSlots]
  exact forward45plus1_true_sum (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) part0 part1 part2 part23 part4 part5 part6 part7 part24 part25 part10 part11 part12 part13 part26 part27 part16 part17 part18 part19 part20 part28 part29

private theorem reverse45plus1_false_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 3562 → x1 ≤ 154 → x2 ≤ 6001 → x3 ≤ 2219 → x4 ≤ 9 → x5 ≤ 3838 → x6 ≤ 70000 → x7 ≤ 3562 → x8 ≤ 154 → x9 ≤ 5000 → x10 ≤ 93 → x11 ≤ 3705 → x12 ≤ 70000 → x13 ≤ 3562 → x14 ≤ 154 → x15 ≤ 5000 → x16 ≤ 93 → x17 ≤ 3490 → x18 ≤ 70000 → x19 ≤ 154 → x20 ≤ 5000 → x21 ≤ 93 → x22 ≤ 2030 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 257873 := by omega

theorem reverse45plus1_false : gateSlots (reverse45plus1 false) ≤ 257873 := by
  simp only [reverse45plus1,gateSlots_append,rename_gateSlots]
  exact reverse45plus1_false_sum (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) part30 part31 part32 part33 part34 part35 part36 part37 part38 part39 part40 part41 part42 part43 part44 part45 part46 part47 part48 part49 part50 part51 part52

private theorem reverse45plus1_true_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 3542 → x1 ≤ 166 → x2 ≤ 6001 → x3 ≤ 2219 → x4 ≤ 9 → x5 ≤ 3838 → x6 ≤ 70000 → x7 ≤ 3542 → x8 ≤ 166 → x9 ≤ 5000 → x10 ≤ 93 → x11 ≤ 3705 → x12 ≤ 70000 → x13 ≤ 3542 → x14 ≤ 166 → x15 ≤ 5000 → x16 ≤ 93 → x17 ≤ 3490 → x18 ≤ 70000 → x19 ≤ 166 → x20 ≤ 5000 → x21 ≤ 93 → x22 ≤ 2030 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 257861 := by omega

theorem reverse45plus1_true : gateSlots (reverse45plus1 true) ≤ 257861 := by
  simp only [reverse45plus1,gateSlots_append,rename_gateSlots]
  exact reverse45plus1_true_sum (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) part53 part54 part32 part33 part34 part35 part36 part55 part56 part39 part40 part41 part42 part57 part58 part45 part46 part47 part48 part59 part50 part51 part52

end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open LeaveSelector
def ports : Ports := ⟨241,401,1724,1725⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by decide +kernel
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by decide +kernel
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by decide +kernel
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open LeaveSelector
def ports : Ports := ⟨256,408,1716,1717⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by decide +kernel
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by decide +kernel
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by decide +kernel
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

def ofFlags (far initialU : Bool) (w : Fin 16) : Mode :=
  if far then if initialU then 1 else ⟨2+w.val,by omega⟩ else 0

theorem mode_flags (far initialU : Bool) (w : Fin 16) :
    left (ofFlags far initialU w)=(far && initialU) ∧
    right (ofFlags far initialU w)=(far && !initialU) ∧
    (far && !initialU=true → key (ofFlags far initialU w)=w.val) := by
  cases far <;> cases initialU <;> simp [left,right,key,ofFlags]; omega

def flagOps (far u : Wire) (inv : Bool) : List Op :=
  [.save far u 1559] ++ (if inv then [.xor 1559 1560,.xor far 1560] else [.xor far 1560,.xor 1559 1560])

def flagUpdate (far u : Wire) (v : BasisState) : BasisState := fun q =>
  if q=1559 then v far && v u else if q=1560 then v far && !v u else v q

theorem flag_prepare (far u : Wire) (inv : Bool) (s : State) (m : List Bool)
    (fa : far≠1559) (fb : far≠1560)
    (a : s.basis 1559=false) (b : s.basis 1560=false) :
    run ((flagOps far u inv).map Op.enter) m s=⟨s.phase,flagUpdate far u s.basis⟩ := by
  apply congrArg₂ State.mk (by cases inv <;> rfl)
  funext q
  by_cases l : q=1559 <;> by_cases w : q=1560 <;> cases inv <;>
    cases f : s.basis far <;> cases z : s.basis u <;>
      simp_all [Op.enter,run,flagUpdate,writeBit,Function.update]

theorem flag_retire (far u : Wire) (inv : Bool) (s : State) (v : BasisState) (m : List Bool)
    (fa : far≠1559) (fb : far≠1560) (uA : u≠1559) 
    (a : v 1559=false) (b : v 1560=false)
    (input : s.basis=flagUpdate far u v) :
    run ((flagOps far u inv).reverse.map Op.exit) m s=⟨s.phase,v⟩ := by
  let base : State := ⟨s.phase,v⟩
  have h:=flag_prepare far u inv base [] fa fb a b
  rw [enter_run] at h
  have matchS : s=⟨base.phase,trace (flagOps far u inv) base.basis⟩ :=
    (congrArg₂ State.mk rfl input).trans h.symm
  conv_lhs => rw [matchS]
  apply exit_run
  cases inv <;> simp [base,Safe,Op.safe,Op.args,Op.dst,flagOps,a,Ne.symm fa,Ne.symm fb,Ne.symm uA]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum IntegerHigh SkywalkNat

private theorem raw_before_first (xs : List Nat) (i : Nat) (hi : i<xs.length) (early : i≤xs.idxOf 2) :
    decide (xs[i]=2)=decide (i=xs.idxOf 2) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    by_cases hit:x=2
    · subst x
      simp at early
      subst i; simp
    · cases i with
      | zero => simp [hit]
      | succ i =>
        simp [hit] at early ⊢
        have hh:=ih i (by simpa using hi) early
        simpa using hh

private theorem len (n : Nat) (z : SkywalkNat.State) : (letters n z).length=n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [letters,ih]

/-- The physical swap tape may contain any later exchanges. Only the prefix
through the selected swap participates in the one-hot and retirement proofs. -/
theorem raw_exchange (B small : Nat) (ready : guard 15 small≤B)
    (v : BasisState) (sw : Nat→Wire)
    (records : ∀i : Fin 15, v (sw i)=decide ((letters 15 ⟨small,B⟩)[i.val]'(by rw [len]; exact i.isLt)=2)) :
    ∀i<15,i≤wait 15 small → v (sw i)=decide (i=wait 15 small) := by
  intro i hi early
  have h:=first_exchange 15 B small ready
  rw [←h] at early ⊢
  exact (records ⟨i,hi⟩).trans (raw_before_first _ _ (by simpa only [len] using hi) early)

theorem raw_negative (p : Ports) (B small : Nat) (ready : guard 15 small≤B)
    (v : BasisState) (k : Mode) (waitKey : right k=true → key k=wait 15 small)
    (record : parityBits p v=oddBits (letters 15 ⟨small,B⟩)) :
    (signExpr p k).read v = (right k && negative (oddBits (letters 15 ⟨small,B⟩))) := by
  rw [sign_value p k v (fun r => by rw [record,lead_wait _ _ _ ready,waitKey r]),record]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

/-- Reverse reconstruction uses the saved physical crossing and proximity bits.
The later shadow operand is unconstrained; the stored crossing was computed
from the earlier shadow, before the forward word transform. -/
def inverseCert (p : Ports) (forward back : List Op) (k : Mode) :=
  (affected p).all (fun q => decide (sim back (restored p false k) q = post p forward false k q))

theorem recover (p : Ports) (forward back : List Op) (k : Mode) (s : State) (m : List Bool)
    (v : BasisState) (input : ∀q,s.basis q=(restored p false k q).read v)
    (cert : inverseCert p forward back k=true)
    (foot : ∀o∈forward++back,o.dst∈affected p) :
    run (back.map Op.enter) m s = ⟨s.phase,fun q => (post p forward false k q).read v⟩ := by
  rw [enter_run]; apply congrArg₂ State.mk rfl
  rw [funext input,←interpreted]; funext q
  by_cases own:q∈affected p
  · exact congrArg (Expr.read v) (of_decide_eq_true (List.all_eq_true.mp cert q own))
  · have dis (o : Op) (ho:o∈forward++back) : q≠o.dst := fun e=>own (e ▸ foot o ho)
    rw [sim_outside _ _ _ (fun o h=>dis o (List.mem_append_right _ h))]
    have tail : q≠1597 := fun e=>own (e ▸ List.mem_append_left _ (by decide : 1597∈List.range' 1576 22))
    simp only [post,restored,tail,decide_false,Bool.and_false,Bool.false_eq_true,if_false]
    rw [sim_outside _ _ _ (fun o h=>dis o (List.mem_append_left _ h))]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

def parityAt (q : Wire) : Program → Option Bool
  | [] => some false
  | .X t::is => if q=t then (parityAt q is).map Bool.not else parityAt q is
  | .CX _ t::is | .CCX _ _ t::is | .measureX t _ _::is => if q=t then none else parityAt q is

theorem polarity (q : Wire) (is : Program) (b : Bool) (h : parityAt q is=some b)
    (s : State) (m : List Bool) :
    (run is m s).basis q=(s.basis q ^^ b) := by
  induction is generalizing b s m with
  | nil => simp [parityAt] at h; subst b; simp [run]
  | cons g is ih =>
    cases g with
    | X t =>
      by_cases eq:q=t
      · subst q; simp only [parityAt,if_true] at h
        cases v:parityAt t is with
        | none => simp [v] at h
        | some x =>
          have bx : (!x)=b := by simpa [v] using h
          simp only [run]; rw [ih x v]; simp [writeBit,←bx]
      · simp only [parityAt,if_neg eq] at h
        simp only [run]; rw [ih _ h]; simp [writeBit,eq]
    | CX a t | CCX _ a t | measureX t _ _ =>
      by_cases eq:q=t
      · simp [parityAt,eq] at h
      · simp only [parityAt,if_neg eq] at h
        simp only [run]; rw [ih _ h]; simp [measureAndCorrect,writeBit,eq]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open Arithmetic CodecBitSliceVerify StairArchiveGates StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

def op (loading select : Bool) : Operation :=
  if loading then (if select then .load0 else .load1) else (if select then .restore0 else .restore1)

def raw : Cols := integer_load0Trace0In.take 23
def code (select : Bool) : Cols :=
  (if select then integer_load0Trace5Out else integer_load1Trace5Out).take 16
def startCols (loading select:Bool) := if loading then raw else code select
def endCols (loading select:Bool) := if loading then code select else raw

theorem io (loading select:Bool) (i:Fin 157) :
    get (input (op loading select)) i=get (startCols loading select) i ∧
    get (output (op loading select)) i=get (endCols loading select) i := by
  revert i
  cases loading <;> cases select <;> decide +kernel

theorem blank (loading select:Bool) (i:Fin 157) (h : 23≤ i.val) :
    get (startCols loading select) i=0 ∧ get (endCols loading select) i=0 := by
  revert i
  cases loading <;> cases select <;> decide +kernel

end ECDSAAdd.Entrant.StairPacket.ArchivePortAction

end

section

namespace ECDSAAdd.Entrant.StairArchiveTrace
open SkywalkNat SkywalkRails StairArchiveRaw

def chain : Bool → List (Bool × Bool) → Prop
  | _, [] => True
  | u, v::vs => v.2 = (!u && !v.1) ∧ chain (u || !v.1) vs

theorem orientation {k : Nat} {z t : SkywalkNat.State} (h : IntegerHigh.Rel (k+1) z t) :
    decide (IntegerHigh.letter z=2) =
      (!decide (z.v<z.u) && !decide (IntegerHigh.letter z=0)) ∧
    decide ((SkywalkNat.step z).v < (SkywalkNat.step z).u) =
      (decide (z.v<z.u) || !decide (IntegerHigh.letter z=0)) := by
  cases h with
  | left B s D large =>
    have lb := IntegerHigh.guard_gt k s
    have lim : 2*IntegerHigh.guard k s+s≤B := by simpa [IntegerHigh.guard_succ] using large
    generalize big : B+2^(k+1)*D = x
    have guard : 3*s+2≤x := by omega
    by_cases even : x%2=0
    · simp [IntegerHigh.letter,SkywalkNat.step,show x≠0 by omega,even,show s<x by omega,
        show s<x/2 by omega]
    · simp [IntegerHigh.letter,SkywalkNat.step,show x≠0 by omega,even,show s<x by omega,
        show ¬x<s by omega,show s≤x by omega,show s<(x-s)/2 by omega]
  | right B s D large =>
    have lb := IntegerHigh.guard_gt k s
    have lim : 2*IntegerHigh.guard k s+s≤B := by simpa [IntegerHigh.guard_succ] using large
    generalize big : B+2^(k+1)*D = x
    have guard : 3*s+2≤x := by omega
    by_cases zero : s=0
    · subst s; simp [IntegerHigh.letter,SkywalkNat.step]
    · by_cases even : s%2=0
      · simp [IntegerHigh.letter,SkywalkNat.step,zero,even,show ¬x<s by omega,show ¬x<s/2 by omega]
      · simp [IntegerHigh.letter,SkywalkNat.step,zero,even,show ¬x<s by omega,show s<x by omega,
          show ¬x≤s by omega,show s<(x-s)/2 by omega]

theorem signed {k : Nat} {z t : SkywalkNat.State} (h : IntegerHigh.Rel k z t)
    (g sign : Bool) (pos : 0<z.v) (odd : z.v%2=1) :
    chain (decide (z.v<z.u)) (SkywalkTrace.trace k (encode g sign z.u z.v)) := by
  induction k generalizing z t g sign with
  | zero => trivial
  | succ n ih =>
    obtain ⟨neq,_⟩ := IntegerHigh.different h
    obtain ⟨_,tail⟩ := IntegerHigh.advance h
    obtain ⟨zp,zo⟩ := step_v_odd_pos z pos odd
    obtain ⟨record,orient⟩ := orientation h
    rw [SkywalkTrace.trace, IntegerHigh.recorded z g sign pos odd neq]
    simp only [chain,SkywalkTrace.next,step_reencode g sign z pos odd]
    exact ⟨record,orient ▸ ih tail _ _ zp zo⟩

def afterFlags (u : Bool) (xs : List (Bool × Bool)) := xs.foldl (fun v bit => v || !bit.1) u

theorem suffix (n : Nat) (xs : List (Bool × Bool)) (u : Bool) (valid : chain u xs) :
    chain (afterFlags u (xs.take n)) (xs.drop n) := by
  induction n generalizing xs u with
  | zero => exact valid
  | succ n ih =>
    cases xs with
    | nil => trivial
    | cons h t => exact ih t _ valid.2

theorem chain_bits (xs : List (Bool × Bool)) (u : Bool) (h : chain u xs) (i : Nat) (hi : i<xs.length) :
    (read xs i).2 = (!u && !(read xs i).1 && (List.range i).all (fun k => (read xs k).1)) := by
  induction xs generalizing u i with
  | nil => simp at hi
  | cons c xs ih =>
    cases i with
    | zero => simpa only [StairArchiveRaw.read,List.getElem?_cons_zero,Option.getD_some,List.range_zero,
        List.all_nil,Bool.and_true] using h.1
    | succ i =>
      have rest := ih (u || !c.1) h.2 i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)
      rw [List.range_succ_eq_map, List.all_cons, List.all_map]
      change (read xs i).2 = (!u && !(read xs i).1 && (c.1 && (List.range i).all (fun k => (read xs k).1)))
      rw [rest]
      cases u <;> cases cc : c.1 <;> simp

theorem legal_signed (n : Nat) (z : SkywalkNat.State) (g sign : Bool) (pos : 0<z.v) (odd : z.v%2=1) :
    legal (SkywalkTrace.trace n (encode g sign z.u z.v)) := by
  induction n generalizing z g sign with
  | zero => simp [legal, SkywalkTrace.trace]
  | succ n ih =>
    obtain ⟨zp,zo⟩ := step_v_odd_pos z pos odd
    have current := SkywalkTrace.code_classified g sign z pos odd
    have first : SkywalkTrace.code (encode g sign z.u z.v) ≠ (true,true) := by
      intro bad
      rw [bad] at current
      have even : z.u%2=0 := of_decide_eq_true current.1.symm
      exact Bool.noConfusion (current.2.1 even)
    intro event mem
    rw [SkywalkTrace.trace, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact first
    · rw [SkywalkTrace.next, step_reencode g sign z pos odd] at mem
      exact (ih _ _ _ zp zo) event mem

theorem far_suffix (pre : Nat) {z t : SkywalkNat.State} (h : IntegerHigh.Rel (pre+10) z t)
    (g sign cross : Bool) (pos : 0<z.v) (odd : z.v%2=1) :
    let all := SkywalkTrace.trace (pre+10) (encode g sign z.u z.v)
    let xs := all.drop pre
    let u := afterFlags (decide (z.v<z.u)) (all.take pre)
    ∃ row<63145, ∀ q<23, (rawCol q).testBit row = rawBit (read xs) true u cross q := by
  let all := SkywalkTrace.trace (pre+10) (encode g sign z.u z.v)
  have len : (all.drop pre).length=10 := by
    simp only [all, List.length_drop, SkywalkTrace.trace_length]; omega
  apply list_member _ len
  · simp
  · intro _ i hi
    exact chain_bits _ _ (suffix pre all _ (signed h g sign pos odd)) i (by omega)

theorem near_suffix (pre : Nat) (z : SkywalkNat.State) (g sign : Bool) (pos : 0<z.v) (odd : z.v%2=1) :
    let all := SkywalkTrace.trace (pre+10) (encode g sign z.u z.v)
    let xs := all.drop pre
    ∃ row<63145, ∀ q<23, (rawCol q).testBit row = rawBit (read xs) false false false q := by
  let all := SkywalkTrace.trace (pre+10) (encode g sign z.u z.v)
  have len : (all.drop pre).length=10 := by
    simp only [all, List.length_drop, SkywalkTrace.trace_length]; omega
  apply list_member _ len
  · intro _
    exact ⟨fun x hx => legal_signed (pre+10) z g sign pos odd x (List.mem_of_mem_drop hx), rfl, rfl⟩
  · simp

end ECDSAAdd.Entrant.StairArchiveTrace

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave225Hit Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

def program (inv : Bool) := if inv then leave225Inv else leave225
def initPC (inv : Bool) := if inv then 932 else 242
def retirePC (inv : Bool) := if inv then 2858 else 2190
def beforeWord (inv : Bool) := ((program inv).drop (initPC inv+33)).take (if inv then 37 else 59)
def afterWord (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 59 else 37)

theorem flags (inv : Bool) : ((program inv).drop (initPC inv)).take 3 =
    (flagOps 1721 1722 inv).map Op.enter := by cases inv <;> rfl


theorem firstHit (inv : Bool) : ((program inv).drop (initPC inv+3)).take 30 =
    putAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact written
  · exact hitsInv

theorem lastHit (inv : Bool) : ((program inv).drop (retirePC inv+(if inv then 59 else 37))).take 30 =
    dropAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact retireHits
  · exact Leave225Hit.retired

theorem separate (i : Nat) (hi:i<15) (j : Nat) (hj:j<15) : swaps i≠LeaveSelector.tags j := by
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by decide +kernel
  exact cert ⟨i,hi⟩ ⟨j,hj⟩

theorem execute (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(LeaveSelector.start ports inv k q).read v) :
    let out := run (beforeWord inv) m s
    out.phase=s.phase ∧ out.basis 1725=nearby k ∧
    out.basis 1724=(crossing ports k).read v ∧ out.basis 1596=(signExpr ports k).read v ∧
    out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  cases inv
  · exact physical ports prepare false k s m v input (controlCert k)
  · exact physical ports prepareInv true k s m v input (controlInvCert k)

theorem clear (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v) :
    run (afterWord inv) m s=⟨s.phase,fun q => (restored ports inv k q).read v⟩ := by
  cases inv
  · apply cleanup ports prepare retire false k s m v input (cleanCert k)
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)


end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave240Hit Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

def program (inv : Bool) := if inv then leave240Inv else leave240
def initPC (inv : Bool) := if inv then 995 else 242
def retirePC (inv : Bool) := if inv then 3056 else 2325
def beforeWord (inv : Bool) := ((program inv).drop (initPC inv+33)).take (if inv then 37 else 59)
def afterWord (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 59 else 37)

theorem flags (inv : Bool) : ((program inv).drop (initPC inv)).take 3 =
    (flagOps 1713 1714 inv).map Op.enter := by cases inv <;> rfl


theorem firstHit (inv : Bool) : ((program inv).drop (initPC inv+3)).take 30 =
    putAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact written
  · exact hitsInv

theorem lastHit (inv : Bool) : ((program inv).drop (retirePC inv+(if inv then 59 else 37))).take 30 =
    dropAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact retireHits
  · exact Leave240Hit.retired

theorem separate (i : Nat) (hi:i<15) (j : Nat) (hj:j<15) : swaps i≠LeaveSelector.tags j := by
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by decide +kernel
  exact cert ⟨i,hi⟩ ⟨j,hj⟩

theorem execute (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(LeaveSelector.start ports inv k q).read v) :
    let out := run (beforeWord inv) m s
    out.phase=s.phase ∧ out.basis 1717=nearby k ∧
    out.basis 1716=(crossing ports k).read v ∧ out.basis 1596=(signExpr ports k).read v ∧
    out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  cases inv
  · exact physical ports prepare false k s m v input (controlCert k)
  · exact physical ports prepareInv true k s m v input (controlInvCert k)

theorem clear (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v) :
    run (afterWord inv) m s=⟨s.phase,fun q => (restored ports inv k q).read v⟩ := by
  cases inv
  · apply cleanup ports prepare retire false k s m v input (cleanCert k)
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)


end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum IntegerHigh SkywalkNat

/-- Input g=even and s=exchange are the two components of the recorded raw
three-way event. The physical selector reads g after the packet's parity flips. -/
theorem history_words (p : Ports) (sw : Nat→Wire) (xs : List Nat) (hx : xs.length=15)
    (b v : BasisState)
    (source : ∀i : Fin 15, b (p.g+i)=decide (xs[i.val]'(by rw [hx]; exact i.isLt)=0) ∧
        b (sw i)=decide (xs[i.val]'(by rw [hx]; exact i.isLt)=2))
    (cut : ∀i : Fin 15, v (p.g+i)= !b (p.g+i) ∧ v (sw i)=b (sw i)) :
    parityBits p v=oddBits xs ∧ ∀i : Fin 15,v (sw i)=decide (xs[i.val]'(by rw [hx]; exact i.isLt)=2) := by
  constructor
  · apply List.ext_getElem
    · simp [parityBits,oddBits,hx]
    · intro i hi hj
      have lt:i<15:=by simpa [parityBits] using hi
      obtain ⟨g,_⟩:=cut ⟨i,lt⟩
      obtain ⟨src,_⟩:=source ⟨i,lt⟩
      simp only [parityBits,oddBits,List.getElem_map,List.getElem_range]
      rw [show v (p.g+i)= !b (p.g+i) from g,show b (p.g+i)=decide (xs[i]'(by omega)=0) from src]
      simp
  · intro i; exact (cut i).2.trans (source i).2

def farMode (far u : Bool) (s : Nat) : Mode := ofFlags far u ⟨wait 15 s,by have h:=wait_le 15 s; omega⟩

theorem initialized (p : Ports) (inv : Bool) (far u : Wire) (s : State) (v : BasisState) (m : List Bool)
    (small : Nat) (fa : far≠1559) (fb : far≠1560)
    (a : s.basis 1559=false) (b : s.basis 1560=false)
    (rest : ∀q,q≠1559 → q≠1560 → s.basis q=(before p inv (farMode (s.basis far) (s.basis u) small) q).read v) :
    let k:=farMode (s.basis far) (s.basis u) small
    let out:=run ((flagOps far u inv).map Op.enter) m s
    out.phase=s.phase ∧ ∀q,out.basis q=(before p inv k q).read v := by
  rw [flag_prepare _ _ _ _ _ fa fb a b]; dsimp only
  obtain ⟨l,r,_⟩:=mode_flags (s.basis far) (s.basis u) ⟨wait 15 small,by have h:=wait_le 15 small; omega⟩
  refine ⟨rfl,?_⟩; intro q
  by_cases ql:q=1559
  · subst q; simp [before,start,flagUpdate,Expr.read,farMode,l]
  by_cases qr:q=1560
  · subst q; simp [before,flagUpdate,Expr.read,farMode,r]
  · simpa [flagUpdate,ql,qr] using rest q ql qr

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open Arithmetic CodecBitSliceVerify StairArchiveGates StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private theorem of_member {P:Program} {g:Instr} {q:Wire} (inP:g∈P) (hit:q∈g.wires) : q∈wires P := by
  induction P with
  | nil => simp at inP
  | cons h t ih =>
    rw [wires,Finset.mem_union]
    rcases List.mem_cons.mp inP with rfl|tail
    · exact Or.inl hit
    · exact Or.inr (ih tail)

private def marks : Bool → Bool → List Nat
  | false, false => [1, 2, 6, 11, 16, 31, 36, 41, 46, 47, 51, 56, 61, 324, 306, 315, 1189, 1196, 1205, 1217, 1229, 1243, 1248]
  | false, true => [1, 2, 6, 11, 16, 31, 36, 41, 46, 47, 51, 56, 61, 324, 306, 315, 1183, 1192, 1203, 1214, 1230, 1244, 1249]
  | true, false => [1, 2, 3, 4, 11, 12, 42, 49, 44, 51, 123, 124, 125, 126, 133, 134, 164, 171, 166, 173, 334, 245, 246]
  | true, true => [42, 49, 44, 51, 10, 11, 1, 2, 3, 4, 164, 171, 166, 173, 132, 133, 123, 124, 125, 126, 334, 245, 246]

private theorem marked (loading select:Bool) : ∀i:Fin 23,
    ((program (op loading select))[(marks loading select).getD i 0]?).any
      (fun g => decide (i.val ∈ g.wires))=true := by
  cases loading <;> cases select <;> decide +kernel

theorem prefix_touched (loading select:Bool) : Finset.range 23 ⊆ wires (program (op loading select)) := by
  intro q hq
  have good:=marked loading select ⟨q,Finset.mem_range.mp hq⟩
  generalize eh : (program (op loading select))[(marks loading select).getD q 0]? = v at *
  cases v with
  | none => simp at good
  | some g =>
    exact of_member (List.mem_of_getElem? eh) (of_decide_eq_true good)

end ECDSAAdd.Entrant.StairPacket.ArchivePortAction

end

section

namespace ECDSAAdd.Entrant.StairArchiveTrace
open SkywalkRails StairArchiveRaw

def observed (p : IntegerPacket.Shape) (i pre : Nat) (m : List Bool) (s : State) :=
  IntegerPacket.readCells p i (pre+10) (run (IntegerPacket.seq p i (pre+10)) m s).basis

theorem real_far (p : IntegerPacket.Shape) (i pre : Nat) (bound : i+(pre+10)≤p.length)
    {z t : SkywalkNat.State} (large : IntegerHigh.Rel (pre+10) z t) (g sign cross : Bool)
    (pos : 0<z.v) (odd : z.v%2=1) (m : List Bool) (s : State)
    (ready : IntegerPacket.ready p i (encode g sign z.u z.v) s.basis) :
    let all := observed p i pre m s
    let xs := all.drop pre
    let u := afterFlags (decide (z.v<z.u)) (all.take pre)
    ∃ row<63145, ∀ q<23, (rawCol q).testBit row = rawBit (read xs) true u cross q := by
  have hp := encode_odd_sum g sign (z.u : Int) (z.v : Int) (by omega)
  have eq := (IntegerPacket.records p i (pre+10) bound _ hp s m ready).1
  dsimp only [observed]
  rw [eq]
  exact far_suffix pre large g sign cross pos odd

theorem real_near (p : IntegerPacket.Shape) (i pre : Nat) (bound : i+(pre+10)≤p.length)
    (z : SkywalkNat.State) (g sign : Bool) (pos : 0<z.v) (odd : z.v%2=1)
    (m : List Bool) (s : State) (ready : IntegerPacket.ready p i (encode g sign z.u z.v) s.basis) :
    let xs := (observed p i pre m s).drop pre
    ∃ row<63145, ∀ q<23, (rawCol q).testBit row = rawBit (read xs) false false false q := by
  have hp := encode_odd_sum g sign (z.u : Int) (z.v : Int) (by omega)
  have eq := (IntegerPacket.records p i (pre+10) bound _ hp s m ready).1
  dsimp only [observed]
  rw [eq]
  exact near_suffix pre z g sign pos odd

end ECDSAAdd.Entrant.StairArchiveTrace

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum LeaveSelector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
def rawPrefix (inv : Bool) := (program inv).take (initPC inv)
theorem historyShape : ∀ inv : Bool, ∀i : Fin 15,
    LeaveSelector.parityAt (ports.g+i) (rawPrefix inv)=some true ∧
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by decide +kernel

theorem history (inv : Bool) (i : Fin 15) (s : State) (m : List Bool) :
    let out:=run (rawPrefix inv) m s
    out.basis (ports.g+i)= !s.basis (ports.g+i) ∧ out.basis (swaps i)=s.basis (swaps i) := by
  obtain ⟨g,sw⟩:=historyShape inv i
  exact ⟨by simpa using polarity _ _ _ g s m,by simpa using polarity _ _ _ sw s m⟩
end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum LeaveSelector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
def rawPrefix (inv : Bool) := (program inv).take (initPC inv)
theorem historyShape : ∀ inv : Bool, ∀i : Fin 15,
    LeaveSelector.parityAt (ports.g+i) (rawPrefix inv)=some true ∧
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by decide +kernel

theorem history (inv : Bool) (i : Fin 15) (s : State) (m : List Bool) :
    let out:=run (rawPrefix inv) m s
    out.basis (ports.g+i)= !s.basis (ports.g+i) ∧ out.basis (swaps i)=s.basis (swaps i) := by
  obtain ⟨g,sw⟩:=historyShape inv i
  exact ⟨by simpa using polarity _ _ _ g s m,by simpa using polarity _ _ _ sw s m⟩
end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit IntegerHigh

def withHits (far u : Wire) (inv : Bool) (sw : Nat→Wire) (word : Program) : Program :=
  (flagOps far u inv).map Op.enter ++ (putAll 1560 sw tags 0 15 ++ word)

theorem assembled (p : Ports) (far u : Wire) (inv : Bool) (ops : List Op) (sw : Nat→Wire)
    (layout : Layout 1560 sw tags 0 15) (apart : ∀i<15,sw i≠1559 ∧ sw i≠1560)
    (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (fa : far≠1559) (fb : far≠1560) (a : s.basis 1559=false) (b : s.basis 1560=false)
    (k : Mode) (mode : k=farMode (s.basis far) (s.basis u) small)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before p inv k q).read v)
    (exchanges : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k))
    (cert : reads p (sim ops (start p inv k))=controls p k) :
    let out := run (withHits far u inv sw (ops.map Op.enter)) m s
    out.phase=s.phase ∧ out.basis p.near=nearby k ∧ out.basis p.crossing=(crossing p k).read v ∧
    out.basis 1596=(signExpr p k).read v ∧ out.basis 1597=((crossing p k).read v && (signExpr p k).read v) := by
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
  have hw:=physical p ops inv k r m'' v hh.2 cert
  simp only [withHits,run_append,run_take]
  exact ⟨hw.1.trans (hh.1.trans init.1),hw.2⟩

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end


section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open Arithmetic CodecBitSliceVerify StairArchiveGates StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

abbrev Ports := Fin 157 → Wire
def Frame (a : Ports) (cs:Cols) (row:Nat) (s:State) :=
  ∀ i, s.basis (a i)=(get cs i).testBit row

theorem piece (loading select:Bool) (ports:Ports) (f:Wire→Wire)
    (unique : Function.Injective ports)
    (placement : ∀ q, (h:q<width (op loading select)) → ∃ i:Fin 157, i.val=q ∧ f q=ports i)
    (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame ports (startCols loading select) row s) :
    let t:=run (placed f (op loading select)) m s
    t.phase=s.phase ∧ Frame ports (endCols loading select) row t ∧
      ∀q,(∀i,ports i≠q) → t.basis q=s.basis q := by
  let o := op loading select
  have locate (q:Wire) (hq:q∈wires (program o)) := placement q (Finset.mem_range.mp (sub o hq))
  have inj : ∀ a∈Finset.range (width o), ∀ b∈Finset.range (width o), f a=f b → a=b := by
    intro a ha b hb eq
    obtain ⟨i,rfl,hi⟩:=placement a (Finset.mem_range.mp ha)
    obtain ⟨j,rfl,hj⟩:=placement b (Finset.mem_range.mp hb)
    exact congrArg Fin.val (unique (hi.symm.trans (eq.trans hj)))
  have ⟨phase,inside,outside⟩:=placed_run f o row hr inj m s (by
    intro q hq; obtain ⟨i,rfl,hi⟩:=locate q hq; rw [hi,ready,(io loading select i).1])
  have away (q:Wire) (no:∀j∈wires (program o), f j≠q) : q∉wires (placed f o) := by
    rw [placed, renameProgram_support]
    simpa only [Finset.mem_image,not_exists,not_and] using no
  refine ⟨phase,?_,fun q no => outside q (away q (by
    intro j hj
    obtain ⟨i,_,eq⟩:=locate j hj
    rw [eq]; exact no i))⟩
  intro i
  by_cases h : i.val∈wires (program o)
  · obtain ⟨j,eq,fj⟩:=locate i h
    have ji:j=i:=Fin.ext eq
    subst j
    rw [←fj,inside _ h,(io loading select i).2]
  · have large : 23≤ i.val:=by
      by_contra! bad; exact h (prefix_touched loading select (Finset.mem_range.mpr bad))
    have outsideQ:=away (ports i) (by
      intro q hq eq
      obtain ⟨j,reg,fj⟩:=locate q hq
      have ji:=unique (fj.symm.trans eq)
      exact h (by simpa only [←reg,ji] using hq))
    rw [outside _ outsideQ,ready,(blank loading select i large).1,(blank loading select i large).2]

def moves (ps:List (Wire×Wire)) : Program := ps.flatMap fun ⟨a,b⟩ => swapBits a b
def backMap : List (Wire×Wire) → Wire → Wire
  | [], q => q
  | (a,b)::ps, q =>
    let j:=backMap ps q
    if j=a then b else if j=b then a else j

theorem moves_run (ps:List (Wire×Wire)) (fresh:∀p∈ps,p.1≠p.2) (s:State) (m:List Bool) :
    run (moves ps) m s=⟨s.phase,fun q=>s.basis (backMap ps q)⟩ := by
  induction ps generalizing s m with
  | nil => rfl
  | cons ab ps ih =>
    obtain ⟨a,b⟩:=ab
    have ne:a≠b:=fresh (a,b) (by simp)
    have head:run (swapBits a b) m s=⟨s.phase,fun q=>s.basis (if q=a then b else if q=b then a else q)⟩:=by
      apply congrArg (State.mk s.phase); funext q
      by_cases qa:q=a <;> by_cases qb:q=b <;> cases ha:s.basis a <;> cases hb:s.basis b <;>
        simp_all [writeBit,Function.update,Ne.symm ne]
    rw [show moves ((a,b)::ps)=swapBits a b++moves ps from rfl,run_append,run_take,head,
      ih (fun p hp=>fresh p (List.mem_cons_of_mem _ hp))]
    rfl

end ECDSAAdd.Entrant.StairPacket.ArchivePortAction

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit

def clearKey (v : BasisState) (q : Nat) := if 1559≤q ∧ q≤1575 then false else v q

private theorem isTag (q : Nat) : (∃i<15,q=tags i) ↔ 1561≤q ∧ q≤1575 := by
  change (∃i : Nat,i<15 ∧ q=1561+i) ↔ _
  constructor
  · rintro ⟨i,hi,eq⟩; change q=1561+i at eq; omega
  · intro h; exact ⟨q-1561,by omega,by omega⟩

theorem release_tags (far u : Nat) (inv : Bool) (k : Mode) (sw : Nat→Wire)
    (layout : Layout 1560 sw tags 0 15) (dis : ∀i<15,∀j<15,sw i≠tags j)
    (s : State) (m : List Bool) (f : 1575<far) (iU : 1575<u)
    (farLeft : s.basis 1559=(s.basis far && s.basis u))
    (farRight : right k=(s.basis far && !s.basis u))
    (waiting : s.basis 1560=hot k 15) (hs : ∀i<15,s.basis (tags i)=hot k i)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k)) :
    run (dropAll 1560 sw tags 0 15 ++ (flagOps far u inv).reverse.map Op.exit) m s =
      ⟨s.phase,clearKey s.basis⟩ := by
  rw [run_append,run_take,hits_retired _ _ layout dis _ _ waiting hs exchange]
  let base := clearKey s.basis
  have leftEq : s.basis 1559=(base far && base u) := by simpa [base,clearKey,show ¬far≤1575 by omega,show ¬u≤1575 by omega] using farLeft
  have rightEq : right k=(base far && ! base u) := by simpa [base,clearKey,show ¬far≤1575 by omega,show ¬u≤1575 by omega] using farRight
  have noL : ¬∃j<15,1559=tags j := by rw [isTag]; decide
  have fa : far≠(1559:Nat) := by omega
  have fb : far≠(1560:Nat) := by omega
  have ua : u≠(1559:Nat) := by omega
  by_cases on:right k=true
  · simp only [on,if_true]
    apply flag_retire far u inv _ base _ fa fb ua (by rfl) (by rfl)
    funext q; change Nat at q
    by_cases l:q=1559
    · subst q; simp only [retireBasis,flagUpdate,if_neg (by decide : (1559:Nat)≠1560),if_neg noL,if_true,leftEq]
    by_cases w:q=1560
    · subst q; simp [retireBasis,flagUpdate,←rightEq,on]
    · simp only [retireBasis,if_neg w,flagUpdate,if_neg l,isTag,base,clearKey]
      by_cases h:1561≤q ∧ q≤1575
      · simp [h,show 1559≤q ∧ q≤1575 by omega]
      · simp [h,show ¬(1559≤q ∧ q≤1575) by omega]
  · have off:right k=false:=Bool.eq_false_iff.mpr on
    simp only [off,Bool.false_eq_true,if_false]
    apply flag_retire far u inv s base _ fa fb ua (by rfl) (by rfl)
    funext q; change Nat at q
    by_cases l:q=1559
    · subst q; simpa [flagUpdate] using leftEq
    by_cases w:q=1560
    · subst q; simpa [flagUpdate,←rightEq,hot,off] using waiting
    by_cases h:1561≤q ∧ q≤1575
    · obtain ⟨i,hi,e⟩:=(isTag q).2 h
      have z:=hs i hi; rw [←e] at z
      simpa [flagUpdate,l,w,base,clearKey,show 1559≤q ∧ q≤1575 by omega,hot,off] using z
    · simp [flagUpdate,l,w,base,clearKey,show ¬(1559≤q ∧ q≤1575) by omega]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open CodecBitSliceVerify StairArchiveIntegerHook

theorem state_eq {s t:State} (phase:s.phase=t.phase) (basis:∀q,s.basis q=t.basis q) : s=t := by
  cases s; cases t; exact congrArg₂ State.mk phase (funext basis)

theorem injective_list (xs:List Wire) (len:xs.length=157) (hn:xs.Nodup) :
    Function.Injective (fun i:Fin 157 => xs.getD i 0) := by
  intro i j h
  change xs.getD i 0=xs.getD j 0 at h
  rw [List.getD_eq_getElem _ _ (by rw [len]; exact i.isLt),
    List.getD_eq_getElem _ _ (by rw [len]; exact j.isLt)] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hn).mp h)

theorem end_blank (loading select:Bool) (i:Fin 157)
    (h:(if loading then 16 else 23) ≤ i.val) : get (endCols loading select) i=0 := by
  revert i
  cases loading <;> cases select <;> decide +kernel

theorem backMap_outside (ps:List (Wire×Wire)) (q:Wire)
    (no:∀p∈ps,q≠p.1 ∧ q≠p.2) : backMap ps q=q := by
  induction ps with
  | nil => rfl
  | cons ab ps ih =>
    obtain ⟨a,b⟩:=ab
    have noPair:=no (a,b) (by simp)
    simp only [backMap,ih (fun p h=>no p (List.mem_cons_of_mem _ h)),
      if_neg noPair.1,if_neg noPair.2]

theorem packet (loading select:Bool) (src dst : Ports) (f:Wire→Wire) (ps:List (Wire×Wire))
    (perm:Fin 157→Fin 157) (uniq:Function.Injective src)
    (placement : ∀ q, (h:q<width (op loading select)) → ∃ i:Fin 157, i.val=q ∧ f q=src i)
    (proper:∀p∈ps,p.1≠p.2)
    (route:∀i,backMap ps (dst i)=src (perm i))
    (sort:∀i, perm i=i ∨ ((if loading then 16 else 23)≤ i.val ∧ (if loading then 16 else 23)≤ (perm i).val))
    (scope:∀p∈ps,(∃i,src i=p.1) ∧ (∃i,src i=p.2))
    (row:Nat) (hr:row<63145) (s:State) (m:List Bool) (ready:Frame src (startCols loading select) row s) :
    let t:=run (placed f (op loading select) ++ moves ps) m s
    t.phase=s.phase ∧ Frame dst (endCols loading select) row t ∧
      ∀q,(∀i,src i≠q) → t.basis q=s.basis q := by
  obtain ⟨phase,all,away⟩:=piece loading select src f uniq placement row hr s m ready
  simp only [run_append,run_take,moves_run ps proper]
  refine ⟨phase,?_,?_⟩
  · intro i
    change (run _ m s).basis (backMap ps (dst i)) = _
    rw [route,all]
    rcases sort i with eq|⟨i0,p0⟩
    · rw [eq]
    · rw [end_blank _ _ _ i0,end_blank _ _ _ p0]
  · intro q no
    rw [backMap_outside ps q (by
      intro p hp; obtain ⟨⟨i,ri⟩,⟨j,rj⟩⟩:=scope p hp
      exact ⟨fun eq=>no i (ri.trans eq.symm),fun eq=>no j (rj.trans eq.symm)⟩)]
    exact away _ no

end ECDSAAdd.Entrant.StairPacket.ArchivePortAction

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit

def witnesses (far u : Wire) (sw : Nat→Wire) (k : Mode) (v : Sym) : Prop :=
  v far=Expr.wire far ∧ v u=Expr.wire u ∧ v 1559=Expr.bit (left k) ∧
  v 1560=Expr.bit (hot k 15) ∧ ∀i : Fin 15,v (tags i)=Expr.bit (hot k i) ∧ v (sw i)=Expr.wire (sw i)
instance (far u : Wire) (sw : Nat→Wire) (k : Mode) (v : Sym) : Decidable (witnesses far u sw k v) := by
  unfold witnesses; infer_instance

theorem full_release (far u : Nat) (sw : Nat→Wire) (layout : Layout 1560 sw tags 0 15)
    (dis : ∀i<15,∀j<15,sw i≠tags j) (f:1575<far) (iU:1575<u) (inv : Bool) (k : Mode)
    (s : State) (m : List Bool) (v : BasisState) (s0 : Sym) (after : Program)
    (first : run after m s=⟨s.phase,fun q=>(s0 q).read v⟩)
    (ports : witnesses far u sw k s0)
    (l : left k=(v far && v u)) (r : right k=(v far && !v u))
    (exchange : right k=true → ∀i<15,i≤key k → v (sw i)=decide (i=key k)) :
    run (after++(dropAll 1560 sw tags 0 15 ++ (flagOps far u inv).reverse.map Op.exit)) m s=
      ⟨s.phase,clearKey (fun q=>(s0 q).read v)⟩ := by
  obtain ⟨pF,pU,pL,pR,rows⟩:=ports
  rw [run_append,run_take,first]
  apply release_tags far u inv k sw layout dis _ _ f iU
  · simpa only [pL,pF,pU,Expr.read] using l
  · simpa only [pF,pU,Expr.read] using r
  · simp only [pR,Expr.read]
  · intro i hi; simp only [(rows ⟨i,hi⟩).1,Expr.read]
  · intro on i hi early; simpa only [(rows ⟨i,hi⟩).2,Expr.read] using exchange on i hi early

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary240
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [246,1274,247,1275,248,1276,249,1277,250,1278,251,1279,252,1280,253,1281,254,1282,255,1283,1716,1717,1718,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [246,1274,247,1275,248,249,1277,250,251,1279,252,1280,253,254,1282,255,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1276,1278,1281,1283,1716,1717,1718]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [246,1274,247,1275,248,1276,249,1277,250,1278,251,1279,252,1280,253,1281,254,1282,255,1283,1716,1717,1718,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := [(249,1276),(1277,1276),(250,1276),(251,1276),(1279,1278),(252,1276),(1280,1278),(253,1276),(254,1278),(1282,1276),(255,1281)]
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : Partial.archiveLoad240 d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
theorem load_unique : Function.Injective rawPorts := by exact injective_list rawPortsList (by decide +kernel) (by decide +kernel)
theorem load_map : ∀q:Fin 155, loadMap q=rawPorts ⟨q,by omega⟩ := by decide +kernel
theorem load_route : ∀i,backMap loadMoves (codePorts i)=rawPorts (loadRoute i) := by decide +kernel
theorem load_sort : ∀ i, loadRoute i=i ∨ (16≤ i.val ∧ 16≤(loadRoute i).val) := by decide +kernel
theorem load_scope : ∀p∈loadMoves,(∃i,rawPorts i=p.1) ∧ (∃i,rawPorts i=p.2) := by decide +kernel
theorem load_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame rawPorts (startCols true d) row s) :
    let t:=run (Partial.archiveLoad240 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by decide +kernel) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [246,1274,247,1275,248,249,1277,250,251,1279,252,1280,253,254,1282,255,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1276,249),(249,1277),(1277,250),(250,251),(1278,1279),(251,252),(1279,1280),(252,253),(1280,254),(253,1282),(1281,255),(254,1556),(1282,1557),(255,1558),(1283,1559),(1716,1560),(1717,1561),(1718,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore240 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
theorem restore_unique : Function.Injective codePorts := by exact injective_list codePortsList (by decide +kernel) (by decide +kernel)
theorem restore_map : ∀q:Fin 150, restoreMap q=codePorts ⟨q,by omega⟩ := by decide +kernel
theorem restore_route : ∀i,backMap restoreMoves (rawPorts i)=codePorts (restoreRoute i) := by decide +kernel
theorem restore_sort : ∀ i, restoreRoute i=i ∨ (23≤ i.val ∧ 23≤(restoreRoute i).val) := by decide +kernel
theorem restore_scope : ∀p∈restoreMoves,(∃i,codePorts i=p.1) ∧ (∃i,codePorts i=p.2) := by decide +kernel
theorem restore_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame codePorts (startCols false d) row s) :
    let t:=run (Partial.archiveRestore240 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by decide +kernel) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by decide +kernel
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run (Partial.archiveRestore240 d) n (run (Partial.archiveLoad240 d) m s)=s := by
  have f:=load_run d row hr s m ready
  have b:=restore_run d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃i,rawPorts i=q
    · obtain ⟨i,rfl⟩:=h
      exact (b.2.1 i).trans (ready i).symm
    · have no:∀i,rawPorts i≠q:=fun i eq=>h ⟨i,eq⟩
      have noc:∀i,codePorts i≠q:=by
        intro i; obtain ⟨j,eq⟩:=code_from_raw i
        exact eq ▸ no j
      exact (b.2.2 q noc).trans (f.2.2 q no)
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary240

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary255
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [261,1289,262,1290,263,1291,264,1292,265,1293,266,1294,267,1295,268,1296,269,1297,270,1298,1709,1710,1711,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [261,1289,262,1290,263,264,1292,265,266,1294,267,1295,268,269,1297,270,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1291,1293,1296,1298,1709,1710,1711]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [261,1289,262,1290,263,1291,264,1292,265,1293,266,1294,267,1295,268,1296,269,1297,270,1298,1709,1710,1711,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := [(264,1291),(1292,1291),(265,1291),(266,1291),(1294,1293),(267,1291),(1295,1293),(268,1291),(269,1293),(1297,1291),(270,1296)]
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : Partial.archiveLoad255 d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
theorem load_unique : Function.Injective rawPorts := by exact injective_list rawPortsList (by decide +kernel) (by decide +kernel)
theorem load_map : ∀q:Fin 155, loadMap q=rawPorts ⟨q,by omega⟩ := by decide +kernel
theorem load_route : ∀i,backMap loadMoves (codePorts i)=rawPorts (loadRoute i) := by decide +kernel
theorem load_sort : ∀ i, loadRoute i=i ∨ (16≤ i.val ∧ 16≤(loadRoute i).val) := by decide +kernel
theorem load_scope : ∀p∈loadMoves,(∃i,rawPorts i=p.1) ∧ (∃i,rawPorts i=p.2) := by decide +kernel
theorem load_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame rawPorts (startCols true d) row s) :
    let t:=run (Partial.archiveLoad255 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by decide +kernel) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [261,1289,262,1290,263,264,1292,265,266,1294,267,1295,268,269,1297,270,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1291,264),(264,1292),(1292,265),(265,266),(1293,1294),(266,267),(1294,1295),(267,268),(1295,269),(268,1297),(1296,270),(269,1556),(1297,1557),(270,1558),(1298,1559),(1709,1560),(1710,1561),(1711,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore255 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
theorem restore_unique : Function.Injective codePorts := by exact injective_list codePortsList (by decide +kernel) (by decide +kernel)
theorem restore_map : ∀q:Fin 150, restoreMap q=codePorts ⟨q,by omega⟩ := by decide +kernel
theorem restore_route : ∀i,backMap restoreMoves (rawPorts i)=codePorts (restoreRoute i) := by decide +kernel
theorem restore_sort : ∀ i, restoreRoute i=i ∨ (23≤ i.val ∧ 23≤(restoreRoute i).val) := by decide +kernel
theorem restore_scope : ∀p∈restoreMoves,(∃i,codePorts i=p.1) ∧ (∃i,codePorts i=p.2) := by decide +kernel
theorem restore_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame codePorts (startCols false d) row s) :
    let t:=run (Partial.archiveRestore255 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by decide +kernel) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by decide +kernel
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run (Partial.archiveRestore255 d) n (run (Partial.archiveLoad255 d) m s)=s := by
  have f:=load_run d row hr s m ready
  have b:=restore_run d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃i,rawPorts i=q
    · obtain ⟨i,rfl⟩:=h
      exact (b.2.1 i).trans (ready i).symm
    · have no:∀i,rawPorts i≠q:=fun i eq=>h ⟨i,eq⟩
      have noc:∀i,codePorts i≠q:=by
        intro i; obtain ⟨j,eq⟩:=code_from_raw i
        exact eq ▸ no j
      exact (b.2.2 q noc).trans (f.2.2 q no)
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary255

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary270
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [276,1809,277,1808,278,1807,279,1806,280,1805,281,1804,282,1803,283,1802,284,1801,285,1800,1029,1030,1031,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [276,1809,277,1808,278,279,1806,280,281,1804,282,1803,283,284,1801,285,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1807,1805,1802,1800,1029,1030,1031]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [276,1809,277,1808,278,1807,279,1806,280,1805,281,1804,282,1803,283,1802,284,1801,285,1800,1029,1030,1031,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := [(279,1807),(1806,1807),(280,1807),(281,1807),(1804,1805),(282,1807),(1803,1805),(283,1807),(284,1805),(1801,1807),(285,1802)]
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : Partial.archiveLoad270 d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
theorem load_unique : Function.Injective rawPorts := by exact injective_list rawPortsList (by decide +kernel) (by decide +kernel)
theorem load_map : ∀q:Fin 155, loadMap q=rawPorts ⟨q,by omega⟩ := by decide +kernel
theorem load_route : ∀i,backMap loadMoves (codePorts i)=rawPorts (loadRoute i) := by decide +kernel
theorem load_sort : ∀ i, loadRoute i=i ∨ (16≤ i.val ∧ 16≤(loadRoute i).val) := by decide +kernel
theorem load_scope : ∀p∈loadMoves,(∃i,rawPorts i=p.1) ∧ (∃i,rawPorts i=p.2) := by decide +kernel
theorem load_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame rawPorts (startCols true d) row s) :
    let t:=run (Partial.archiveLoad270 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by decide +kernel) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [276,1809,277,1808,278,279,1806,280,281,1804,282,1803,283,284,1801,285,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1807,279),(279,1806),(1806,280),(280,281),(1805,1804),(281,282),(1804,1803),(282,283),(1803,284),(283,1801),(1802,285),(284,1556),(1801,1557),(285,1558),(1800,1559),(1029,1560),(1030,1561),(1031,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore270 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
theorem restore_unique : Function.Injective codePorts := by exact injective_list codePortsList (by decide +kernel) (by decide +kernel)
theorem restore_map : ∀q:Fin 150, restoreMap q=codePorts ⟨q,by omega⟩ := by decide +kernel
theorem restore_route : ∀i,backMap restoreMoves (rawPorts i)=codePorts (restoreRoute i) := by decide +kernel
theorem restore_sort : ∀ i, restoreRoute i=i ∨ (23≤ i.val ∧ 23≤(restoreRoute i).val) := by decide +kernel
theorem restore_scope : ∀p∈restoreMoves,(∃i,codePorts i=p.1) ∧ (∃i,codePorts i=p.2) := by decide +kernel
theorem restore_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame codePorts (startCols false d) row s) :
    let t:=run (Partial.archiveRestore270 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by decide +kernel) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by decide +kernel
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run (Partial.archiveRestore270 d) n (run (Partial.archiveLoad270 d) m s)=s := by
  have f:=load_run d row hr s m ready
  have b:=restore_run d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃i,rawPorts i=q
    · obtain ⟨i,rfl⟩:=h
      exact (b.2.1 i).trans (ready i).symm
    · have no:∀i,rawPorts i≠q:=fun i eq=>h ⟨i,eq⟩
      have noc:∀i,codePorts i≠q:=by
        intro i; obtain ⟨j,eq⟩:=code_from_raw i
        exact eq ▸ no j
      exact (b.2.2 q noc).trans (f.2.2 q no)
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary270

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open CodecBitSliceVerify StairArchiveGates StairArchiveRaw
theorem starting_frame (a:Ports) (s:State) (row:Nat) (data:Nat→Bool)
    (matchRow:∀q<23,(rawCol q).testBit row=data q)
    (rawBits:∀i:Fin 157,i.val<23 → s.basis (a i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (a i)=false) :
    Frame a raw row s := by
  intro i
  by_cases low:i.val<23
  · rw [rawBits i low,←matchRow _ low]
    exact congrArg (fun x:Nat=>x.testBit row) (io true true i).1
  · have big:23≤ i.val:=by omega
    rw [scratch i big]
    rw [show get raw i=0 from (blank true true i big).1]
    simp

theorem field_bits (select:Bool) (i:Fin 16) :
    get (code select) i = get (if select then enter0Trace0In else enter1Trace0In) i := by
  revert i
  cases select <;> decide +kernel
end ECDSAAdd.Entrant.StairPacket.ArchivePortAction
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary240
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run (Partial.archiveLoad240 d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then enter0Trace0In else enter1Trace0In) i).testBit row) ∧
        (∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run (Partial.archiveRestore240 d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame rawPorts s row data h recorded scratch
  have ⟨ph,fr,away⟩:=load_run d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip d row hr s m tape ready⟩
  intro i
  exact (fr ⟨i,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d i))
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary240
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary255
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run (Partial.archiveLoad255 d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then enter0Trace0In else enter1Trace0In) i).testBit row) ∧
        (∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run (Partial.archiveRestore255 d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame rawPorts s row data h recorded scratch
  have ⟨ph,fr,away⟩:=load_run d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip d row hr s m tape ready⟩
  intro i
  exact (fr ⟨i,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d i))
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary255
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary270
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run (Partial.archiveLoad270 d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then enter0Trace0In else enter1Trace0In) i).testBit row) ∧
        (∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run (Partial.archiveRestore270 d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame rawPorts s row data h recorded scratch
  have ⟨ph,fr,away⟩:=load_run d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip d row hr s m tape ready⟩
  intro i
  exact (fr ⟨i,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d i))
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary270

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Partial Arithmetic MappedCompressed StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def domain (q : Nat) := (236 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1042) || (1264 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1798) || (1799 ≤ q && q ≤ 1812)

def Covered (P : Program) : Prop := ∀ q ∈ wires P, domain q = true

theorem covered_append {P Q : Program} (a : Covered P) (b : Covered Q) : Covered (P ++ Q) := by
  intro q h
  rw [wires_append,Finset.mem_union] at h
  exact h.elim (a q) (b q)

theorem from_check {P : Program} (h : allSites domain P = true) : Covered P := allSites_sound h

private theorem interval0 : (List.range' 236 294).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval1 : (List.range' 786 257).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval2 : (List.range' 1264 37).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval3 : (List.range' 1556 243).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval4 : (List.range' 1799 14).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel

theorem valid {q : Wire} (h : domain q = true) : Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true := by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
  · exact List.all_eq_true.mp interval0 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval1 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval2 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval3 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval4 q (by simp only [List.mem_range'_1]; omega)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts
open Arithmetic MappedCompressed Stair44Resources StairConcreteAssembly StairArchiveInactive
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen StairArchiveGates
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount StairGroups.packet
  StairArchiveInactive.packet fieldHook

def distributed (d : Bool) (j n : Nat) :=
  PacketSequence.program d (StairArchiveInactive.packet d) j n
private theorem ren (f : Wire → Wire) (a b : Program) : renameProgram f (a++b)=renameProgram f a++renameProgram f b := List.map_append
theorem distribute (d : Bool) (j n : Nat) :
    StairHostsSchedule.hostedGroup hostPlan d 0 j n = distributed d j n := by
  change StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (PacketSequence.program d (StairGroups.packet d 0) j n)) = _
  simp only [hosts_eq,distributed,renameProgram_comp]
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,
      ren,ih,StairArchiveInactive.packet,hosts_eq,renameProgram_comp]

private theorem split (c : Cost) (d : Bool) (j n k : Nat) :
    c.measure (distributed d j (n+k)) =
    c.measure (distributed d j n) + c.measure (distributed d (j+n) k) := by
  unfold distributed
  induction n generalizing j with
  | zero =>
    simp only [Nat.zero_add,Nat.add_zero,PacketSequence.program]
    have z := c.append [] []
    simp only [List.nil_append] at z
    omega
  | succ n ih =>
    have rest := ih (j+1)
    have align : j+1+n=j+(n+1) := by omega
    rw [align] at rest
    cases d <;> simp only [Nat.succ_add,PacketSequence.program,Bool.false_eq_true,if_false,
      if_true,c.append] <;> omega

def group (d : Bool) (j n : Nat) := StairHostsSchedule.hostedGroup hostPlan d 0 j n

def ordered (d : Bool) (a b : Program) := if d then a++b else b++a

/-- The three suffixes of the integer windows 225, 240, 255 start at field ticks 230, 245, 260. -/
def group84 (d : Bool) : Program :=
  ordered d (group d 1 45) (ordered d (ten 46 (!d)) (ordered d (group d 48 1)
    (ordered d (ten 49 (!d)) (ordered d (group d 51 1)
      (ordered d (ten 52 (!d)) (group d 54 31))))))

private theorem ord (c : Cost) (d : Bool) (a b : Program) :
    c.measure (ordered d a b)=c.measure a+c.measure b := by
  cases d <;> simp [ordered,c.append,Nat.add_comm]

theorem overhead (j : Nat) (d : Bool) :
    toffoliCount (ten j (!d)) = toffoliCount (group d j 2)+208 ∧
    measurementCount (ten j (!d)) = measurementCount (group d j 2)+277 := by
  rw [group,distribute]
  cases d <;>
    simp only [distributed,PacketSequence.program,Bool.not_true,Bool.not_false,ten,first,second,
      enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
      List.append_nil,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,enter0_toffoliCount,switch0_toffoliCount,leave0_toffoliCount,
      enter1_toffoliCount,switch1_toffoliCount,leave1_toffoliCount,enter0_measurementCount,
      switch0_measurementCount,leave0_measurementCount,enter1_measurementCount,
      switch1_measurementCount,leave1_measurementCount] <;> constructor <;> omega

private theorem partition (c : Cost) (d : Bool) :
    c.measure (group d 1 84) = c.measure (group d 1 45)+c.measure (group d 46 2)+
      c.measure (group d 48 1)+c.measure (group d 49 2)+c.measure (group d 51 1)+
      c.measure (group d 52 2)+c.measure (group d 54 31) := by
  simp only [group,distribute]
  have a := split c d 1 45 39
  have b := split c d 46 2 37
  have e := split c d 48 1 36
  have f := split c d 49 2 34
  have g := split c d 51 1 33
  have h := split c d 52 2 31
  norm_num only [] at a b e f g h
  omega

theorem group_cost (d : Bool) :
    toffoliCount (group84 d) = toffoliCount (group d 1 84)+624 ∧
    measurementCount (group84 d) = measurementCount (group d 1 84)+831 := by
  have solve (c : Cost) (delta : Nat) (h : ∀j,c.measure (ten j (!d))=c.measure (group d j 2)+delta) :
      c.measure (group84 d) = c.measure (group d 1 84)+3*delta := by
    simp only [group84,ord,h,partition]
    omega
  exact ⟨solve tc 208 (fun j => (overhead j d).1),solve mc 277 (fun j => (overhead j d).2)⟩
/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d) = slots.measure (group d 1 84)+3*(if d then 6042 else 6053) := by
  have h (j : Nat) : slots.measure (ten j (!d)) =
      slots.measure (group d j 2)+(if d then 6042 else 6053) := by
    rw [show slots.measure=Challenge.gateSlots from rfl,group,distribute]
    cases d <;>
      simp only [distributed,PacketSequence.program,Bool.not_true,Bool.not_false,ten,first,second,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,enter0_gateSlots,
        switch0_gateSlots,leave0_gateSlots,enter1_gateSlots,switch1_gateSlots,leave1_gateSlots] <;> omega
  simp only [group84,ord,h,partition]
  omega
end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [225,271); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 209 ++
    forward45plus1 d ++ Rolling1588TickGap.forward d 271 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 271 tail ++
    reverse45plus1 d ++ Rolling1588.reverse d 16 209) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (forward45plus1 d)+f=c.measure (Rolling1588TickGap.forward d 225 46))
    (hr : c.measure (reverse45plus1 d)+r=c.measure (Rolling1588.reverse d 225 46)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (255+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (255+tail)) := by
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  have x := StairRestSupport.reverse_append d 209 16 (46+tail)
  have y := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] Partial.forward45plus1 Partial.reverse45plus1 Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 5001 else 5004)=
      toffoliCount (Stair44WalkRun.forward d (255+tail)) ∧
    toffoliCount (backward d tail)+(if d then 4993 else 4996)=
      toffoliCount (Stair44WalkRun.backward d (255+tail)) ∧
    measurementCount (forward d tail)+2546=measurementCount (Stair44WalkRun.forward d (255+tail)) ∧
    measurementCount (backward d tail)+2552=measurementCount (Stair44WalkRun.backward d (255+tail)) := by
  cases d
  · have sf := StockWindowCosts.stock false
    have a := forward45plus1_false
    have b := reverse45plus1_false
    have t := walk tc false tail 5004 4996
      (subEq 5004 a.1 sf.1 rfl) (subEq 4996 b.1 sf.2.2.1 rfl)
    have m := walk mc false tail 2546 2552
      (subEq 2546 a.2 sf.2.1 rfl) (subEq 2552 b.2 sf.2.2.2 rfl)
    exact ⟨t.1,t.2,m⟩
  · have sf := StockWindowCosts.stock true
    have a := forward45plus1_true
    have b := reverse45plus1_true
    have t := walk tc true tail 5001 4993
      (subEq 5001 a.1 sf.1 rfl) (subEq 4993 b.1 sf.2.2.1 rfl)
    have m := walk mc true tail 2546 2552
      (subEq 2546 a.2 sf.2.1 rfl) (subEq 2552 b.2 sf.2.2.2 rfl)
    exact ⟨t.1,t.2,m⟩

/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 255+tail=n)
    (hf : (if d then 5001 else 5004)=f) (hr : (if d then 4993 else 4996)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+2546=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+2552=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail
end ECDSAAdd.Entrant.StairPacket.WindowWalkCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def portsPass (j : Fin 23) (a : Nat) :=
  (IntegerPacket.ports (shape j) a).wires.all (fun q => domain (net j a q))

theorem routeSites {j : Fin 23} (table : ∀ i : Fin 15, portsPass j i = true)
    (a n : Nat) (bound : a+n ≤ 15) :
    Covered (routed j a n) ∧ Covered (unrouted j a n) := by
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [routed,unrouted,wires] at h
  | succ n ih =>
    have h : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape j) ⟨a,h⟩)
    have sub := ih (a+1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (shape j) a).wires.toFinset) :
        Covered (renameProgram (net j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact List.all_eq_true.mp (table ⟨a,h⟩) x (List.mem_toFinset.mp (hp hx))
    exact ⟨covered_append (ok _ step.1) sub.1, covered_append sub.2 (ok _ step.2)⟩

theorem ports10 : ∀ a : Fin 15, portsPass ⟨10,by decide⟩ a = true := by decide +kernel
theorem ports11 : ∀ a : Fin 15, portsPass ⟨11,by decide⟩ a = true := by decide +kernel
theorem ports12 : ∀ a : Fin 15, portsPass ⟨12,by decide⟩ a = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site0 : Covered (portal225) := by
  exact from_check (by decide +kernel)

theorem site1 : Covered (enter225) := by
  exact from_check (by decide +kernel)

theorem site2 : Covered (routed ⟨10,by decide⟩ 0 1) := by
  exact (routeSites ports10 0 1 (by decide)).1

theorem site3 : Covered (renameProgram (OB5.sig 225) (Rolling1588.packAtTick false 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site4 : Covered (routed ⟨10,by decide⟩ 1 14) := by
  exact (routeSites ports10 1 14 (by decide)).1

theorem site5 : Covered (leave225) := by
  exact from_check (by decide +kernel)

theorem site6 : Covered (enter240) := by
  exact from_check (by decide +kernel)

theorem site7 : Covered (routed ⟨11,by decide⟩ 0 1) := by
  exact (routeSites ports11 0 1 (by decide)).1

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site40 : Covered (enter255Inv) := by
  exact from_check (by decide +kernel)

theorem site41 : Covered (leave240Inv) := by
  exact from_check (by decide +kernel)

theorem site42 : Covered (unrouted ⟨11,by decide⟩ 1 14) := by
  exact (routeSites ports11 1 14 (by decide)).2

theorem site43 : Covered (archiveRestore240 false) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site44 : Covered (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick false 230)) := by
  exact from_check (by decide +kernel)

theorem site45 : Covered (unrouted ⟨11,by decide⟩ 0 1) := by
  exact (routeSites ports11 0 1 (by decide)).2

theorem site46 : Covered (enter240Inv) := by
  exact from_check (by decide +kernel)

theorem site47 : Covered (leave225Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site48 : Covered (unrouted ⟨10,by decide⟩ 1 14) := by
  exact (routeSites ports10 1 14 (by decide)).2

theorem site49 : Covered (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick false 225)) := by
  exact from_check (by decide +kernel)

theorem site50 : Covered (unrouted ⟨10,by decide⟩ 0 1) := by
  exact (routeSites ports10 0 1 (by decide)).2

theorem site51 : Covered (enter225Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site52 : Covered (portal225Inv) := by
  exact from_check (by decide +kernel)

theorem site53 : Covered (archiveRestore270 true) := by
  exact from_check (by decide +kernel)

theorem site54 : Covered (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick true 260)) := by
  exact from_check (by decide +kernel)

theorem site55 : Covered (archiveRestore255 true) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site56 : Covered (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick true 245)) := by
  exact from_check (by decide +kernel)

theorem site57 : Covered (archiveRestore240 true) := by
  exact from_check (by decide +kernel)

theorem site58 : Covered (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick true 230)) := by
  exact from_check (by decide +kernel)

theorem site59 : Covered (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick true 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site8 : Covered (renameProgram (OB5.sig 240) (Rolling1588.packAtTick false 230)) := by
  exact from_check (by decide +kernel)

theorem site9 : Covered (archiveLoad240 false) := by
  exact from_check (by decide +kernel)

theorem site10 : Covered (routed ⟨11,by decide⟩ 1 14) := by
  exact (routeSites ports11 1 14 (by decide)).1

theorem site11 : Covered (leave240) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site12 : Covered (enter255) := by
  exact from_check (by decide +kernel)

theorem site13 : Covered (routed ⟨12,by decide⟩ 0 1) := by
  exact (routeSites ports12 0 1 (by decide)).1

theorem site14 : Covered (renameProgram (OB5.sig 255) (Rolling1588.packAtTick false 245)) := by
  exact from_check (by decide +kernel)

theorem site15 : Covered (archiveLoad255 false) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site16 : Covered (routed ⟨12,by decide⟩ 1 14) := by
  exact (routeSites ports12 1 14 (by decide)).1

theorem site17 : Covered (leave255) := by
  exact from_check (by decide +kernel)

theorem site18 : Covered (park270) := by
  exact from_check (by decide +kernel)

theorem site19 : Covered (portal270Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site20 : Covered (renameProgram (OB5.sig 270) (TickRanges.tick base 270)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have table : (W.compactSkywalkTickLayout base 270).wires.all (fun z => domain (OB5.sig 270 z)) = true := by decide +kernel
  exact List.all_eq_true.mp table x (List.mem_toFinset.mp (W.repairedTick_support base 270 (by decide) base_pool_nodup (TickRanges.tick_support base 270 (by decide) base_pool_nodup hx)))

theorem site21 : Covered (renameProgram (OB5.sig 270) (Rolling1588.packAtTick false 260)) := by
  exact from_check (by decide +kernel)

theorem site22 : Covered (archiveLoad270 false) := by
  exact from_check (by decide +kernel)

theorem site23 : Covered (renameProgram (OB5.sig 225) (Rolling1588.packAtTick true 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site24 : Covered (renameProgram (OB5.sig 240) (Rolling1588.packAtTick true 230)) := by
  exact from_check (by decide +kernel)

theorem site25 : Covered (archiveLoad240 true) := by
  exact from_check (by decide +kernel)

theorem site26 : Covered (renameProgram (OB5.sig 255) (Rolling1588.packAtTick true 245)) := by
  exact from_check (by decide +kernel)

theorem site27 : Covered (archiveLoad255 true) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site28 : Covered (renameProgram (OB5.sig 270) (Rolling1588.packAtTick true 260)) := by
  exact from_check (by decide +kernel)

theorem site29 : Covered (archiveLoad270 true) := by
  exact from_check (by decide +kernel)

theorem site30 : Covered (archiveRestore270 false) := by
  exact from_check (by decide +kernel)

theorem site31 : Covered (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick false 260)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site32 : Covered (renameProgram (OB5.sig 270) (W.ReverseCarry.compactReceiverTick base 270)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have table : (W.compactSkywalkTickLayout base 270).wires.all (fun z => domain (OB5.sig 270 z)) = true := by decide +kernel
  exact List.all_eq_true.mp table x (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base 270 (by decide) base_pool_nodup hx))

theorem site33 : Covered (portal270) := by
  exact from_check (by decide +kernel)

theorem site34 : Covered (park270Inv) := by
  exact from_check (by decide +kernel)

theorem site35 : Covered (leave255Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site36 : Covered (unrouted ⟨12,by decide⟩ 1 14) := by
  exact (routeSites ports12 1 14 (by decide)).2

theorem site37 : Covered (archiveRestore255 false) := by
  exact from_check (by decide +kernel)

theorem site38 : Covered (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick false 245)) := by
  exact from_check (by decide +kernel)

theorem site39 : Covered (unrouted ⟨12,by decide⟩ 0 1) := by
  exact (routeSites ports12 0 1 (by decide)).2

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def entryTailPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldCosts.group84 true ++
    StairSchedule.forwardSegment p 87 62 425 450 ++
    hostedGroup hostPlan true 14 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    hostedGroup hostPlan true 23 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    hostedGroup hostPlan true 31 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    hostedGroup hostPlan true 37 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    hostedGroup hostPlan true 42 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    hostedGroup hostPlan false 42 98 2 ++
    StairSchedule.reverseSegment p 22 12 490 500 ++
    hostedGroup hostPlan false 37 96 2 ++
    StairSchedule.reverseSegment p 32 22 480 490 ++
    hostedGroup hostPlan false 31 93 3 ++
    StairSchedule.reverseSegment p 47 32 465 480 ++
    hostedGroup hostPlan false 23 90 3 ++
    StairSchedule.reverseSegment p 62 47 450 465 ++
    hostedGroup hostPlan false 14 85 5 ++
    StairSchedule.reverseSegment p 87 62 425 450 ++
    WindowFieldCosts.group84 false

def entryLowPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (Rolling1588.placedFirstPacket true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailPrefix p) ++
    FourScratchWindow.unprefix

def exitLowSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (exitHeadSuffix p) ++
    FourScratchWindow.unprefix ++
    StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
      (Rolling1588.placedFirstPacket false)

def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (entryLowPrefix p) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (entryLowSuffix hostPlan) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowPrefix hostPlan) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowSuffix p)

theorem field_delta (c : Cost) (d : Bool) (n : Nat)
    (h : c.measure (WindowFieldCosts.group84 d)=c.measure (WindowFieldCosts.group d 1 84)+n) :
    (if d then c.measure (entryFieldHosted checkpointPrimitives)
     else c.measure (exitFieldHosted checkpointPrimitives)) =
    (if d then c.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
     else c.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan))+n := by
  cases d <;> simp only [Bool.false_eq_true,if_true,if_false,WindowFieldCosts.group] at h ⊢
  all_goals simp only [entryFieldHosted,exitFieldHosted,entryLowPrefix,exitLowSuffix,
    entryTailPrefix,exitHeadSuffix,StairHostsSchedule.entryFieldHosted,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.exitLowSuffix,StairHostsSchedule.entryTailPrefix,
    StairHostsSchedule.exitHeadSuffix,StairSchedule.fieldRename,StairSchedule.parityRename,
    c.rename,c.append,h]
  all_goals omega

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 154) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace (entryFieldHosted checkpointPrimitives) ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 235) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 234) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 154) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (ParityUniform.entryYAll layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (ParityUniform.exitYAll layout cy)

def borrowGeneric (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (generic cx cy))

def finite (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGeneric cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def program (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finite (.some hc) cx cy)

theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 154)+gainF=c.measure (Stair44WalkRun.forward true 409))
    (dR : c.measure (WindowWalkCosts.backward false 235)+gainR=c.measure (Stair44WalkRun.backward false 490))
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure divide+gainF+gainR=c.measure Stair44Outer.divide+fieldExtra := by
  have h := field_delta c true _ g
  simp only [if_true] at h
  simp only [divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 234)+gainF=c.measure (Stair44WalkRun.forward false 489))
    (mR : c.measure (WindowWalkCosts.backward true 154)+gainR=c.measure (Stair44WalkRun.backward true 409))
    (g : c.measure (WindowFieldCosts.group84 false)=c.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    c.measure (multiply k)+gainF+gainR=c.measure (Stair44Outer.multiply k)+fieldExtra := by
  have h := field_delta c false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

theorem finite_delta (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (h : c.measure divide+c.measure (multiply cx.val)+gain =
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)) :
    c.measure (finite C cx cy)+gain=c.measure (Stair44Outer.finite C cx cy) := by
  simp only [finite,Stair44Outer.finite,borrowGeneric,Stair44Outer.borrowGeneric,
    generic,Stair44Outer.generic,c.append,c.rename]
  omega

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open ArchiveFieldScratch StairArchiveRelease StairArchiveNativeCut StairArchiveTen

def reserved : List Wire := List.range' 4836 39 ++ List.range' 4876 4
private theorem subset {q : Wire} (h : q∈reserved) : q∈StairPhysicalInventory.physicalHoles := by
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  simp only [reserved,StairPhysicalLayout.newHolesNat,List.mem_append,List.mem_range'_1] at *
  omega

theorem weaken {P : Program} {f : Wire → Wire} (h : PieceOK StairPhysicalInventory.physicalHoles f P) :
    PieceOK reserved f P := ⟨h.1,fun x hx bad => h.2 x hx (subset bad)⟩

theorem app {a b : Program} {f : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (a++b) ↔ PieceOK hs f a ∧ PieceOK hs f b := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => h.1.append h.2⟩ <;>
    constructor <;> intro q hq
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_right _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_right _ hq)

theorem ren {a : Program} {f g : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (renameProgram g a) ↔ PieceOK hs (fun q => f (g q)) a := by
  refine ⟨fun h => ⟨?_,?_⟩,PieceOK.rename⟩ <;> intro x hx
  · exact h.1 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · exact h.2 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)

private theorem singleton_ok {q : Wire} (h : Stair44OuterSites.fit q=true) :
    q∈StairHoleSupport.recordArena ∧ q∉StairHoleSupport.oldHoles ∧ q∉reserved := by
  let P : Program := [.X q]
  have inv : PieceOK StairPhysicalInventory.physicalHoles id P := Stair44OuterSites.fits
    (fun x hx => by
      have eq : x=q := by simpa [P,wires,Instr.wires] using hx
      exact eq ▸ h)
  have here : q∈wires P := by simp [P,wires,Instr.wires]
  exact ⟨(inv.1 q here).1,(inv.1 q here).2,(weaken inv).2 q here⟩

private theorem tagOK : 4835∈StairHoleSupport.recordArena ∧ 4835∉StairHoleSupport.oldHoles ∧
    4835∉reserved := by
  rw [StairPhysicalLayout.recordArena_eq,StairPhysicalLayout.oldHoles_eq]
  decide +kernel

private theorem addresses (j : Nat) (hj : j∈List.range' 1 83) (q : Wire) (hq : q∈layout j) :
    Stair44OuterSites.fit q=true ∨ q=4835 := by
  have p := List.all_eq_true.mp packets_exact j hj
  dsimp only [packetOK,Id.run,pure] at p
  simp only [Bool.and_eq_true] at p
  simp only [layout,transient_exact,List.mem_append,List.mem_cons] at hq
  rcases hq with a | a | a
  · have z := List.all_eq_true.mp p.2 q a
    simp only [Bool.and_eq_true] at z
    exact Or.inl z.1
  · exact Or.inr a
  · exact Or.inl (List.all_eq_true.mp permanent_exact.2 q a)

theorem hook (j : Nat) (hj : j∈List.range' 1 83) (op : Stage) :
    PieceOK reserved TP (fieldHook j op) := by
  rw [fieldHook,ren]
  have cover (x : Wire) (hx : x∈wires (program op)) :
      TP (fieldPort j x)∈StairHoleSupport.recordArena ∧
      TP (fieldPort j x)∉StairHoleSupport.oldHoles ∧ TP (fieldPort j x)∉reserved := by
    have lt := Finset.mem_range.mp (sub op hx)
    have sl := (layout_frame j hj).2
    have small : x < (layout j).length := sl ▸ lt
    have member : port j x ∈ layout j := by
      simp only [port,List.getElem?_eq_getElem small,Option.getD_some,List.getElem_mem]
    change StairOuterPlacement.outerPlace _ ∈ _ ∧ _ ∧ _
    simp only [show TP=StairOuterPlacement.outerPlace from rfl,StairPlaceFast.outerPlace_eqB,placed_port j hj x lt]
    rcases addresses j hj _ member with p|e
    · exact singleton_ok p
    · rw [e]; exact tagOK
  exact ⟨fun x hx => ⟨(cover x hx).1,(cover x hx).2.1⟩,fun x hx => (cover x hx).2.2⟩

theorem width {P : Program} (h : PieceOK reserved id P) : Challenge.qubits P ≤ 1543 := by
  have listOK := StairCertificate.holeList_of_physical_sub reserved (by decide +kernel) (fun _ hx => subset hx)
  exact StairCertificate.qubits_le_holes reserved listOK P (holePlacement_of_ok h)
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

attribute [local irreducible] wires domain

theorem forward45plus1_domain (d : Bool) : Covered (forward45plus1 d) := by
  intro q h
  cases d
  · simp only [forward45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site0 q h
    · exact site1 q h
    · exact site2 q h
    · exact site3 q h
    · exact site4 q h
    · exact site5 q h
    · exact site6 q h
    · exact site7 q h
    · exact site8 q h
    · exact site9 q h
    · exact site10 q h
    · exact site11 q h
    · exact site12 q h
    · exact site13 q h
    · exact site14 q h
    · exact site15 q h
    · exact site16 q h
    · exact site17 q h
    · exact site18 q h
    · exact site19 q h
    · exact site20 q h
    · exact site21 q h
    · exact site22 q h
  · simp only [forward45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site0 q h
    · exact site1 q h
    · exact site2 q h
    · exact site23 q h
    · exact site4 q h
    · exact site5 q h
    · exact site6 q h
    · exact site7 q h
    · exact site24 q h
    · exact site25 q h
    · exact site10 q h
    · exact site11 q h
    · exact site12 q h
    · exact site13 q h
    · exact site26 q h
    · exact site27 q h
    · exact site16 q h
    · exact site17 q h
    · exact site18 q h
    · exact site19 q h
    · exact site20 q h
    · exact site28 q h
    · exact site29 q h
theorem reverse45plus1_domain (d : Bool) : Covered (reverse45plus1 d) := by
  intro q h
  cases d
  · simp only [reverse45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site30 q h
    · exact site31 q h
    · exact site32 q h
    · exact site33 q h
    · exact site34 q h
    · exact site35 q h
    · exact site36 q h
    · exact site37 q h
    · exact site38 q h
    · exact site39 q h
    · exact site40 q h
    · exact site41 q h
    · exact site42 q h
    · exact site43 q h
    · exact site44 q h
    · exact site45 q h
    · exact site46 q h
    · exact site47 q h
    · exact site48 q h
    · exact site49 q h
    · exact site50 q h
    · exact site51 q h
    · exact site52 q h
  · simp only [reverse45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site53 q h
    · exact site54 q h
    · exact site32 q h
    · exact site33 q h
    · exact site34 q h
    · exact site35 q h
    · exact site36 q h
    · exact site55 q h
    · exact site56 q h
    · exact site39 q h
    · exact site40 q h
    · exact site41 q h
    · exact site42 q h
    · exact site57 q h
    · exact site58 q h
    · exact site45 q h
    · exact site46 q h
    · exact site47 q h
    · exact site48 q h
    · exact site59 q h
    · exact site50 q h
    · exact site51 q h
    · exact site52 q h

theorem forward45plus1_fits (d : Bool) : ∀ q ∈ wires (forward45plus1 d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forward45plus1_domain d q h)

theorem reverse45plus1_fits (d : Bool) : ∀ q ∈ wires (reverse45plus1 d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (reverse45plus1_domain d q h)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

private theorem fieldTc (d : Bool) :
    tc.measure (WindowFieldCosts.group84 d)=tc.measure (WindowFieldCosts.group d 1 84)+624 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact (WindowFieldCosts.group_cost d).1
private theorem fieldMc (d : Bool) :
    mc.measure (WindowFieldCosts.group84 d)=mc.measure (WindowFieldCosts.group d 1 84)+831 := by
  rw [show mc.measure=measurementCount from rfl]
  exact (WindowFieldCosts.group_cost d).2
private theorem sum_delta {a b x y g h f r : Nat}
    (l : a+g+h=x+f) (rr : b+g+h=y+f) (v : 2*(g+h)=r+2*f) : a+b+r=x+y := by omega
private theorem pair_delta {a b x y g h i j f r : Nat}
    (l : a+g+h=x+f) (rr : b+i+j=y+f) (v : g+h+i+j=r+2*f) : a+b+r=x+y := by omega

attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84 WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+5001+4996=tc.measure Stair44Outer.divide+624 :=
  kernels tc 5001 4996 624 (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).1
    (WindowWalkCosts.inst false 235 490 5004 4996 rfl rfl rfl).2.1 (fieldTc true)

theorem tc_mul (k : Nat) : tc.measure (multiply k)+5004+4993=tc.measure (Stair44Outer.multiply k)+624 :=
  kernelsM tc k 5004 4993 624 (WindowWalkCosts.inst false 234 489 5004 4996 rfl rfl rfl).1
    (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.1 (fieldTc false)

theorem mc_div : mc.measure divide+2546+2552=mc.measure Stair44Outer.divide+831 :=
  kernels mc 2546 2552 831 (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst false 235 490 5004 4996 rfl rfl rfl).2.2.2 (fieldMc true)

theorem mc_mul (k : Nat) : mc.measure (multiply k)+2546+2552=mc.measure (Stair44Outer.multiply k)+831 :=
  kernelsM mc k 2546 2552 831 (WindowWalkCosts.inst false 234 489 5004 4996 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.2.2 (fieldMc false)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+18746=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+8534=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 18746 (pair_delta tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 8534 (sum_delta mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2151219 ∧
    measurementCount (program C) ≤ 1512390 := by
  have h := Stair44Resources.totals C
  cases C with
  | zero => change toffoliCount [] ≤ _ ∧ measurementCount [] ≤ _; simp [toffoliCount,measurementCount]
  | @some cx cy hc =>
    have d := deltas (.some hc) cx cy
    simp only [program,Stair44Outer.program,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowWalkCosts
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount gateSlots measurementCount wires renameProgram
  Rolling1588TickGap.forward Rolling1588.reverse Partial.forward45plus1 Partial.reverse45plus1

private theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 255+tail=n)
    (hf : c.measure (Partial.forward45plus1 d) ≤ f) (hr : c.measure (Partial.reverse45plus1 d) ≤ r) :
    c.measure (WindowWalkCosts.forward d tail) ≤ c.measure (Stair44WalkRun.forward d n)+f ∧
    c.measure (WindowWalkCosts.backward d tail) ≤ c.measure (Stair44WalkRun.backward d n)+r := by
  subst n
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  have x := StairRestSupport.reverse_append d 209 16 (46+tail)
  have y := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,WindowWalkCosts.forward,WindowWalkCosts.backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

private theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 154) ≤ c.measure (Stair44WalkRun.forward true 409)+gainF)
    (dR : c.measure (WindowWalkCosts.backward false 235) ≤ c.measure (Stair44WalkRun.backward false 490)+gainR)
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure WindowCallerCosts.divide ≤ c.measure Stair44Outer.divide+gainF+gainR+fieldExtra := by
  have h  := WindowCallerCosts.field_delta c true _ g
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

private theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 234) ≤ c.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : c.measure (WindowWalkCosts.backward true 154) ≤ c.measure (Stair44WalkRun.backward true 409)+gainR)
    (g : c.measure (WindowFieldCosts.group84 false)=c.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    c.measure (WindowCallerCosts.multiply k) ≤ c.measure (Stair44Outer.multiply k)+gainF+gainR+fieldExtra := by
  have h  := WindowCallerCosts.field_delta c false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [WindowCallerCosts.multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

private theorem finite_upper (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (h : c.measure WindowCallerCosts.divide+c.measure (WindowCallerCosts.multiply cx.val) ≤
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)+gain) :
    c.measure (WindowCallerCosts.finite C cx cy) ≤ c.measure (Stair44Outer.finite C cx cy)+gain := by
  simp only [WindowCallerCosts.finite,Stair44Outer.finite,WindowCallerCosts.borrowGeneric,Stair44Outer.borrowGeneric,
    WindowCallerCosts.generic,Stair44Outer.generic,c.append,c.rename]
  omega


private theorem casts {P : Program} {n : Nat} (h : gateSlots P ≤ n) : slots.measure P ≤ n := h
private theorem groupCap (d : Bool) (n : Nat) (hn : 3*(if d then 6042 else 6053)=n) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  subst n
  exact WindowFieldCosts.group_slots d
private theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+257077+257873+18126 :=
  kernels slots 257077 257873 18126
    (walk slots true 154 257077 257861 409 rfl (casts forward45plus1_true) (casts reverse45plus1_true)).1
    (walk slots false 235 257059 257873 490 rfl (casts forward45plus1_false) (casts reverse45plus1_false)).2
    (groupCap true 18126 rfl)

private theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+257059+257861+18159 :=
  kernelsM slots k 257059 257861 18159
    (walk slots false 234 257059 257873 489 rfl (casts forward45plus1_false) (casts reverse45plus1_false)).1
    (walk slots true 154 257077 257861 409 rfl (casts forward45plus1_true) (casts reverse45plus1_true)).2
    (groupCap false 18159 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+257077+257873+18126)
    (hm : b ≤ y+257059+257861+18159) : a+b ≤ x+y+1066155 := by omega

private theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+1066155 :=
  finite_upper slots C cx cy 1066155 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 51926637 := by
  have h := Stair44Resources.slotBound C
  cases C with
  | zero => change gateSlots [] ≤ _; simp [gateSlots]
  | @some cx cy hc =>
    have f := cap (.some hc) cx cy
    rw [show slots.measure=gateSlots from rfl] at f
    simp only [WindowCallerCosts.program,Stair44Outer.program,rename_gateSlots] at h ⊢
    omega
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open StairRestSupport StairPhysicalV3 ArchiveFieldScratch StairArchiveRelease StairArchiveGates Baselines
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet


private theorem app {p q : Program} : Sound (p++q) ↔ Sound p ∧ Sound q :=
  ⟨fun h => ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩,
    fun h => sound_append h.1 h.2⟩

private theorem emitted (op : Stage) : GatePhysical (StairArchiveRelease.program op) := by
  cases op
  exacts [enter0_GatePhysical,switch0_GatePhysical,leave0_GatePhysical,
    enter1_GatePhysical,switch1_GatePhysical,leave1_GatePhysical]

private theorem hook (j : Nat) (hj : j∈[46,49,52]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide +kernel
  refine ⟨gatePhysical_rename_support _ _ (fun a ha b hb eq => field_inj j span a (sub op ha) b (sub op hb) eq) (emitted op),?_⟩
  intro q hq
  rw [fieldHook,renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have len : (fieldSites j).length=121 := by
    have hh := (layout_frame j span).2
    rwa [←field_layout,List.length_map] at hh
  have lt : x < (fieldSites j).length := len ▸ (Finset.mem_range.mp (sub op hx))
  apply of_decide_eq_true (List.all_eq_true.mp chk _ ?_)
  simp only [fieldPort,List.getElem?_eq_getElem lt,Option.getD_some,List.getElem_mem]

private theorem distributed_ok (d : Bool) (j n : Nat) :
    Sound (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → Sound (packet d i) := by
  induction n generalizing j with
  | zero =>
    change Sound [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩⟩
  | succ n ih =>
    change Sound (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (Sound (packet d j) ∧ Sound (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → Sound (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

private theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → Sound (packet d i) := by
  apply (distributed_ok d 1 84).mp
  rw [←distribute]
  exact sound_hostedGroup StairOpenWiring.half760 hostSlots_v3 d 0 1 84 (by decide) (by decide) (by decide) (by decide)

private theorem ordinary (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    Sound (group d j n) := by
  rw [group,distribute,distributed_ok]
  exact fun i l u => whole d i (by omega) (by omega)

private theorem pair (d : Bool) (j : Nat) (pick : j∈[46,49,52]) (lo : 1≤j) (hi : j≤83) :
    Sound (ten j (!d)) := by
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : Sound (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (second j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  exact ord (ordinary d 1 45 (by decide) (by decide)) (ord (pair d 46 (by decide) (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide)) (ord (pair d 49 (by decide) (by decide) (by decide))
      (ord (ordinary d 51 1 (by decide) (by decide)) (ord (pair d 52 (by decide) (by decide) (by decide))
        (ordinary d 54 31 (by decide) (by decide)))))))

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet

private theorem distributed_ok (d : Bool) (j n : Nat) :
    PieceOK reserved TP (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → PieceOK reserved TP (packet d i) := by
  induction n generalizing j with
  | zero =>
    change PieceOK _ _ [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => pieceOK_nil _ _⟩
  | succ n ih =>
    change PieceOK _ _ (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (PieceOK reserved TP (packet d j) ∧ PieceOK reserved TP (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → PieceOK reserved TP (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

private theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → PieceOK reserved TP (packet d i) := by
  apply (distributed_ok d 1 84).mp
  rw [←distribute]
  exact weaken (Stair44Groups.hostedGroup44 d 0 1 84 (by decide))

private theorem ordinary (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK reserved TP (group d j n) := by
  rw [group,distribute,distributed_ok]
  exact fun i l u => whole d i (by omega) (by omega)

private theorem pair (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK reserved TP (ten j (!d)) := by
  have jmem : j∈List.range' 1 83 := List.mem_range'_1.mpr ⟨lo,by omega⟩
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : PieceOK reserved TP (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : PieceOK reserved TP (second j (!d)) := by cases d <;> first | exact here | exact next
  exact (hook j jmem _).append (firstOK.append ((hook j jmem _).append (lastOK.append (hook j jmem _))))

theorem group84_ok (d : Bool) : PieceOK reserved TP (group84 d) := by
  have ord {a b : Program} (ha : PieceOK reserved TP a) (hb : PieceOK reserved TP b) :
      PieceOK reserved TP (ordered d a b) := by cases d <;> first | exact ha.append hb | exact hb.append ha
  exact ord (ordinary d 1 45 (by decide) (by decide)) (ord (pair d 46 (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide)) (ord (pair d 49 (by decide) (by decide))
      (ord (ordinary d 51 1 (by decide) (by decide)) (ord (pair d 52 (by decide) (by decide))
        (ordinary d 54 31 (by decide) (by decide)))))))

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Baselines StairPhysicalV3 StairRestSupport StairConcreteAssembly
variable {p : StairSchedule.StairPrimitives}
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000
theorem sound_entryTailPrefix (H : LoanHyp) (P : PrimitiveSlots p) (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryTailPrefix p) := by
  have g0 := group84_ok true
  have g14 := sound_hostedGroup H hs true 14 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs true 23 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs true 31 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs true 37 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs true 42 98 2 (by decide) (by omega) (by omega) (by omega)
  have s1 := sound_forwardSegment P 87 62 425 450 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s2 := sound_forwardSegment P 62 47 450 465 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s3 := sound_forwardSegment P 47 32 465 480 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s4 := sound_forwardSegment P 32 22 480 490 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s5 := sound_forwardSegment P 22 12 490 500 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have sl := sound_forwardLast P
  unfold WindowCallerCosts.entryTailPrefix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append g0 s1) g14) s2) g23) s3) g31) s4) g37) s5) g42) sl

theorem sound_exitHeadSuffix (H : LoanHyp) (P : PrimitiveSlots p) (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitHeadSuffix p) := by
  have g0 := group84_ok false
  have g14 := sound_hostedGroup H hs false 14 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs false 23 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs false 31 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs false 37 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs false 42 98 2 (by decide) (by omega) (by omega) (by omega)
  have s5 := sound_reverseSegment P 22 12 490 500 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s4 := sound_reverseSegment P 32 22 480 490 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s3 := sound_reverseSegment P 47 32 465 480 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s2 := sound_reverseSegment P 62 47 450 465 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s1 := sound_reverseSegment P 87 62 425 450 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have rl := sound_reverseLast P
  unfold WindowCallerCosts.exitHeadSuffix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append rl g42) s5) g37) s4) g31) s3) g23) s2) g14) s1) g0

theorem sound_entryFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryFieldHosted p) := by
  have first := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket true)
    (sound_firstPacket true)
  have pre : Sound (WindowCallerCosts.entryLowPrefix p) := by
    unfold WindowCallerCosts.entryLowPrefix
    exact sound_append (sound_append (sound_append first sound_clearProgram)
      (sound_borrow (sound_entryTailPrefix H P hs))) sound_unprefix
  have tail : Sound (StairHostsSchedule.entryTailSuffix hostPlan) := by
    have g := sound_hostedGroup H hs true 44 100 2 (by decide) (by omega) (by omega)
      (by omega)
    unfold StairHostsSchedule.entryTailSuffix
    exact sound_append (sound_append (sound_append g
      (sound_sig 511 (by omega) B.divEndpoint)) sound_copyN) B.canon
  have suf : Sound (StairHostsSchedule.entryLowSuffix hostPlan) := by
    unfold StairHostsSchedule.entryLowSuffix
    exact sound_append (sound_append sound_clearProgram (sound_borrow tail)) sound_unprefix
  unfold WindowCallerCosts.entryFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_fieldRename pre) sound_paritySetup) sound_hostedX)
    (sound_fieldRename suf)) sound_hostedX) sound_paritySetup

theorem sound_exitFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitFieldHosted p) := by
  have head : Sound (StairHostsSchedule.exitHeadPrefix hostPlan) := by
    have g := sound_hostedGroup H hs false 44 100 2 (by decide) (by omega) (by omega)
      (by omega)
    unfold StairHostsSchedule.exitHeadPrefix StairHostsSchedule.hostedEndpoint
      StairSchedule.placedEndPacket
    exact sound_append (sound_append (sound_append B.center sound_copyN)
      (sound_sig 511 (by omega) B.multEndpoint)) g
  have pre : Sound (StairHostsSchedule.exitLowPrefix hostPlan) := by
    unfold StairHostsSchedule.exitLowPrefix
    exact sound_append (sound_append sound_clearProgram (sound_borrow head)) sound_unprefix
  have last := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket false)
    (sound_firstPacket false)
  have suf : Sound (WindowCallerCosts.exitLowSuffix p) := by
    unfold WindowCallerCosts.exitLowSuffix
    exact sound_append (sound_append (sound_append sound_clearProgram
      (sound_borrow (sound_exitHeadSuffix H P hs))) sound_unprefix) last
  unfold WindowCallerCosts.exitFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    sound_paritySetup sound_hostedX) (sound_fieldRename pre)) sound_paritySetup)
    sound_hostedX) (sound_fieldRename suf)

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairRestSupport
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
attribute [local irreducible] wires renameProgram Partial.forward45plus1 Partial.reverse45plus1
  Rolling1588TickGap.forward Rolling1588.reverse Stair44WalkMap.rest Stair44WalkMap.first

abbrev GoodWindow (p : Program) :=
  ∀ q∈wires p, Stair44PhaseSites.valid (Stair44WalkMap.rest q)=true

private theorem native {p : Program} (h : GoodWindow p) :
    PieceOK reserved (fun x => PP (Stair44WalkMap.rest x)) p := by
  apply weaken
  apply Stair44OuterSites.fits
  intro x hx
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace (Stair44WalkMap.rest x))=true
  rw [StairPlaceFast.phasePlace_eqB]
  exact h x hx

theorem walkF (d : Bool) (tail : Nat) (bound : 16+(255+tail)≤506)
    (new : GoodWindow (Partial.forward45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.forward d tail) := by
  have old := weaken (Stair44PhaseSites.forward d (255+tail) bound)
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  rw [b] at a
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(255+tail)≤506)
    (new : GoodWindow (Partial.reverse45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (255+tail) bound)
  have a := StairRestSupport.reverse_append d 209 16 (46+tail)
  have b := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at a
  rw [b] at a
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.backward,num,a,app,ren] at old
  simp only [WindowWalkCosts.backward,app,ren]
  exact ⟨⟨⟨old.1.1.1,native new⟩,old.1.2⟩,old.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Secp256k1 Baselines StairPhysicalV3 StairRestSupport
open Stair44Outer StairConcreteAssembly Stair44WalkMap
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000
attribute [local irreducible] wires GatePhysical
private theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
  ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩

private theorem firstDom (q : Wire) (h : InDom q) : InDom (first q) := by
  unfold first shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))

private theorem restDom (q : Wire) (h : InDom q) : InDom (rest q) := by
  unfold rest shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))


private theorem dom {p : Program} (cover : PartialSites.Covered p) : Good p := by
  intro q hq
  have h := cover q hq
  simp only [PartialSites.domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  unfold InDom InDomN
  left
  constructor
  all_goals omega

private theorem fw (d : Bool) (tail n : Nat) (hn : 15+(255+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (Partial.forward45plus1 d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (255+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (255+tail)) at late
  rw [show 255+tail=209+(46+tail) by omega,forward_append d 209 16 (46+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 225 (46+tail)) at ms
  rw [forward_append d 46 225 tail] at ms
  have patch : Sound (Partial.forward45plus1 d) := ⟨p,dom (PartialSites.forward45plus1_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 271 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(255+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (Partial.reverse45plus1 d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (255+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (255+tail)) at late
  rw [show 255+tail=209+(46+tail) by omega,reverse_append d 209 16 (46+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 225 (46+tail)) at ms
  rw [reverse_append d 46 225 tail] at ms
  have patch : Sound (Partial.reverse45plus1 d) := ⟨p,dom (PartialSites.reverse45plus1_domain d)⟩
  have last : Sound (Rolling1588.reverse d 271 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
private theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (Partial.forward45plus1 d)) (rr : ∀d,GatePhysical (Partial.reverse45plus1 d))

include ff rr in
theorem dividePhysical : GatePhysical WindowCallerCosts.divide := by
  have eq : InverseFive23.lastPhase15 false = reverseEnd ++
      Rolling1588.reverse false 1 505 ++ FrontierEntry1591NativeH.inverse base := by
    simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
      reverseEnd,List.append_assoc]
  have h := sound_lastPhase15
  rw [eq] at h
  have ⟨a,native⟩ := parts h
  have ⟨tail,walk⟩ := parts a
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [WindowCallerCosts.divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 154 424 rfl sound_forward424 (ff _)),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 235 505 rfl walk (rr _))⟩,phase (sound_rename _ first.injective firstDom native)⟩

include ff rr in
theorem multiplyPhysical (k : Nat) : GatePhysical (WindowCallerCosts.multiply k) := by
  have eq : Rolling1588TickGap.tailPhase false = Rolling1588TickGap.forward false 1 504 ++ forwardEnd := by
    simp only [Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
      forwardEnd,List.append_assoc]
  have h := sound_tailPhase
  rw [eq] at h
  have ⟨walk,tail⟩ := parts h
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_exitFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [WindowCallerCosts.multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw false 234 504 rfl walk (ff _)),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 154 424 rfl sound_reverse424 (rr _))⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

include ff rr in
theorem genericPhysical (cx cy : Fp) : GatePhysical (WindowCallerCosts.generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [WindowCallerCosts.generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.1.1.1,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical ff rr⟩,
    Stair44Square.physical _⟩,multiplyPhysical ff rr _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.2.2⟩

include ff rr in
theorem physical (C : Point) : GatePhysical (WindowCallerCosts.program C) := by
  cases C with
  | zero => simp [WindowCallerCosts.program,GatePhysical]
  | @some cx cy hc =>
    let C : Point := .some hc
    have m := AboveFieldPointDevelop.middle_physical C cx cy
    simp only [AboveFieldPointDevelop.middle,gatePhysical_append] at m
    apply gatePhysical_rename _ (Wrapper5.U layout).injective
    simp only [WindowCallerCosts.finite,gatePhysical_append]
    refine ⟨⟨gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_,?_⟩,
      gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_⟩
    · simp only [gatePhysical_append]
      exact ⟨⟨FlagTop.stageNew_physical hc,m.1.1.1.1⟩,m.1.1.1.2⟩
    · exact gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ FlagTop.rho_injective _ (genericPhysical ff rr cx cy))
    · simp only [gatePhysical_append]
      exact ⟨⟨m.1.2,m.2⟩,ControlPointEncodingDevelop.borrowOut_physical hc⟩
end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
open StairConcreteAssembly Stair44Outer
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-- Replacing a child leaves the safety contract on the other children intact. -/
private def SafeChange (f : Wire → Wire) (old new : Program) :=
  PieceOK reserved f old → PieceOK reserved f new
private theorem same (f : Wire → Wire) (p : Program) : SafeChange f p p := id
private theorem fresh {f : Wire → Wire} {p q : Program} (h : PieceOK reserved f q) :
    SafeChange f p q := fun _ => h
private theorem appendChange {f : Wire → Wire} {a b x y : Program}
    (l : SafeChange f a x) (r : SafeChange f b y) : SafeChange f (a++b) (x++y) :=
  fun old => (l (app.mp old).1).append (r (app.mp old).2)
private theorem renameChange {f g : Wire → Wire} {a b : Program}
    (h : SafeChange (fun x => f (g x)) a b) : SafeChange f (renameProgram g a) (renameProgram g b) :=
  fun old => ren.mpr (h (ren.mp old))

private theorem tail (p : StairSchedule.StairPrimitives) :
    SafeChange TP (StairHostsSchedule.entryTailPrefix p hostPlan)
      (WindowCallerCosts.entryTailPrefix p) := by
  unfold StairHostsSchedule.entryTailPrefix WindowCallerCosts.entryTailPrefix
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  exact fresh (group84_ok true)

private theorem head (p : StairSchedule.StairPrimitives) :
    SafeChange TP (StairHostsSchedule.exitHeadSuffix p hostPlan)
      (WindowCallerCosts.exitHeadSuffix p) := by
  unfold StairHostsSchedule.exitHeadSuffix WindowCallerCosts.exitHeadSuffix
  exact appendChange (same _ _) (fresh (group84_ok false))

private theorem entryField : PieceOK reserved KP
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) := by
  have h := weaken Stair44FieldSites.entry
  apply (show SafeChange KP (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) from ?_) h
  have low : SafeChange lowPlace (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan)
      (WindowCallerCosts.entryLowPrefix checkpointPrimitives) :=
    appendChange (appendChange (same _ _) (renameChange (tail _))) (same _ _)
  have field : SafeChange KP (StairSchedule.fieldRename (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan))
      (StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix checkpointPrimitives)) :=
    renameChange (renameChange low)
  exact appendChange (appendChange (appendChange (appendChange (appendChange field
    (same _ _)) (same _ _)) (same _ _)) (same _ _)) (same _ _)

private theorem exitField : PieceOK reserved KP
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) := by
  have h := weaken Stair44FieldSites.exit
  apply (show SafeChange KP (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) from ?_) h
  have low : SafeChange lowPlace (StairHostsSchedule.exitLowSuffix checkpointPrimitives hostPlan)
      (WindowCallerCosts.exitLowSuffix checkpointPrimitives) :=
    appendChange (appendChange (appendChange (same _ _) (renameChange (head _))) (same _ _)) (same _ _)
  exact appendChange (same _ _) (renameChange (renameChange low))

private theorem phase {P : Program} (v : PieceOK reserved PP P) :
    PieceOK reserved UG (Stair44Outer.phasePlace P) := ok_kernel (ok_phase v)

theorem division (f : GoodWindow (Partial.forward45plus1 true))
    (r : GoodWindow (Partial.reverse45plus1 false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 154 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryField)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 235 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Partial.forward45plus1 false))
    (r : GoodWindow (Partial.reverse45plus1 true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 234 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 154 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (Partial.forward45plus1 d))
    (r : ∀d,GoodWindow (Partial.reverse45plus1 d)) :
    Challenge.qubits (WindowCallerCosts.program C) ≤ 1543 := by
  apply width
  cases C with
  | zero => exact pieceOK_nil _ _
  | @some cx cy hc =>
    apply ok_wrapper
    exact ((weaken (Stair44OuterSites.initial hc)).append (ok_generic
      ((((((weaken (Stair44OuterSites.entryY (-cy))).append (weaken (Stair44OuterSites.entryX (-cx)))).append
        (division (f _) (r _))).append (weaken (Stair44Release.squareSites (ReflectionE1.correction cx)))).append
          (multiplication cx.val (f _) (r _))).append (weaken (Stair44OuterSites.exitY cy))))).append
      (weaken (Stair44OuterSites.finalPart hc))
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic Secp256k1

theorem physical (C : Point) : GatePhysical (program C) :=
  WindowPhysical.physical PartialPhysical.forward45plus1_physical PartialPhysical.reverse45plus1_physical C

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Secp256k1

theorem qubitBound (C : Point) : Challenge.qubits (program C) ≤ 1543 :=
  WindowSites.program_width C PartialSites.forward45plus1_fits PartialSites.reverse45plus1_fits

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowRelease
open Arithmetic Secp256k1 Challenge Baselines

def entry : Challenge.Entry := fun C => normalizeProgram (WindowCallerCosts.program C)
def bounds : Challenge.Bounds := ⟨2151219,1512390,1543,51926637⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowCallerCosts.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowCallerCosts.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowCallerCosts.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1512390
    rw [normalize_measurements]
    exact (WindowCallerCosts.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowCallerCosts.qubitBound C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 51926637
    rw [normalize_slots]
    exact WindowSlots.slotBound C

end ECDSAAdd.Entrant.StairPacket.WindowRelease

end
