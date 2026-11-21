import ECDSAAdd.Submission.Entrant.ShadowParts

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem canonical (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (IntegerPacket.ready (Shadow7.shape j) 0 z) (Shadow7.forward j)
      (IntegerPacket.ready (Shadow7.shape j) 15 (SkywalkTrace.next^[15] z)) :=
  IntegerPacket.semantic (Shadow7.shape j) 0 15 (by rfl) z odd

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem restores (j : Fin 23) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    IntegerPacket.Restores (IntegerPacket.ready (Shadow7.shape j) 0 z) (Shadow7.forward j) (Shadow7.reverse j) :=
  IntegerPacket.roundtrip (Shadow7.shape j) 0 15 (by rfl) z odd

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem bounds (j : Fin 23) :
    toffoliCount (Shadow7.forward j)=15*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.forward j)=15*(Shadow7.smallBits j+18) ∧
    toffoliCount (Shadow7.reverse j)=15*(2*(Shadow7.smallBits j+18)) ∧
    measurementCount (Shadow7.reverse j)=15*(Shadow7.smallBits j+18) :=
  IntegerPacket.metrics (Shadow7.shape j) 0 15 (by rfl)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic
set_option maxHeartbeats 3500000

theorem stable {j : Fin 23} {a q : Nat} (ha : a < 15)
    (hq:q∈(IntegerPacket.ports (Shadow7.shape j) a).wires) : net j a q=windowNet j q := by
  have hj:=j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  unfold windowNet net OB5.sig start
  split <;> split
  all_goals try rfl
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem fixed_route (j : Fin 23) (a n : Nat) (bound:a+n≤15) :
    Shadow7.routed j a n=renameProgram (windowNet j) (IntegerPacket.seq (Shadow7.shape j) a n) ∧
    Shadow7.unrouted j a n=renameProgram (windowNet j) (IntegerPacket.back (Shadow7.shape j) a n) := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have ha : a < 15 := by omega
    have h:=(skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩))
    obtain ⟨f,r⟩:=ih (a+1) (by omega)
    have app (g : Wire → Wire) (P Q : Program) : renameProgram g (P++Q)=renameProgram g P++renameProgram g Q := List.map_append
    simp only [Shadow7.routed,Shadow7.unrouted,IntegerPacket.seq,IntegerPacket.back,app,f,r]
    constructor
    · exact congrArg (fun P=>P++_) (renameProgram_congr_support _ _ _ (fun q hq=>
        Shadow7.stable ha (List.mem_toFinset.mp (h.1 hq))))
    · exact congrArg (fun P=>_++P) (renameProgram_congr_support _ _ _ (fun q hq=>
        Shadow7.stable ha (List.mem_toFinset.mp (h.2 hq))))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem pull_routed (j:Fin 23) (i n:Nat) (bound:i+n≤15) (m:List Bool) (s:State) :
    pullState (windowNet j) (run (Shadow7.routed j i n) m s)=run (seq (Shadow7.shape j) i n) m (pullState (windowNet j) s) := by
  rw [(Shadow7.fixed_route j i n bound).1,run_rename _ (netInjective j)]

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_frame (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) :
    Triple (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.onRails j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h:=IntegerPacket.semantic (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m ready
  rw [←Shadow7.pull_routed j i n bound m s] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_records (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (s:State) (m:List Bool) (h:Shadow7.onRails j i z s.basis) :
    readCells (Shadow7.shape j) i n (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=SkywalkTrace.trace n z ∧
    ∀ d < i, cell (Shadow7.shape j) d (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=cell (Shadow7.shape j) d (mappedBasis j s.basis) := by
  have hh:=records (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m h
  rw [←Shadow7.pull_routed j i n bound m s] at hh
  exact hh

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_undo (j:Fin 23) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) :
    Restores (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.unrouted j i n) := by
  intro s m t ready
  have forward:=Shadow7.pull_routed j i n bound m s
  let actual:=run (Shadow7.routed j i n) m s
  have bk:pullState (windowNet j) (run (Shadow7.unrouted j i n) t actual)=run (back (Shadow7.shape j) i n) t (pullState (windowNet j) actual):=by
    rw [(Shadow7.fixed_route j i n bound).2,run_rename _ (netInjective j)]
  have fin:=IntegerPacket.roundtrip (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m t ready
  change pullState (windowNet j) actual=_ at forward
  rw [forward,fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h:=congrArg (fun x:State=>x.basis (windowNet j q)) bk
  change (run (Shadow7.unrouted j i n) t actual).basis (windowNet j (windowNet j q))=s.basis (windowNet j (windowNet j q)) at h
  have inv : windowNet j (windowNet j q)=q := by
    apply OB5.sig_invol
    have hj:=j.isLt
    simp [start];omega
  rwa [inv] at h

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket
attribute [local irreducible] run Shadow7.onRails
set_option maxHeartbeats 2000000

theorem split_run (j:Fin 23) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m n:List Bool)
    (ready:Shadow7.onRails j 0 z s.basis) (v:State)
    (active:Shadow7.onRails j 1 (SkywalkTrace.next z) v.basis)
    (first:cell (Shadow7.shape j) 0 (mappedBasis j v.basis)=
      cell (Shadow7.shape j) 0 (mappedBasis j (run (Shadow7.routed j 0 1) m s).basis)) :
    let out:=run (Shadow7.routed j 1 14) n v
    Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
    readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z := by
  have post:=Shadow7.route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have back:=Shadow7.route_records j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have front:=(Shadow7.route_records j 0 1 (by decide) z odd s m ready).1
  have firstValue:=congrArg List.head? front
  simp only [readCells,SkywalkTrace.trace,List.head?_cons,Option.some.injEq] at firstValue
  exact ⟨post.2,congr (congrArg List.cons ((back.2 0 (by decide)).trans (first.trans firstValue))) back.1⟩

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket

def watch (j:Fin 23) :=
  let p:=Shadow7.shape j
  let L:=ports p 1
  (L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket
set_option linter.unusedSimpArgs false

theorem watch_congr (j:Fin 23) (s t:State) (agree:∀q∈Shadow7.watch j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:Shadow7.onRails j 1 z s.basis) :
    Shadow7.onRails j 1 z t.basis ∧ cell (Shadow7.shape j) 0 (mappedBasis j t.basis)=cell (Shadow7.shape j) 0 (mappedBasis j s.basis) := by
  let p:=Shadow7.shape j
  let L:=ports p 1
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 1 14:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails

structure AdminResult (j:Fin 23) (reverse:Program) (src out:State) : Prop where
  phase : out.phase=src.phase
  unchanged : ∀q∈Shadow7.watch j,out.basis q=src.basis q
  undo : ∀m,run reverse m out=src

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails

theorem body_run (j:Fin 23) (admin reverse:Program) (s:State) (m:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z s.basis)
    (mid:let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (Shadow7.unbody j reverse) n out=s := by
  let src:=run (Shadow7.routed j 0 1) m s
  let t:=m.drop (measurementCount (Shadow7.routed j 0 1))
  let pre:=run admin t src
  let n:=t.drop (measurementCount admin)
  have head:=Shadow7.route_frame j 0 1 (by decide) z odd s m active
  have valid:Shadow7.onRails j 1 (SkywalkTrace.next z) src.basis:=head.2
  have pass:=Shadow7.watch_congr j src pre mid.unchanged _ valid
  have span:=Shadow7.split_run j z odd s m n active pre pass.1 pass.2
  have last:=Shadow7.route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n pass.1
  dsimp only [Shadow7.body,Shadow7.unbody]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack:=Shadow7.route_undo j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n r pass.1
  change run (Shadow7.unrouted j 0 1) _ (run reverse _ (run (Shadow7.unrouted j 1 14) r (run (Shadow7.routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact Shadow7.route_undo j 0 1 (by decide) z odd s m _ active

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

theorem ready_after_head (j:Fin 23) (P:Program) (s:State) (a b:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z s.basis)
    (preserve:∀t:State,∀q∈Shadow7.watch j,(run P b t).basis q=t.basis q) :
    Shadow7.onRails j 1 (SkywalkTrace.next z) (run P b (run (Shadow7.routed j 0 1) a s)).basis:=
  (Shadow7.watch_congr j _ _ (preserve _) _ (Shadow7.route_frame j 0 1 (by decide) z odd s a active).2).1

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def tickSites (j:Fin 23) (a:Nat) := ((ports (Shadow7.shape j) a).wires.map (windowNet j))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def spanSites (j:Fin 23) (a n:Nat) := (List.range' a n).flatMap (Shadow7.tickSites j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem route_sites (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (inP:q∈wires (Shadow7.routed j a n)) :
    q∈Shadow7.spanSites j a n := by
  induction n generalizing a with
  | zero=>simp [Shadow7.routed,wires] at inP
  | succ n ih=>
    rw [Shadow7.routed,wires_append,Finset.mem_union] at inP
    rw [Shadow7.spanSites,List.range'_succ,List.flatMap_cons,List.mem_append]
    rcases inP with h|h
    · rw [renameProgram_support,Finset.mem_image] at h
      obtain ⟨t,used,eq⟩:=h
      have ht:a<15:=by omega
      have inside:=List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok (Shadow7.shape j) ⟨a,ht⟩)).1 used)
      exact Or.inl (List.mem_map.mpr ⟨t,inside,(Shadow7.stable ht inside).symm.trans eq⟩)
    · exact Or.inr (ih (a+1) (by omega) h)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem route_outside (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (free:q∉Shadow7.spanSites j a n) (s:State) (m:List Bool) :
    (run (Shadow7.routed j a n) m s).basis q=s.basis q :=
  run_preserves_outside _ _ _ _ (fun used=>free (Shadow7.route_sites j a n lim q used))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem old_clear {j:Fin 23} {a n q:Nat} (lim:a+n≤15)
    (old:oldRange (start j+a) (windowNet j q)) : q∉Shadow7.spanSites j a n := by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by
    apply OB5.sig_invol
    have hj:=j.isLt;simp [start];omega
  rw [←eq,undo] at old
  have hj:=j.isLt
  simp only [IntegerPacket.ports,Shadow7.shape,Shadow7.smallBits,Shadow7.sbP,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  simp only [oldRange,start] at old
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction

theorem native_carry (j:Fin 23) (z:SkywalkRails.State) (s:State) (ready:Shadow7.onRails j 15 z s.basis) (q:Wire)
    (mem:q∈((ports (Shadow7.shape j) 15).carry.map (windowNet j))) : s.basis q=false:=by
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp mem
  exact (regValue_zero _ _).mp ready.2.2.2.1 _ hw

end ECDSAAdd.Entrant.StairPacket.Shadow7
