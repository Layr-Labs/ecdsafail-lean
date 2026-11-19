import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickBeforeStore0786
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickClosed7f1
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActual16ba
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActualc63a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFlagScratch8371
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickLoaded78b0
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPostReadyf724
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPrepared375e
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPreservedRecordsbaa4
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRetireActual981d
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoundtrip8ad0
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoutedRestore88ff
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickWholeac0c
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldJourney3425
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldRelation99df
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldRestore6ae6
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldStep5117
import ECDSAAdd.Submission.Entrant.PrizeScopeWindowFieldTen933e
import ECDSAAdd.Submission.Entrant.PrizeStair44PointMap486a9e3
import ECDSAAdd.Submission.Entrant.PrizeTail227303371
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary240
theorem load_cover (d:Bool) : wires (Partial.archiveLoad240 d) ⊆ rawPortsList.toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    have inside:∀j:Fin 155,loadMap j∈rawPortsList:=by decide +kernel
    exact List.mem_toFinset.mpr (inside ⟨w,small⟩)
  · decide +kernel
end ArchiveBoundary240
namespace ArchiveBoundary255
theorem load_cover (d:Bool) : wires (Partial.archiveLoad255 d) ⊆ rawPortsList.toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    have inside:∀j:Fin 155,loadMap j∈rawPortsList:=by decide +kernel
    exact List.mem_toFinset.mpr (inside ⟨w,small⟩)
  · decide +kernel
end ArchiveBoundary255
namespace ArchiveBoundary270
theorem load_cover (d:Bool) : wires (Partial.archiveLoad270 d) ⊆ rawPortsList.toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    have inside:∀j:Fin 155,loadMap j∈rawPortsList:=by decide +kernel
    exact List.mem_toFinset.mpr (inside ⟨w,small⟩)
  · decide +kernel
end ArchiveBoundary270
#print axioms ArchiveBoundary240.load_cover
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 270 q∉L.wires ∨ q=285
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
theorem observes (q:Wire) (h:readOnly q) (s:State) (m:List Bool) (prev:(run physP m s).basis 285=s.basis 285) : (run physP m s).basis q=s.basis q := by
  rcases h with h|rfl
  · exact run_preserves_outside _ _ _ _ (physical_free P supports.1 _ h)
  · exact prev
theorem oldPrefix : ∀i,readOnly (NativePack270.history i) := by decide +kernel
theorem oldBank : ∀i:Fin 23,readOnly (ArchiveBoundary270.rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EndTick


end

section

namespace ECDSAAdd.Entrant.StairPacket.FlipAudit
open Arithmetic
def ok (watched:Wire→Bool) : Instr→Bool
  | .X _ => true
  | i => !(watched (CodecBitSliceVerify.target i))
def logOne (watched:Wire→Bool) : Instr→List Wire
  | .X w => if watched w then [w] else []
  | _ => []
def log (watched:Wire→Bool) (p:Program) := p.flatMap (logOne watched)
def flip (q:Wire) : List Wire→Bool
  | []=>false
  | x::xs=>(decide (q=x)) ^^ flip q xs

theorem one (watched:Wire→Bool) (q:Wire) (wq:watched q=true) (i:Instr) (pass:ok watched i=true) (s:State) (m:List Bool) :
    (run [i] m s).basis q= (s.basis q ^^ flip q (logOne watched i)) := by
  cases i with
  | X a =>
    by_cases h:q=a
    · subst q;simp [run,writeBit,logOne,wq,flip]
    · cases hw:watched a <;> simp [run,writeBit,logOne,hw,flip,h]
  | CX a t | CCX a b t | measureX t cs ds =>
    have ne:q≠t:=by intro eq;subst q;simp [ok,CodecBitSliceVerify.target,wq] at pass
    simp [run,measureAndCorrect,writeBit,logOne,flip,ne]

theorem flip_append (q:Wire) (a b:List Wire) : flip q (a++b)= (flip q a ^^ flip q b):=by
  induction a with
  | nil => simp [flip]
  | cons w a ih=>simp [flip,ih]

theorem sound (watched:Wire→Bool) (p:Program) (q:Wire) (wq:watched q=true)
    (pass:p.all (ok watched)=true) (s:State) (m:List Bool) :
    (run p m s).basis q= (s.basis q ^^ flip q (log watched p)) := by
  induction p generalizing s m with
  | nil=>simp [run,log,flip]
  | cons i p ih=>
    simp only [List.all_cons,Bool.and_eq_true] at pass
    change (run ([i]++p) m s).basis q=_
    rw [run_append,ih pass.2,one watched q wq i pass.1]
    simp [log,flip_append]

theorem log_cat (w:Wire→Bool) (a b:Program) : log w (a++b)=log w a++log w b := by simp [log]
theorem cancel_all (xs:List Wire) (inside:∀w∈xs,flip w xs=false) (q:Wire) : flip q xs=false:=by
  by_cases h:q∈xs
  · exact inside _ h
  · clear inside
    induction xs with
    | nil=>rfl
    | cons a xs ih=>simp only [List.mem_cons,not_or] at h;simp [flip,h.1,ih h.2]
#print axioms sound
end ECDSAAdd.Entrant.StairPacket.FlipAudit


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
def tickSites (j:Fin 23) (a:Nat) := ((ports (shape j) a).wires.map (windowNet j))
def spanSites (j:Fin 23) (a n:Nat) := (List.range' a n).flatMap (tickSites j)
theorem route_sites (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (inP:q∈wires (routed j a n)) :
    q∈spanSites j a n := by
  induction n generalizing a with
  | zero=>simp [routed,wires] at inP
  | succ n ih=>
    rw [routed,wires_append,Finset.mem_union] at inP
    rw [spanSites,List.range'_succ,List.flatMap_cons,List.mem_append]
    rcases inP with h|h
    · rw [renameProgram_support,Finset.mem_image] at h
      obtain ⟨t,used,eq⟩:=h
      have ht:a<15:=by omega
      have inside:=List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok (shape j) ⟨a,ht⟩)).1 used)
      exact Or.inl (List.mem_map.mpr ⟨t,inside,(stable ht inside).symm.trans eq⟩)
    · exact Or.inr (ih (a+1) (by omega) h)
theorem route_outside (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (free:q∉spanSites j a n) (s:State) (m:List Bool) :
    (run (routed j a n) m s).basis q=s.basis q :=
  run_preserves_outside _ _ _ _ (fun used=>free (route_sites j a n lim q used))
def oldRange (t q:Nat) : Prop := (16≤q ∧ q+2≤16+t) ∨ (1044≤q ∧ q+2≤1044+t)
instance (t q:Nat) : Decidable (oldRange t q):=by unfold oldRange;infer_instance
theorem old_clear {j:Fin 23} {a n q:Nat} (lim:a+n≤15)
    (old:oldRange (start j+a) (windowNet j q)) : q∉spanSites j a n := by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by
    apply OB5.sig_invol
    have hj:=j.isLt;simp [start];omega
  rw [←eq,undo] at old
  have hj:=j.isLt
  simp only [IntegerPacket.ports,shape,smallBits,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  simp only [oldRange,start] at old
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega
#print axioms route_outside
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.SavedHigh
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
theorem mapped (ps:List (Wire×Wire)) (a b:Wire×Wire→Wire) (s t:BasisState) (eq:∀p∈ps,s (a p)=t (b p)) :
    regValue (ps.map a) s=regValue (ps.map b) t:=by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    have head:=eq p (by simp)
    have tail:=ih (fun v h=>eq v (by simp [h]))
    change (if s (a p) then 1 else 0)+2*regValue _ s=(if t (b p) then 1 else 0)+2*regValue _ t
    rw [head,tail]
theorem stored {lo hi g n f u neg far long} {L:SkywalkIntegerLayout} {net:Wire→Wire} (bits:Nat)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool)
    (packed:PackedCut lo hi g n f u neg far long (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (gate:net g=L.previous) (left:(hi.map Prod.fst).map net=L.a.drop bits) (right:(hi.map Prod.snd).map net=L.b.drop bits)
    (la:bits≤L.a.length) (lb:bits≤L.b.length) : regValue (hi.map Prod.snd) cut.basis=(z.u+z.v)/2^bits:=by
  have math:=mathematical _ _ _ _ _ _ input
  have tag:(pullState net raw).basis g=G:=(congrArg raw.basis gate).trans math.1
  have select (p:Wire×Wire) (h:p∈hi):cut.basis p.2=if G then raw.basis (net p.2) else raw.basis (net p.1):=by
    have e:=(packed.upper p h).2
    rw [tag] at e;exact e
  cases G with
  | false=>
    rw [mapped hi Prod.snd Prod.fst _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←unroute net _ _,left,shiftedValue _ _ la,show regValue L.a raw.basis=z.u+z.v from math.2.2.1]
  | true=>
    rw [mapped hi Prod.snd Prod.snd _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←unroute net _ _,right,shiftedValue _ _ lb,show regValue L.b raw.basis=z.u+z.v from math.2.2.1]
theorem three (a b c:Wire) (s:BasisState) (row:Nat)
    (ha:s a=row.testBit 12) (hb:s b=row.testBit 13) (hc:s c=row.testBit 14) :
    regValue [a,b,c] s=row/4096%8:=by
  simp only [regValue,List.foldr_cons,List.foldr_nil,ha,hb,hc,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  split <;> split <;> split <;> simp_all <;> omega
theorem assemble (b k:Nat) (z:SkywalkNat.State) (G S:Bool) (s:BasisState) (a c e:Wire) (rest:List Wire)
    (ha:s a=(shadowRow b k z G S).testBit 12) (hc:s c=(shadowRow b k z G S).testBit 13)
    (he:s e=(shadowRow b k z G S).testBit 14)
    (high:regValue rest s=(z.u+z.v)/2^(b+k+1+3)) :
    regValue ([a,c,e]++rest) s=(if Shadow.far b k z then Shadow.high b k z else 0):=by
  rw [regValue_append,three _ _ _ _ _ ha hc he,(tags b k z G S).2.2.2.2, high]
  have div:(z.u+z.v)/2^(b+k+1+3)=Shadow.high b k z/8:=by
    unfold Shadow.high Shadow.limb;rw [Nat.div_div_eq_div_mul,pow_add 2 (b+k+1) 3];rfl
  rw [div]
  change (if Shadow.far b k z then Shadow.high b k z%8 else 0)%8+8*(Shadow.high b k z/8)=_
  by_cases h:Shadow.far b k z
  · simp only [h,if_true];omega
  · simp only [h,if_false];unfold Shadow.far at h;omega
#print axioms stored
#print axioms assemble
end ECDSAAdd.Entrant.StairPacket.SavedHigh


end

section

namespace ECDSAAdd.Entrant.StairPacket.SharedSigned
open SkywalkRails IntegerHigh
set_option maxHeartbeats 2500000
theorem step_flags (g s:Bool) (z:SkywalkNat.State) (odd:z.v%2=1) :
    let c:=SkywalkTrace.code (encode g s z.u z.v)
    SkywalkTrace.next (encode g s z.u z.v)=
      encode c.1 (s ^^ c.2) (SkywalkNat.step z).u (SkywalkNat.step z).v:=by
  have hv:0<(z.v:Int):=by omega
  have vo:(z.v:Int)%2=1:=by omega
  rcases z with ⟨a,b⟩
  change 0<(b:Int) at hv
  change (b:Int)%2=1 at vo
  by_cases ev:a%2=0
  · have sh:=step_encode_even g s (a:Int) (b:Int) (by omega) hv vo (by omega)
    simp only [SkywalkTrace.next,SkywalkTrace.code,sh,railsOf,Bool.xor_false]
    by_cases za:a=0
    · subst a;simp [encode,SkywalkNat.step,signed]
    · simp [encode,SkywalkNat.step,za,ev]
  · have sh:=step_encode_odd g s (a:Int) (b:Int) (by omega) hv vo (by omega)
    simp only [SkywalkTrace.next,SkywalkTrace.code,sh,railsOf]
    have nz:a≠0:=by omega
    cases s <;> by_cases ab:b≤a <;> by_cases eq:a=b <;>
      simp_all [SkywalkNat.step,encode,signed] <;> (try split_ifs) <;> (try omega)
    all_goals dsimp only
    all_goals omega

def flags (g s:Bool) : List (Bool×Bool)→Bool×Bool
  | []=>(g,s)
  | c::cs=>flags c.1 (s ^^ c.2) cs
theorem lift (n:Nat) (g s:Bool) (z:SkywalkNat.State) (odd:z.v%2=1) :
    let out:=flags g s (SkywalkTrace.trace n (encode g s z.u z.v))
    SkywalkTrace.next^[n] (encode g s z.u z.v)=
      encode out.1 out.2 (SkywalkNat.step^[n] z).u (SkywalkNat.step^[n] z).v := by
  induction n generalizing z g s with
  | zero=>rfl
  | succ n ih=>
    simp only [Function.iterate_succ_apply,SkywalkTrace.trace,flags,step_flags g s z odd]
    exact ih _ _ _ (SkywalkNat.step_v_odd_pos z (by omega) odd).2
theorem same (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) (G S:Bool) :
    let t:=Shadow.reduced b 15 z
    let pair:=flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
    SkywalkTrace.next^[15] (encode G S z.u z.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v:=by
  have shadow:=lift 15 G S (Shadow.reduced b 15 z) (shadow_odd b z small odd)
  rw [true_records b z small odd G S] at shadow
  exact ⟨shadow,lift _ _ _ _ odd⟩
#print axioms same
end ECDSAAdd.Entrant.StairPacket.SharedSigned


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed

/-- The highest reserved carry is clean even when the individual native tick
has already shortened its carry list by one. -/
theorem stock_carry_end (d:Bool) (x p i:Nat) (hi:i≤512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) : s.basis 1812=false:=by
  obtain ⟨raw,hraw,hs⟩:=stage
  have fields:=(W.compactSkywalkStage_fields_iff base _ i hi base_pool_nodup raw.basis).mp hraw
  have none : 1812∉wires (Rolling1588.Integer.encodePrefix base d i):=by
    rw [Rolling1588.Integer.prefix_support_eq]
    intro mem
    obtain ⟨j,eq,lim⟩:=StackOB5Base.encodePrefix_mem i hi _ mem
    change 1812=j+16 at eq
    omega
  rw [hs,run_preserves_outside _ [] raw _ none]
  exact (regValue_zero _ _).mp fields.2.2.2.2.2.1 _ (by decide +kernel)
#print axioms stock_carry_end
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
/-- The ordinary full-width native steps, before inserting any history encoder. -/
def span (i:Nat) : Nat→Program
  | 0=>[]
  | n+1=>W.compactSkywalkTick base i ++ span (i+1) n
def oldStart (i:Nat) := if i=225 then i-5 else i-15
def oldCount (i:Nat) := if i=225 then 5 else 15
def sites (i:Nat) := (List.range' (oldStart i) (oldCount i)).flatMap fun r=>[base r,base (1028+r)]
/-- The history snapshot comes from this window after its real pack/archive writes. -/
def overlay (i:Nat) (wide history:State) : State :=
  ⟨wide.phase,fun q=>if q∈sites i then history.basis q else wide.basis q⟩
def origin (i:Nat) (raw history:State) : State :=
  overlay i (pullState (OB5.sig (i+14)) (run (span i 15) [] raw)) history
def endRaw (i:Nat) (raw history:State) : State := pullState (OB5.sig (i+14)) (origin i raw history)
theorem endpoint (i:Nat) (limit:i+14≤511) (raw history:State) :
    pullState (OB5.sig (i+14)) (endRaw i raw history)=origin i raw history :=
  OB5.pull_invol _ limit _
theorem outside (i:Nat) (raw history:State) (q:Wire) (h:q∉sites i) :
    (origin i raw history).basis q=(run (span i 15) [] raw).basis (OB5.sig (i+14) q) := by
  simp [origin,overlay,h,pullState]
theorem inside (i:Nat) (raw history:State) (q:Wire) (h:q∈sites i) :
    (origin i raw history).basis q=history.basis q := by simp [origin,overlay,h]
def Earlier (i:Nat) (q:Wire) := ∃r:Nat,r+2≤ i ∧ (q=base r ∨ q=base (1028+r))
def Coherent (i:Nat) (actual reference:State) :=
  actual.phase=reference.phase ∧ ∀q,¬Earlier i q → actual.basis q=reference.basis q
theorem earlier_mono {i j q} (le:i≤j) (h:Earlier i q) : Earlier j q := by
  obtain ⟨r,h,e⟩:=h;exact ⟨r,Nat.le_trans h le,e⟩
theorem away {i q} (hi:i<512) (h:Earlier i q) : q∉(W.compactSkywalkTickLayout base i).wires := by
  obtain ⟨r,lt,e|e⟩:=h
  all_goals subst q;have pos:i≠0:=by omega
  all_goals have width:=W.compactSkywalkTick_width_bounds i hi
  all_goals apply W.compactSkywalkStage_tick_away base i hi base_pool_nodup
  all_goals try simp [skywalkPoolPreviousId,pos]
  all_goals omega
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3500000
set_option maxRecDepth 18000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

theorem canonical_reads (i:Nat) (hi:i<512) (w s:State)
    (view:∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=w.basis q) (m:List Bool) :
    ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,
      (run (W.compactSkywalkTick base i) m s).basis q=(run (W.compactSkywalkTick base i) m w).basis q := by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have touched:=(run_local_increment P s w m (fun q h=>view _ (sub h))).2
  intro q hit
  by_cases used:q∈wires P
  · exact touched q used
  · exact (run_preserves_outside _ m s q used).trans ((view _ hit).trans (run_preserves_outside _ m w q used).symm)

theorem after_reference (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 270 original.basis) :
    ∃ref:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 270 ref.basis ∧
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 271 (run canonical [] ref).basis ∧
      Reads raw ref ∧ Reads (run canonical [] raw) (run canonical [] ref) := by
  obtain ⟨ref,hs,agree⟩:=local_reference 270 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have r:Reads raw ref:=fun q h=>(read q h).trans (agree q h)
  exact ⟨ref,hs,(W.compactSkywalkStageStep base base_pool_nodup x p 270 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).2,r,
    canonical_reads 270 (by decide) ref raw r []⟩

theorem pastG (i j:Nat) (hi:i≤512) (hj:j < i) (r:SkywalkRails.State) (b:BasisState)
    (hs:W.CompactSkywalkStage base r i b) :
    b (base j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 :=
  (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.1 j hj).1

theorem full_carry (i:Nat) (hi:i≤512) (r:SkywalkRails.State) (b:BasisState) (hs:W.CompactSkywalkStage base r i b) :
    ∀q∈wireBlock base 1540 257,b q=false :=
  (regValue_zero _ _).mp (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.2.2.1)

end ECDSAAdd.Entrant.StairPacket.EndTick


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
attribute [local irreducible] run routed
def Kept (ps:Ports) (d:Bool) (row:Nat) (s:State) := ∀i:Fin 16,s.basis (ps ⟨i.val,by omega⟩)=(get (code d) i.val).testBit row
theorem body_keeps (j:Fin 23) (P:Program) (ps:Ports) (d:Bool) (row:Nat) (s:State) (m:List Bool)
    (off:∀i:Fin 16,ps ⟨i.val,by omega⟩∉spanSites j 1 14)
    (hold:Frame ps (code d) row (run P (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s))) :
    Kept ps d row (run (body j P) m s) := by
  intro i
  simp only [body,run_append,run_take]
  exact (route_outside j 1 14 (by decide) _ (off i) _ _).trans (hold ⟨i.val,by omega⟩)
namespace NativePack240
open ArchiveBoundary240
theorem encoded_outside : ∀i:Fin 16,codePorts ⟨i.val,by omega⟩∉spanSites idx 1 14 := by
  have old:∀i:Fin 16,oldRange (start idx+1) (windowNet idx (codePorts ⟨i.val,by omega⟩)):=by decide +kernel
  exact fun i=>old_clear (by decide) (old i)
attribute [local irreducible] onRails Kept measurementCount body Frame rawPorts codePorts withArchive program history code
theorem window_keeps (d:Bool) (s:State) (m:List Bool) (row:Nat)
    (hold:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (window d) m s) :=
  body_keeps idx (withArchive d) codePorts d row s m encoded_outside hold
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem encoded_outside : ∀i:Fin 16,codePorts ⟨i.val,by omega⟩∉spanSites idx 1 14 := by
  have old:∀i:Fin 16,oldRange (start idx+1) (windowNet idx (codePorts ⟨i.val,by omega⟩)):=by decide +kernel
  exact fun i=>old_clear (by decide) (old i)
attribute [local irreducible] onRails Kept measurementCount body Frame rawPorts codePorts withArchive program history code
theorem window_keeps (d:Bool) (s:State) (m:List Bool) (row:Nat)
    (hold:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (window d) m s) :=
  body_keeps idx (withArchive d) codePorts d row s m encoded_outside hold
end NativePack255
#print axioms NativePack240.window_keeps
#print axioms NativePack255.window_keeps
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def watched (q:Wire) := decide (16≤q ∧ q<256 ∨ 1044≤q ∧ q<1284)
theorem guardleave225Part0 : (Partial.leave225Part0).all (ok watched)=true ∧ log watched Partial.leave225Part0=[241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255] := by decide +kernel
theorem guardleave225Part1 : (Partial.leave225Part1).all (ok watched)=true ∧ log watched Partial.leave225Part1=[] := by decide +kernel
theorem guardleave225Part2 : (Partial.leave225Part2).all (ok watched)=true ∧ log watched Partial.leave225Part2=[] := by decide +kernel
theorem guardleave225Part3 : (Partial.leave225Part3).all (ok watched)=true ∧ log watched Partial.leave225Part3=[] := by decide +kernel
theorem guardleave225Part4 : (Partial.leave225Part4).all (ok watched)=true ∧ log watched Partial.leave225Part4=[] := by decide +kernel
theorem guardleave225Part5 : (Partial.leave225Part5).all (ok watched)=true ∧ log watched Partial.leave225Part5=[] := by decide +kernel
theorem guardleave225Part6 : (Partial.leave225Part6).all (ok watched)=true ∧ log watched Partial.leave225Part6=[] := by decide +kernel
theorem guardleave225Part7 : (Partial.leave225Part7).all (ok watched)=true ∧ log watched Partial.leave225Part7=[] := by decide +kernel
theorem guardleave225Part8 : (Partial.leave225Part8).all (ok watched)=true ∧ log watched Partial.leave225Part8=[] := by decide +kernel
theorem guardleave225Part9 : (Partial.leave225Part9).all (ok watched)=true ∧ log watched Partial.leave225Part9=[] := by decide +kernel
theorem guardleave225Part10 : (Partial.leave225Part10).all (ok watched)=true ∧ log watched Partial.leave225Part10=[] := by decide +kernel
theorem guardleave225Part11 : (Partial.leave225Part11).all (ok watched)=true ∧ log watched Partial.leave225Part11=[] := by decide +kernel
theorem guardleave225Part12 : (Partial.leave225Part12).all (ok watched)=true ∧ log watched Partial.leave225Part12=[] := by decide +kernel
theorem guardleave225Part13 : (Partial.leave225Part13).all (ok watched)=true ∧ log watched Partial.leave225Part13=[] := by decide +kernel
theorem guardleave225Part14 : (Partial.leave225Part14).all (ok watched)=true ∧ log watched Partial.leave225Part14=[] := by decide +kernel
theorem guardleave225Part15 : (Partial.leave225Part15).all (ok watched)=true ∧ log watched Partial.leave225Part15=[] := by decide +kernel
theorem guardleave225Part16 : (Partial.leave225Part16).all (ok watched)=true ∧ log watched Partial.leave225Part16=[] := by decide +kernel
theorem guardleave225Part17 : (Partial.leave225Part17).all (ok watched)=true ∧ log watched Partial.leave225Part17=[] := by decide +kernel
theorem guardleave225Part18 : (Partial.leave225Part18).all (ok watched)=true ∧ log watched Partial.leave225Part18=[] := by decide +kernel
theorem guardleave225Part19 : (Partial.leave225Part19).all (ok watched)=true ∧ log watched Partial.leave225Part19=[] := by decide +kernel
theorem guardleave225Part20 : (Partial.leave225Part20).all (ok watched)=true ∧ log watched Partial.leave225Part20=[] := by decide +kernel
theorem guardleave225Part21 : (Partial.leave225Part21).all (ok watched)=true ∧ log watched Partial.leave225Part21=[] := by decide +kernel
theorem guardleave225Part22 : (Partial.leave225Part22).all (ok watched)=true ∧ log watched Partial.leave225Part22=[] := by decide +kernel
theorem guardleave225Part23 : (Partial.leave225Part23).all (ok watched)=true ∧ log watched Partial.leave225Part23=[] := by decide +kernel
theorem guardleave225Part24 : (Partial.leave225Part24).all (ok watched)=true ∧ log watched Partial.leave225Part24=[] := by decide +kernel
theorem guardleave225Part25 : (Partial.leave225Part25).all (ok watched)=true ∧ log watched Partial.leave225Part25=[] := by decide +kernel
theorem guardleave225Part26 : (Partial.leave225Part26).all (ok watched)=true ∧ log watched Partial.leave225Part26=[] := by decide +kernel
theorem guardleave225Part27 : (Partial.leave225Part27).all (ok watched)=true ∧ log watched Partial.leave225Part27=[] := by decide +kernel
theorem guardleave225Part28 : (Partial.leave225Part28).all (ok watched)=true ∧ log watched Partial.leave225Part28=[] := by decide +kernel
theorem guardleave225Part29 : (Partial.leave225Part29).all (ok watched)=true ∧ log watched Partial.leave225Part29=[241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269] := by decide +kernel
theorem guardleave225Part30 : (Partial.leave225Part30).all (ok watched)=true ∧ log watched Partial.leave225Part30=[] := by decide +kernel
theorem guardleave225Part31 : (Partial.leave225Part31).all (ok watched)=true ∧ log watched Partial.leave225Part31=[] := by decide +kernel
theorem guardleave225Part32 : (Partial.leave225Part32).all (ok watched)=true ∧ log watched Partial.leave225Part32=[] := by decide +kernel
theorem guardleave225Part33 : (Partial.leave225Part33).all (ok watched)=true ∧ log watched Partial.leave225Part33=[] := by decide +kernel
theorem admissible : (Partial.leave225).all (ok watched)=true := by
  simp only [Partial.leave225,List.all_append,guardleave225Part0.1,guardleave225Part1.1,guardleave225Part2.1,guardleave225Part3.1,guardleave225Part4.1,guardleave225Part5.1,guardleave225Part6.1,guardleave225Part7.1,guardleave225Part8.1,guardleave225Part9.1,guardleave225Part10.1,guardleave225Part11.1,guardleave225Part12.1,guardleave225Part13.1,guardleave225Part14.1,guardleave225Part15.1,guardleave225Part16.1,guardleave225Part17.1,guardleave225Part18.1,guardleave225Part19.1,guardleave225Part20.1,guardleave225Part21.1,guardleave225Part22.1,guardleave225Part23.1,guardleave225Part24.1,guardleave225Part25.1,guardleave225Part26.1,guardleave225Part27.1,guardleave225Part28.1,guardleave225Part29.1,guardleave225Part30.1,guardleave225Part31.1,guardleave225Part32.1,guardleave225Part33.1,Bool.and_self]
theorem ledger : log watched Partial.leave225=[241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269] := by
  simp only [Partial.leave225,log_cat,guardleave225Part0.2,guardleave225Part1.2,guardleave225Part2.2,guardleave225Part3.2,guardleave225Part4.2,guardleave225Part5.2,guardleave225Part6.2,guardleave225Part7.2,guardleave225Part8.2,guardleave225Part9.2,guardleave225Part10.2,guardleave225Part11.2,guardleave225Part12.2,guardleave225Part13.2,guardleave225Part14.2,guardleave225Part15.2,guardleave225Part16.2,guardleave225Part17.2,guardleave225Part18.2,guardleave225Part19.2,guardleave225Part20.2,guardleave225Part21.2,guardleave225Part22.2,guardleave225Part23.2,guardleave225Part24.2,guardleave225Part25.2,guardleave225Part26.2,guardleave225Part27.2,guardleave225Part28.2,guardleave225Part29.2,guardleave225Part30.2,guardleave225Part31.2,guardleave225Part32.2,guardleave225Part33.2];rfl
theorem preserves (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave225 m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissible,ledger]
  have paired:∀w∈([241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269]:List Wire),flip w [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
theorem guardleave225InvPart0 : (Partial.leave225InvPart0).all (ok watched)=true ∧ log watched Partial.leave225InvPart0=[] := by decide +kernel
theorem guardleave225InvPart1 : (Partial.leave225InvPart1).all (ok watched)=true ∧ log watched Partial.leave225InvPart1=[] := by decide +kernel
theorem guardleave225InvPart2 : (Partial.leave225InvPart2).all (ok watched)=true ∧ log watched Partial.leave225InvPart2=[] := by decide +kernel
theorem guardleave225InvPart3 : (Partial.leave225InvPart3).all (ok watched)=true ∧ log watched Partial.leave225InvPart3=[1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269] := by decide +kernel
theorem guardleave225InvPart4 : (Partial.leave225InvPart4).all (ok watched)=true ∧ log watched Partial.leave225InvPart4=[255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241] := by decide +kernel
theorem guardleave225InvPart5 : (Partial.leave225InvPart5).all (ok watched)=true ∧ log watched Partial.leave225InvPart5=[] := by decide +kernel
theorem guardleave225InvPart6 : (Partial.leave225InvPart6).all (ok watched)=true ∧ log watched Partial.leave225InvPart6=[] := by decide +kernel
theorem guardleave225InvPart7 : (Partial.leave225InvPart7).all (ok watched)=true ∧ log watched Partial.leave225InvPart7=[] := by decide +kernel
theorem guardleave225InvPart8 : (Partial.leave225InvPart8).all (ok watched)=true ∧ log watched Partial.leave225InvPart8=[] := by decide +kernel
theorem guardleave225InvPart9 : (Partial.leave225InvPart9).all (ok watched)=true ∧ log watched Partial.leave225InvPart9=[] := by decide +kernel
theorem guardleave225InvPart10 : (Partial.leave225InvPart10).all (ok watched)=true ∧ log watched Partial.leave225InvPart10=[] := by decide +kernel
theorem guardleave225InvPart11 : (Partial.leave225InvPart11).all (ok watched)=true ∧ log watched Partial.leave225InvPart11=[] := by decide +kernel
theorem guardleave225InvPart12 : (Partial.leave225InvPart12).all (ok watched)=true ∧ log watched Partial.leave225InvPart12=[] := by decide +kernel
theorem guardleave225InvPart13 : (Partial.leave225InvPart13).all (ok watched)=true ∧ log watched Partial.leave225InvPart13=[] := by decide +kernel
theorem guardleave225InvPart14 : (Partial.leave225InvPart14).all (ok watched)=true ∧ log watched Partial.leave225InvPart14=[] := by decide +kernel
theorem guardleave225InvPart15 : (Partial.leave225InvPart15).all (ok watched)=true ∧ log watched Partial.leave225InvPart15=[] := by decide +kernel
theorem guardleave225InvPart16 : (Partial.leave225InvPart16).all (ok watched)=true ∧ log watched Partial.leave225InvPart16=[] := by decide +kernel
theorem guardleave225InvPart17 : (Partial.leave225InvPart17).all (ok watched)=true ∧ log watched Partial.leave225InvPart17=[] := by decide +kernel
theorem guardleave225InvPart18 : (Partial.leave225InvPart18).all (ok watched)=true ∧ log watched Partial.leave225InvPart18=[] := by decide +kernel
theorem guardleave225InvPart19 : (Partial.leave225InvPart19).all (ok watched)=true ∧ log watched Partial.leave225InvPart19=[] := by decide +kernel
theorem guardleave225InvPart20 : (Partial.leave225InvPart20).all (ok watched)=true ∧ log watched Partial.leave225InvPart20=[] := by decide +kernel
theorem guardleave225InvPart21 : (Partial.leave225InvPart21).all (ok watched)=true ∧ log watched Partial.leave225InvPart21=[] := by decide +kernel
theorem guardleave225InvPart22 : (Partial.leave225InvPart22).all (ok watched)=true ∧ log watched Partial.leave225InvPart22=[] := by decide +kernel
theorem guardleave225InvPart23 : (Partial.leave225InvPart23).all (ok watched)=true ∧ log watched Partial.leave225InvPart23=[] := by decide +kernel
theorem guardleave225InvPart24 : (Partial.leave225InvPart24).all (ok watched)=true ∧ log watched Partial.leave225InvPart24=[] := by decide +kernel
theorem guardleave225InvPart25 : (Partial.leave225InvPart25).all (ok watched)=true ∧ log watched Partial.leave225InvPart25=[] := by decide +kernel
theorem guardleave225InvPart26 : (Partial.leave225InvPart26).all (ok watched)=true ∧ log watched Partial.leave225InvPart26=[] := by decide +kernel
theorem guardleave225InvPart27 : (Partial.leave225InvPart27).all (ok watched)=true ∧ log watched Partial.leave225InvPart27=[] := by decide +kernel
theorem guardleave225InvPart28 : (Partial.leave225InvPart28).all (ok watched)=true ∧ log watched Partial.leave225InvPart28=[] := by decide +kernel
theorem guardleave225InvPart29 : (Partial.leave225InvPart29).all (ok watched)=true ∧ log watched Partial.leave225InvPart29=[] := by decide +kernel
theorem guardleave225InvPart30 : (Partial.leave225InvPart30).all (ok watched)=true ∧ log watched Partial.leave225InvPart30=[] := by decide +kernel
theorem guardleave225InvPart31 : (Partial.leave225InvPart31).all (ok watched)=true ∧ log watched Partial.leave225InvPart31=[] := by decide +kernel
theorem guardleave225InvPart32 : (Partial.leave225InvPart32).all (ok watched)=true ∧ log watched Partial.leave225InvPart32=[255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241] := by decide +kernel
theorem guardleave225InvPart33 : (Partial.leave225InvPart33).all (ok watched)=true ∧ log watched Partial.leave225InvPart33=[] := by decide +kernel
theorem admissibleInv : (Partial.leave225Inv).all (ok watched)=true := by
  simp only [Partial.leave225Inv,List.all_append,guardleave225InvPart0.1,guardleave225InvPart1.1,guardleave225InvPart2.1,guardleave225InvPart3.1,guardleave225InvPart4.1,guardleave225InvPart5.1,guardleave225InvPart6.1,guardleave225InvPart7.1,guardleave225InvPart8.1,guardleave225InvPart9.1,guardleave225InvPart10.1,guardleave225InvPart11.1,guardleave225InvPart12.1,guardleave225InvPart13.1,guardleave225InvPart14.1,guardleave225InvPart15.1,guardleave225InvPart16.1,guardleave225InvPart17.1,guardleave225InvPart18.1,guardleave225InvPart19.1,guardleave225InvPart20.1,guardleave225InvPart21.1,guardleave225InvPart22.1,guardleave225InvPart23.1,guardleave225InvPart24.1,guardleave225InvPart25.1,guardleave225InvPart26.1,guardleave225InvPart27.1,guardleave225InvPart28.1,guardleave225InvPart29.1,guardleave225InvPart30.1,guardleave225InvPart31.1,guardleave225InvPart32.1,guardleave225InvPart33.1,Bool.and_self]
theorem ledgerInv : log watched Partial.leave225Inv=[1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241] := by
  simp only [Partial.leave225Inv,log_cat,guardleave225InvPart0.2,guardleave225InvPart1.2,guardleave225InvPart2.2,guardleave225InvPart3.2,guardleave225InvPart4.2,guardleave225InvPart5.2,guardleave225InvPart6.2,guardleave225InvPart7.2,guardleave225InvPart8.2,guardleave225InvPart9.2,guardleave225InvPart10.2,guardleave225InvPart11.2,guardleave225InvPart12.2,guardleave225InvPart13.2,guardleave225InvPart14.2,guardleave225InvPart15.2,guardleave225InvPart16.2,guardleave225InvPart17.2,guardleave225InvPart18.2,guardleave225InvPart19.2,guardleave225InvPart20.2,guardleave225InvPart21.2,guardleave225InvPart22.2,guardleave225InvPart23.2,guardleave225InvPart24.2,guardleave225InvPart25.2,guardleave225InvPart26.2,guardleave225InvPart27.2,guardleave225InvPart28.2,guardleave225InvPart29.2,guardleave225InvPart30.2,guardleave225InvPart31.2,guardleave225InvPart32.2,guardleave225InvPart33.2];rfl
theorem preservesInv (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave225Inv m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissibleInv,ledgerInv]
  have paired:∀w∈([1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241]:List Wire),flip w [1269, 1270, 1271, 1272, 1273, 1273, 1272, 1271, 1270, 1269, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
#print axioms preserves
end ECDSAAdd.Entrant.StairPacket.Leave225Records


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def watched (q:Wire) := decide (16≤q ∧ q<271 ∨ 1044≤q ∧ q<1299)
theorem guardleave240Part0 : (Partial.leave240Part0).all (ok watched)=true ∧ log watched Partial.leave240Part0=[256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270] := by decide +kernel
theorem guardleave240Part1 : (Partial.leave240Part1).all (ok watched)=true ∧ log watched Partial.leave240Part1=[] := by decide +kernel
theorem guardleave240Part2 : (Partial.leave240Part2).all (ok watched)=true ∧ log watched Partial.leave240Part2=[] := by decide +kernel
theorem guardleave240Part3 : (Partial.leave240Part3).all (ok watched)=true ∧ log watched Partial.leave240Part3=[] := by decide +kernel
theorem guardleave240Part4 : (Partial.leave240Part4).all (ok watched)=true ∧ log watched Partial.leave240Part4=[] := by decide +kernel
theorem guardleave240Part5 : (Partial.leave240Part5).all (ok watched)=true ∧ log watched Partial.leave240Part5=[] := by decide +kernel
theorem guardleave240Part6 : (Partial.leave240Part6).all (ok watched)=true ∧ log watched Partial.leave240Part6=[] := by decide +kernel
theorem guardleave240Part7 : (Partial.leave240Part7).all (ok watched)=true ∧ log watched Partial.leave240Part7=[] := by decide +kernel
theorem guardleave240Part8 : (Partial.leave240Part8).all (ok watched)=true ∧ log watched Partial.leave240Part8=[] := by decide +kernel
theorem guardleave240Part9 : (Partial.leave240Part9).all (ok watched)=true ∧ log watched Partial.leave240Part9=[] := by decide +kernel
theorem guardleave240Part10 : (Partial.leave240Part10).all (ok watched)=true ∧ log watched Partial.leave240Part10=[] := by decide +kernel
theorem guardleave240Part11 : (Partial.leave240Part11).all (ok watched)=true ∧ log watched Partial.leave240Part11=[] := by decide +kernel
theorem guardleave240Part12 : (Partial.leave240Part12).all (ok watched)=true ∧ log watched Partial.leave240Part12=[] := by decide +kernel
theorem guardleave240Part13 : (Partial.leave240Part13).all (ok watched)=true ∧ log watched Partial.leave240Part13=[] := by decide +kernel
theorem guardleave240Part14 : (Partial.leave240Part14).all (ok watched)=true ∧ log watched Partial.leave240Part14=[] := by decide +kernel
theorem guardleave240Part15 : (Partial.leave240Part15).all (ok watched)=true ∧ log watched Partial.leave240Part15=[] := by decide +kernel
theorem guardleave240Part16 : (Partial.leave240Part16).all (ok watched)=true ∧ log watched Partial.leave240Part16=[] := by decide +kernel
theorem guardleave240Part17 : (Partial.leave240Part17).all (ok watched)=true ∧ log watched Partial.leave240Part17=[] := by decide +kernel
theorem guardleave240Part18 : (Partial.leave240Part18).all (ok watched)=true ∧ log watched Partial.leave240Part18=[] := by decide +kernel
theorem guardleave240Part19 : (Partial.leave240Part19).all (ok watched)=true ∧ log watched Partial.leave240Part19=[] := by decide +kernel
theorem guardleave240Part20 : (Partial.leave240Part20).all (ok watched)=true ∧ log watched Partial.leave240Part20=[] := by decide +kernel
theorem guardleave240Part21 : (Partial.leave240Part21).all (ok watched)=true ∧ log watched Partial.leave240Part21=[] := by decide +kernel
theorem guardleave240Part22 : (Partial.leave240Part22).all (ok watched)=true ∧ log watched Partial.leave240Part22=[] := by decide +kernel
theorem guardleave240Part23 : (Partial.leave240Part23).all (ok watched)=true ∧ log watched Partial.leave240Part23=[] := by decide +kernel
theorem guardleave240Part24 : (Partial.leave240Part24).all (ok watched)=true ∧ log watched Partial.leave240Part24=[] := by decide +kernel
theorem guardleave240Part25 : (Partial.leave240Part25).all (ok watched)=true ∧ log watched Partial.leave240Part25=[] := by decide +kernel
theorem guardleave240Part26 : (Partial.leave240Part26).all (ok watched)=true ∧ log watched Partial.leave240Part26=[] := by decide +kernel
theorem guardleave240Part27 : (Partial.leave240Part27).all (ok watched)=true ∧ log watched Partial.leave240Part27=[] := by decide +kernel
theorem guardleave240Part28 : (Partial.leave240Part28).all (ok watched)=true ∧ log watched Partial.leave240Part28=[] := by decide +kernel
theorem guardleave240Part29 : (Partial.leave240Part29).all (ok watched)=true ∧ log watched Partial.leave240Part29=[] := by decide +kernel
theorem guardleave240Part30 : (Partial.leave240Part30).all (ok watched)=true ∧ log watched Partial.leave240Part30=[256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270] := by decide +kernel
theorem guardleave240Part31 : (Partial.leave240Part31).all (ok watched)=true ∧ log watched Partial.leave240Part31=[1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284] := by decide +kernel
theorem guardleave240Part32 : (Partial.leave240Part32).all (ok watched)=true ∧ log watched Partial.leave240Part32=[] := by decide +kernel
theorem guardleave240Part33 : (Partial.leave240Part33).all (ok watched)=true ∧ log watched Partial.leave240Part33=[] := by decide +kernel
theorem guardleave240Part34 : (Partial.leave240Part34).all (ok watched)=true ∧ log watched Partial.leave240Part34=[] := by decide +kernel
theorem guardleave240Part35 : (Partial.leave240Part35).all (ok watched)=true ∧ log watched Partial.leave240Part35=[] := by decide +kernel
theorem admissible : (Partial.leave240).all (ok watched)=true := by
  simp only [Partial.leave240,List.all_append,guardleave240Part0.1,guardleave240Part1.1,guardleave240Part2.1,guardleave240Part3.1,guardleave240Part4.1,guardleave240Part5.1,guardleave240Part6.1,guardleave240Part7.1,guardleave240Part8.1,guardleave240Part9.1,guardleave240Part10.1,guardleave240Part11.1,guardleave240Part12.1,guardleave240Part13.1,guardleave240Part14.1,guardleave240Part15.1,guardleave240Part16.1,guardleave240Part17.1,guardleave240Part18.1,guardleave240Part19.1,guardleave240Part20.1,guardleave240Part21.1,guardleave240Part22.1,guardleave240Part23.1,guardleave240Part24.1,guardleave240Part25.1,guardleave240Part26.1,guardleave240Part27.1,guardleave240Part28.1,guardleave240Part29.1,guardleave240Part30.1,guardleave240Part31.1,guardleave240Part32.1,guardleave240Part33.1,guardleave240Part34.1,guardleave240Part35.1,Bool.and_self]
theorem ledger : log watched Partial.leave240=[256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284] := by
  simp only [Partial.leave240,log_cat,guardleave240Part0.2,guardleave240Part1.2,guardleave240Part2.2,guardleave240Part3.2,guardleave240Part4.2,guardleave240Part5.2,guardleave240Part6.2,guardleave240Part7.2,guardleave240Part8.2,guardleave240Part9.2,guardleave240Part10.2,guardleave240Part11.2,guardleave240Part12.2,guardleave240Part13.2,guardleave240Part14.2,guardleave240Part15.2,guardleave240Part16.2,guardleave240Part17.2,guardleave240Part18.2,guardleave240Part19.2,guardleave240Part20.2,guardleave240Part21.2,guardleave240Part22.2,guardleave240Part23.2,guardleave240Part24.2,guardleave240Part25.2,guardleave240Part26.2,guardleave240Part27.2,guardleave240Part28.2,guardleave240Part29.2,guardleave240Part30.2,guardleave240Part31.2,guardleave240Part32.2,guardleave240Part33.2,guardleave240Part34.2,guardleave240Part35.2];rfl
theorem preserves (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave240 m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissible,ledger]
  have paired:∀w∈([256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284]:List Wire),flip w [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
theorem guardleave240InvPart0 : (Partial.leave240InvPart0).all (ok watched)=true ∧ log watched Partial.leave240InvPart0=[] := by decide +kernel
theorem guardleave240InvPart1 : (Partial.leave240InvPart1).all (ok watched)=true ∧ log watched Partial.leave240InvPart1=[] := by decide +kernel
theorem guardleave240InvPart2 : (Partial.leave240InvPart2).all (ok watched)=true ∧ log watched Partial.leave240InvPart2=[] := by decide +kernel
theorem guardleave240InvPart3 : (Partial.leave240InvPart3).all (ok watched)=true ∧ log watched Partial.leave240InvPart3=[1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284] := by decide +kernel
theorem guardleave240InvPart4 : (Partial.leave240InvPart4).all (ok watched)=true ∧ log watched Partial.leave240InvPart4=[270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256] := by decide +kernel
theorem guardleave240InvPart5 : (Partial.leave240InvPart5).all (ok watched)=true ∧ log watched Partial.leave240InvPart5=[] := by decide +kernel
theorem guardleave240InvPart6 : (Partial.leave240InvPart6).all (ok watched)=true ∧ log watched Partial.leave240InvPart6=[] := by decide +kernel
theorem guardleave240InvPart7 : (Partial.leave240InvPart7).all (ok watched)=true ∧ log watched Partial.leave240InvPart7=[] := by decide +kernel
theorem guardleave240InvPart8 : (Partial.leave240InvPart8).all (ok watched)=true ∧ log watched Partial.leave240InvPart8=[] := by decide +kernel
theorem guardleave240InvPart9 : (Partial.leave240InvPart9).all (ok watched)=true ∧ log watched Partial.leave240InvPart9=[] := by decide +kernel
theorem guardleave240InvPart10 : (Partial.leave240InvPart10).all (ok watched)=true ∧ log watched Partial.leave240InvPart10=[] := by decide +kernel
theorem guardleave240InvPart11 : (Partial.leave240InvPart11).all (ok watched)=true ∧ log watched Partial.leave240InvPart11=[] := by decide +kernel
theorem guardleave240InvPart12 : (Partial.leave240InvPart12).all (ok watched)=true ∧ log watched Partial.leave240InvPart12=[] := by decide +kernel
theorem guardleave240InvPart13 : (Partial.leave240InvPart13).all (ok watched)=true ∧ log watched Partial.leave240InvPart13=[] := by decide +kernel
theorem guardleave240InvPart14 : (Partial.leave240InvPart14).all (ok watched)=true ∧ log watched Partial.leave240InvPart14=[] := by decide +kernel
theorem guardleave240InvPart15 : (Partial.leave240InvPart15).all (ok watched)=true ∧ log watched Partial.leave240InvPart15=[] := by decide +kernel
theorem guardleave240InvPart16 : (Partial.leave240InvPart16).all (ok watched)=true ∧ log watched Partial.leave240InvPart16=[] := by decide +kernel
theorem guardleave240InvPart17 : (Partial.leave240InvPart17).all (ok watched)=true ∧ log watched Partial.leave240InvPart17=[] := by decide +kernel
theorem guardleave240InvPart18 : (Partial.leave240InvPart18).all (ok watched)=true ∧ log watched Partial.leave240InvPart18=[] := by decide +kernel
theorem guardleave240InvPart19 : (Partial.leave240InvPart19).all (ok watched)=true ∧ log watched Partial.leave240InvPart19=[] := by decide +kernel
theorem guardleave240InvPart20 : (Partial.leave240InvPart20).all (ok watched)=true ∧ log watched Partial.leave240InvPart20=[] := by decide +kernel
theorem guardleave240InvPart21 : (Partial.leave240InvPart21).all (ok watched)=true ∧ log watched Partial.leave240InvPart21=[] := by decide +kernel
theorem guardleave240InvPart22 : (Partial.leave240InvPart22).all (ok watched)=true ∧ log watched Partial.leave240InvPart22=[] := by decide +kernel
theorem guardleave240InvPart23 : (Partial.leave240InvPart23).all (ok watched)=true ∧ log watched Partial.leave240InvPart23=[] := by decide +kernel
theorem guardleave240InvPart24 : (Partial.leave240InvPart24).all (ok watched)=true ∧ log watched Partial.leave240InvPart24=[] := by decide +kernel
theorem guardleave240InvPart25 : (Partial.leave240InvPart25).all (ok watched)=true ∧ log watched Partial.leave240InvPart25=[] := by decide +kernel
theorem guardleave240InvPart26 : (Partial.leave240InvPart26).all (ok watched)=true ∧ log watched Partial.leave240InvPart26=[] := by decide +kernel
theorem guardleave240InvPart27 : (Partial.leave240InvPart27).all (ok watched)=true ∧ log watched Partial.leave240InvPart27=[] := by decide +kernel
theorem guardleave240InvPart28 : (Partial.leave240InvPart28).all (ok watched)=true ∧ log watched Partial.leave240InvPart28=[] := by decide +kernel
theorem guardleave240InvPart29 : (Partial.leave240InvPart29).all (ok watched)=true ∧ log watched Partial.leave240InvPart29=[] := by decide +kernel
theorem guardleave240InvPart30 : (Partial.leave240InvPart30).all (ok watched)=true ∧ log watched Partial.leave240InvPart30=[] := by decide +kernel
theorem guardleave240InvPart31 : (Partial.leave240InvPart31).all (ok watched)=true ∧ log watched Partial.leave240InvPart31=[] := by decide +kernel
theorem guardleave240InvPart32 : (Partial.leave240InvPart32).all (ok watched)=true ∧ log watched Partial.leave240InvPart32=[] := by decide +kernel
theorem guardleave240InvPart33 : (Partial.leave240InvPart33).all (ok watched)=true ∧ log watched Partial.leave240InvPart33=[] := by decide +kernel
theorem guardleave240InvPart34 : (Partial.leave240InvPart34).all (ok watched)=true ∧ log watched Partial.leave240InvPart34=[270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256] := by decide +kernel
theorem guardleave240InvPart35 : (Partial.leave240InvPart35).all (ok watched)=true ∧ log watched Partial.leave240InvPart35=[] := by decide +kernel
theorem admissibleInv : (Partial.leave240Inv).all (ok watched)=true := by
  simp only [Partial.leave240Inv,List.all_append,guardleave240InvPart0.1,guardleave240InvPart1.1,guardleave240InvPart2.1,guardleave240InvPart3.1,guardleave240InvPart4.1,guardleave240InvPart5.1,guardleave240InvPart6.1,guardleave240InvPart7.1,guardleave240InvPart8.1,guardleave240InvPart9.1,guardleave240InvPart10.1,guardleave240InvPart11.1,guardleave240InvPart12.1,guardleave240InvPart13.1,guardleave240InvPart14.1,guardleave240InvPart15.1,guardleave240InvPart16.1,guardleave240InvPart17.1,guardleave240InvPart18.1,guardleave240InvPart19.1,guardleave240InvPart20.1,guardleave240InvPart21.1,guardleave240InvPart22.1,guardleave240InvPart23.1,guardleave240InvPart24.1,guardleave240InvPart25.1,guardleave240InvPart26.1,guardleave240InvPart27.1,guardleave240InvPart28.1,guardleave240InvPart29.1,guardleave240InvPart30.1,guardleave240InvPart31.1,guardleave240InvPart32.1,guardleave240InvPart33.1,guardleave240InvPart34.1,guardleave240InvPart35.1,Bool.and_self]
theorem ledgerInv : log watched Partial.leave240Inv=[1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256] := by
  simp only [Partial.leave240Inv,log_cat,guardleave240InvPart0.2,guardleave240InvPart1.2,guardleave240InvPart2.2,guardleave240InvPart3.2,guardleave240InvPart4.2,guardleave240InvPart5.2,guardleave240InvPart6.2,guardleave240InvPart7.2,guardleave240InvPart8.2,guardleave240InvPart9.2,guardleave240InvPart10.2,guardleave240InvPart11.2,guardleave240InvPart12.2,guardleave240InvPart13.2,guardleave240InvPart14.2,guardleave240InvPart15.2,guardleave240InvPart16.2,guardleave240InvPart17.2,guardleave240InvPart18.2,guardleave240InvPart19.2,guardleave240InvPart20.2,guardleave240InvPart21.2,guardleave240InvPart22.2,guardleave240InvPart23.2,guardleave240InvPart24.2,guardleave240InvPart25.2,guardleave240InvPart26.2,guardleave240InvPart27.2,guardleave240InvPart28.2,guardleave240InvPart29.2,guardleave240InvPart30.2,guardleave240InvPart31.2,guardleave240InvPart32.2,guardleave240InvPart33.2,guardleave240InvPart34.2,guardleave240InvPart35.2];rfl
theorem preservesInv (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave240Inv m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissibleInv,ledgerInv]
  have paired:∀w∈([1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256]:List Wire),flip w [1284, 1285, 1286, 1287, 1288, 1288, 1287, 1286, 1285, 1284, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256, 270, 269, 268, 267, 266, 265, 264, 263, 262, 261, 260, 259, 258, 257, 256]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
#print axioms preserves
end ECDSAAdd.Entrant.StairPacket.Leave240Records


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def watched (q:Wire) := decide (16≤q ∧ q<286 ∨ 1044≤q ∧ q<1301 ∨ 1800≤q ∧ q≤1812)
theorem guardleave255Part0 : (Partial.leave255Part0).all (ok watched)=true ∧ log watched Partial.leave255Part0=[271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285] := by decide +kernel
theorem guardleave255Part1 : (Partial.leave255Part1).all (ok watched)=true ∧ log watched Partial.leave255Part1=[] := by decide +kernel
theorem guardleave255Part2 : (Partial.leave255Part2).all (ok watched)=true ∧ log watched Partial.leave255Part2=[] := by decide +kernel
theorem guardleave255Part3 : (Partial.leave255Part3).all (ok watched)=true ∧ log watched Partial.leave255Part3=[] := by decide +kernel
theorem guardleave255Part4 : (Partial.leave255Part4).all (ok watched)=true ∧ log watched Partial.leave255Part4=[] := by decide +kernel
theorem guardleave255Part5 : (Partial.leave255Part5).all (ok watched)=true ∧ log watched Partial.leave255Part5=[] := by decide +kernel
theorem guardleave255Part6 : (Partial.leave255Part6).all (ok watched)=true ∧ log watched Partial.leave255Part6=[] := by decide +kernel
theorem guardleave255Part7 : (Partial.leave255Part7).all (ok watched)=true ∧ log watched Partial.leave255Part7=[] := by decide +kernel
theorem guardleave255Part8 : (Partial.leave255Part8).all (ok watched)=true ∧ log watched Partial.leave255Part8=[] := by decide +kernel
theorem guardleave255Part9 : (Partial.leave255Part9).all (ok watched)=true ∧ log watched Partial.leave255Part9=[] := by decide +kernel
theorem guardleave255Part10 : (Partial.leave255Part10).all (ok watched)=true ∧ log watched Partial.leave255Part10=[] := by decide +kernel
theorem guardleave255Part11 : (Partial.leave255Part11).all (ok watched)=true ∧ log watched Partial.leave255Part11=[] := by decide +kernel
theorem guardleave255Part12 : (Partial.leave255Part12).all (ok watched)=true ∧ log watched Partial.leave255Part12=[] := by decide +kernel
theorem guardleave255Part13 : (Partial.leave255Part13).all (ok watched)=true ∧ log watched Partial.leave255Part13=[] := by decide +kernel
theorem guardleave255Part14 : (Partial.leave255Part14).all (ok watched)=true ∧ log watched Partial.leave255Part14=[] := by decide +kernel
theorem guardleave255Part15 : (Partial.leave255Part15).all (ok watched)=true ∧ log watched Partial.leave255Part15=[] := by decide +kernel
theorem guardleave255Part16 : (Partial.leave255Part16).all (ok watched)=true ∧ log watched Partial.leave255Part16=[] := by decide +kernel
theorem guardleave255Part17 : (Partial.leave255Part17).all (ok watched)=true ∧ log watched Partial.leave255Part17=[] := by decide +kernel
theorem guardleave255Part18 : (Partial.leave255Part18).all (ok watched)=true ∧ log watched Partial.leave255Part18=[] := by decide +kernel
theorem guardleave255Part19 : (Partial.leave255Part19).all (ok watched)=true ∧ log watched Partial.leave255Part19=[] := by decide +kernel
theorem guardleave255Part20 : (Partial.leave255Part20).all (ok watched)=true ∧ log watched Partial.leave255Part20=[] := by decide +kernel
theorem guardleave255Part21 : (Partial.leave255Part21).all (ok watched)=true ∧ log watched Partial.leave255Part21=[] := by decide +kernel
theorem guardleave255Part22 : (Partial.leave255Part22).all (ok watched)=true ∧ log watched Partial.leave255Part22=[] := by decide +kernel
theorem guardleave255Part23 : (Partial.leave255Part23).all (ok watched)=true ∧ log watched Partial.leave255Part23=[] := by decide +kernel
theorem guardleave255Part24 : (Partial.leave255Part24).all (ok watched)=true ∧ log watched Partial.leave255Part24=[] := by decide +kernel
theorem guardleave255Part25 : (Partial.leave255Part25).all (ok watched)=true ∧ log watched Partial.leave255Part25=[] := by decide +kernel
theorem guardleave255Part26 : (Partial.leave255Part26).all (ok watched)=true ∧ log watched Partial.leave255Part26=[] := by decide +kernel
theorem guardleave255Part27 : (Partial.leave255Part27).all (ok watched)=true ∧ log watched Partial.leave255Part27=[] := by decide +kernel
theorem guardleave255Part28 : (Partial.leave255Part28).all (ok watched)=true ∧ log watched Partial.leave255Part28=[] := by decide +kernel
theorem guardleave255Part29 : (Partial.leave255Part29).all (ok watched)=true ∧ log watched Partial.leave255Part29=[] := by decide +kernel
theorem guardleave255Part30 : (Partial.leave255Part30).all (ok watched)=true ∧ log watched Partial.leave255Part30=[] := by decide +kernel
theorem guardleave255Part31 : (Partial.leave255Part31).all (ok watched)=true ∧ log watched Partial.leave255Part31=[] := by decide +kernel
theorem guardleave255Part32 : (Partial.leave255Part32).all (ok watched)=true ∧ log watched Partial.leave255Part32=[271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 1299, 1300, 1812] := by decide +kernel
theorem guardleave255Part33 : (Partial.leave255Part33).all (ok watched)=true ∧ log watched Partial.leave255Part33=[1811, 1810, 1810, 1811, 1812, 1300, 1299] := by decide +kernel
theorem guardleave255Part34 : (Partial.leave255Part34).all (ok watched)=true ∧ log watched Partial.leave255Part34=[] := by decide +kernel
theorem guardleave255Part35 : (Partial.leave255Part35).all (ok watched)=true ∧ log watched Partial.leave255Part35=[] := by decide +kernel
theorem guardleave255Part36 : (Partial.leave255Part36).all (ok watched)=true ∧ log watched Partial.leave255Part36=[] := by decide +kernel
theorem admissible : (Partial.leave255).all (ok watched)=true := by
  simp only [Partial.leave255,List.all_append,guardleave255Part0.1,guardleave255Part1.1,guardleave255Part2.1,guardleave255Part3.1,guardleave255Part4.1,guardleave255Part5.1,guardleave255Part6.1,guardleave255Part7.1,guardleave255Part8.1,guardleave255Part9.1,guardleave255Part10.1,guardleave255Part11.1,guardleave255Part12.1,guardleave255Part13.1,guardleave255Part14.1,guardleave255Part15.1,guardleave255Part16.1,guardleave255Part17.1,guardleave255Part18.1,guardleave255Part19.1,guardleave255Part20.1,guardleave255Part21.1,guardleave255Part22.1,guardleave255Part23.1,guardleave255Part24.1,guardleave255Part25.1,guardleave255Part26.1,guardleave255Part27.1,guardleave255Part28.1,guardleave255Part29.1,guardleave255Part30.1,guardleave255Part31.1,guardleave255Part32.1,guardleave255Part33.1,guardleave255Part34.1,guardleave255Part35.1,guardleave255Part36.1,Bool.and_self]
theorem ledger : log watched Partial.leave255=[271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299] := by
  simp only [Partial.leave255,log_cat,guardleave255Part0.2,guardleave255Part1.2,guardleave255Part2.2,guardleave255Part3.2,guardleave255Part4.2,guardleave255Part5.2,guardleave255Part6.2,guardleave255Part7.2,guardleave255Part8.2,guardleave255Part9.2,guardleave255Part10.2,guardleave255Part11.2,guardleave255Part12.2,guardleave255Part13.2,guardleave255Part14.2,guardleave255Part15.2,guardleave255Part16.2,guardleave255Part17.2,guardleave255Part18.2,guardleave255Part19.2,guardleave255Part20.2,guardleave255Part21.2,guardleave255Part22.2,guardleave255Part23.2,guardleave255Part24.2,guardleave255Part25.2,guardleave255Part26.2,guardleave255Part27.2,guardleave255Part28.2,guardleave255Part29.2,guardleave255Part30.2,guardleave255Part31.2,guardleave255Part32.2,guardleave255Part33.2,guardleave255Part34.2,guardleave255Part35.2,guardleave255Part36.2];rfl
theorem preserves (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave255 m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissible,ledger]
  have paired:∀w∈([271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299]:List Wire),flip w [271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
theorem guardleave255InvPart0 : (Partial.leave255InvPart0).all (ok watched)=true ∧ log watched Partial.leave255InvPart0=[] := by decide +kernel
theorem guardleave255InvPart1 : (Partial.leave255InvPart1).all (ok watched)=true ∧ log watched Partial.leave255InvPart1=[] := by decide +kernel
theorem guardleave255InvPart2 : (Partial.leave255InvPart2).all (ok watched)=true ∧ log watched Partial.leave255InvPart2=[] := by decide +kernel
theorem guardleave255InvPart3 : (Partial.leave255InvPart3).all (ok watched)=true ∧ log watched Partial.leave255InvPart3=[1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299] := by decide +kernel
theorem guardleave255InvPart4 : (Partial.leave255InvPart4).all (ok watched)=true ∧ log watched Partial.leave255InvPart4=[285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271] := by decide +kernel
theorem guardleave255InvPart5 : (Partial.leave255InvPart5).all (ok watched)=true ∧ log watched Partial.leave255InvPart5=[] := by decide +kernel
theorem guardleave255InvPart6 : (Partial.leave255InvPart6).all (ok watched)=true ∧ log watched Partial.leave255InvPart6=[] := by decide +kernel
theorem guardleave255InvPart7 : (Partial.leave255InvPart7).all (ok watched)=true ∧ log watched Partial.leave255InvPart7=[] := by decide +kernel
theorem guardleave255InvPart8 : (Partial.leave255InvPart8).all (ok watched)=true ∧ log watched Partial.leave255InvPart8=[] := by decide +kernel
theorem guardleave255InvPart9 : (Partial.leave255InvPart9).all (ok watched)=true ∧ log watched Partial.leave255InvPart9=[] := by decide +kernel
theorem guardleave255InvPart10 : (Partial.leave255InvPart10).all (ok watched)=true ∧ log watched Partial.leave255InvPart10=[] := by decide +kernel
theorem guardleave255InvPart11 : (Partial.leave255InvPart11).all (ok watched)=true ∧ log watched Partial.leave255InvPart11=[] := by decide +kernel
theorem guardleave255InvPart12 : (Partial.leave255InvPart12).all (ok watched)=true ∧ log watched Partial.leave255InvPart12=[] := by decide +kernel
theorem guardleave255InvPart13 : (Partial.leave255InvPart13).all (ok watched)=true ∧ log watched Partial.leave255InvPart13=[] := by decide +kernel
theorem guardleave255InvPart14 : (Partial.leave255InvPart14).all (ok watched)=true ∧ log watched Partial.leave255InvPart14=[] := by decide +kernel
theorem guardleave255InvPart15 : (Partial.leave255InvPart15).all (ok watched)=true ∧ log watched Partial.leave255InvPart15=[] := by decide +kernel
theorem guardleave255InvPart16 : (Partial.leave255InvPart16).all (ok watched)=true ∧ log watched Partial.leave255InvPart16=[] := by decide +kernel
theorem guardleave255InvPart17 : (Partial.leave255InvPart17).all (ok watched)=true ∧ log watched Partial.leave255InvPart17=[] := by decide +kernel
theorem guardleave255InvPart18 : (Partial.leave255InvPart18).all (ok watched)=true ∧ log watched Partial.leave255InvPart18=[] := by decide +kernel
theorem guardleave255InvPart19 : (Partial.leave255InvPart19).all (ok watched)=true ∧ log watched Partial.leave255InvPart19=[] := by decide +kernel
theorem guardleave255InvPart20 : (Partial.leave255InvPart20).all (ok watched)=true ∧ log watched Partial.leave255InvPart20=[] := by decide +kernel
theorem guardleave255InvPart21 : (Partial.leave255InvPart21).all (ok watched)=true ∧ log watched Partial.leave255InvPart21=[] := by decide +kernel
theorem guardleave255InvPart22 : (Partial.leave255InvPart22).all (ok watched)=true ∧ log watched Partial.leave255InvPart22=[] := by decide +kernel
theorem guardleave255InvPart23 : (Partial.leave255InvPart23).all (ok watched)=true ∧ log watched Partial.leave255InvPart23=[] := by decide +kernel
theorem guardleave255InvPart24 : (Partial.leave255InvPart24).all (ok watched)=true ∧ log watched Partial.leave255InvPart24=[] := by decide +kernel
theorem guardleave255InvPart25 : (Partial.leave255InvPart25).all (ok watched)=true ∧ log watched Partial.leave255InvPart25=[] := by decide +kernel
theorem guardleave255InvPart26 : (Partial.leave255InvPart26).all (ok watched)=true ∧ log watched Partial.leave255InvPart26=[] := by decide +kernel
theorem guardleave255InvPart27 : (Partial.leave255InvPart27).all (ok watched)=true ∧ log watched Partial.leave255InvPart27=[] := by decide +kernel
theorem guardleave255InvPart28 : (Partial.leave255InvPart28).all (ok watched)=true ∧ log watched Partial.leave255InvPart28=[] := by decide +kernel
theorem guardleave255InvPart29 : (Partial.leave255InvPart29).all (ok watched)=true ∧ log watched Partial.leave255InvPart29=[] := by decide +kernel
theorem guardleave255InvPart30 : (Partial.leave255InvPart30).all (ok watched)=true ∧ log watched Partial.leave255InvPart30=[] := by decide +kernel
theorem guardleave255InvPart31 : (Partial.leave255InvPart31).all (ok watched)=true ∧ log watched Partial.leave255InvPart31=[] := by decide +kernel
theorem guardleave255InvPart32 : (Partial.leave255InvPart32).all (ok watched)=true ∧ log watched Partial.leave255InvPart32=[] := by decide +kernel
theorem guardleave255InvPart33 : (Partial.leave255InvPart33).all (ok watched)=true ∧ log watched Partial.leave255InvPart33=[] := by decide +kernel
theorem guardleave255InvPart34 : (Partial.leave255InvPart34).all (ok watched)=true ∧ log watched Partial.leave255InvPart34=[] := by decide +kernel
theorem guardleave255InvPart35 : (Partial.leave255InvPart35).all (ok watched)=true ∧ log watched Partial.leave255InvPart35=[285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271] := by decide +kernel
theorem guardleave255InvPart36 : (Partial.leave255InvPart36).all (ok watched)=true ∧ log watched Partial.leave255InvPart36=[] := by decide +kernel
theorem admissibleInv : (Partial.leave255Inv).all (ok watched)=true := by
  simp only [Partial.leave255Inv,List.all_append,guardleave255InvPart0.1,guardleave255InvPart1.1,guardleave255InvPart2.1,guardleave255InvPart3.1,guardleave255InvPart4.1,guardleave255InvPart5.1,guardleave255InvPart6.1,guardleave255InvPart7.1,guardleave255InvPart8.1,guardleave255InvPart9.1,guardleave255InvPart10.1,guardleave255InvPart11.1,guardleave255InvPart12.1,guardleave255InvPart13.1,guardleave255InvPart14.1,guardleave255InvPart15.1,guardleave255InvPart16.1,guardleave255InvPart17.1,guardleave255InvPart18.1,guardleave255InvPart19.1,guardleave255InvPart20.1,guardleave255InvPart21.1,guardleave255InvPart22.1,guardleave255InvPart23.1,guardleave255InvPart24.1,guardleave255InvPart25.1,guardleave255InvPart26.1,guardleave255InvPart27.1,guardleave255InvPart28.1,guardleave255InvPart29.1,guardleave255InvPart30.1,guardleave255InvPart31.1,guardleave255InvPart32.1,guardleave255InvPart33.1,guardleave255InvPart34.1,guardleave255InvPart35.1,guardleave255InvPart36.1,Bool.and_self]
theorem ledgerInv : log watched Partial.leave255Inv=[1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271] := by
  simp only [Partial.leave255Inv,log_cat,guardleave255InvPart0.2,guardleave255InvPart1.2,guardleave255InvPart2.2,guardleave255InvPart3.2,guardleave255InvPart4.2,guardleave255InvPart5.2,guardleave255InvPart6.2,guardleave255InvPart7.2,guardleave255InvPart8.2,guardleave255InvPart9.2,guardleave255InvPart10.2,guardleave255InvPart11.2,guardleave255InvPart12.2,guardleave255InvPart13.2,guardleave255InvPart14.2,guardleave255InvPart15.2,guardleave255InvPart16.2,guardleave255InvPart17.2,guardleave255InvPart18.2,guardleave255InvPart19.2,guardleave255InvPart20.2,guardleave255InvPart21.2,guardleave255InvPart22.2,guardleave255InvPart23.2,guardleave255InvPart24.2,guardleave255InvPart25.2,guardleave255InvPart26.2,guardleave255InvPart27.2,guardleave255InvPart28.2,guardleave255InvPart29.2,guardleave255InvPart30.2,guardleave255InvPart31.2,guardleave255InvPart32.2,guardleave255InvPart33.2,guardleave255InvPart34.2,guardleave255InvPart35.2,guardleave255InvPart36.2];rfl
theorem preservesInv (s:State) (m:List Bool) (q:Wire) (hq:watched q=true) :
    (run Partial.leave255Inv m s).basis q=s.basis q := by
  rw [sound watched _ _ hq admissibleInv,ledgerInv]
  have paired:∀w∈([1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271]:List Wire),flip w [1299, 1300, 1812, 1811, 1810, 1810, 1811, 1812, 1300, 1299, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271, 285, 284, 283, 282, 281, 280, 279, 278, 277, 276, 275, 274, 273, 272, 271]=false:=by decide +kernel
  have all:=cancel_all _ paired q
  rw [all,Bool.xor_false]
#print axioms preserves
end ECDSAAdd.Entrant.StairPacket.Leave255Records


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSignedCoordinates
open Arithmetic PortalValues

theorem pair (L:SkywalkIntegerLayout) (g sg:Bool) (u v i:Nat) (s:BasisState)
    (a:signedRegValue L.a s=(SkywalkRails.encode g sg u v).a)
    (b:signedRegValue L.b s=(SkywalkRails.encode g sg u v).b)
    (prev:s L.previous=g) (la:i<L.a.length) (lb:i<L.b.length) :
    let e:=negative sg u
    let p:=(u+v).testBit i
    let n:=(u-e.toNat).testBit i ^^ e
    s (L.a.getD i 0)=(if g then n else p) ∧ s (L.b.getD i 0)=(if g then p else n) := by
  obtain ⟨_,_,pos,mag⟩:=signedWords L g sg u v s a b prev
  let e:=negative sg u
  have signedBit (x:List Wire) (hx:i<x.length) (hm:regValue x (fun q=>s q ^^ e)=u-e.toNat) :
      s (x.getD i 0)=((u-e.toNat).testBit i ^^ e) := by
    have read:=HighBankAdjust.bit_read x i (fun q=>s q ^^ e) hx
    rw [hm] at read
    change (s (x.getD i 0) ^^ e)=_ at read
    rw [←read];cases e <;> simp
  cases g
  · exact ⟨(HighBankAdjust.bit_read _ _ _ la).trans (congrArg (Nat.testBit · i) pos),signedBit _ lb mag⟩
  · exact ⟨signedBit _ la mag,(HighBankAdjust.bit_read _ _ _ lb).trans (congrArg (Nat.testBit · i) pos)⟩

theorem sharedDigit (x y b i:Nat) (modEq:x%2^(b+1)=y%2^(b+1)) (hi:i≤b) :
    x.testBit i=y.testBit i := by
  have h:=congrArg (Nat.testBit · i) modEq
  simpa only [Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr (Nat.lt_succ_of_le hi),Bool.true_and] using h

end ECDSAAdd.Entrant.StairPacket.LeaveSignedCoordinates


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
def MayTouch (j:Fin 23) (w:Wire) : Prop :=
  (start j+15≤w ∧ w≤start j+14+16+(shape j).mid+2) ∨ (786≤w ∧ w≤787+(shape j).mid) ∨
  (1556≤w ∧ w≤1556+(shape j).mid) ∨ (1044+start j≤w ∧ w<1044+start j+15)
instance (j:Fin 23) (w:Wire) : Decidable (MayTouch j w):=by unfold MayTouch;infer_instance
theorem named_range (j:Fin 23) (a n q:Nat) (lim:a+n≤15) (outside:¬MayTouch j (windowNet j q)) :
    q∉spanSites j a n:=by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by apply OB5.sig_invol;have hj:=j.isLt;simp [start];omega
  rw [undo] at outside
  apply outside
  simp only [ports,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false,shape,smallBits,start] at hw
  simp only [MayTouch,shape,smallBits,start]
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega
theorem through_body (j:Fin 23) (P:Program) (s:State) (m:List Bool) (q:Nat)
    (free:¬MayTouch j (windowNet j q))
    (admin:let a:=run (routed j 0 1) m s
      (run P (m.drop (measurementCount (routed j 0 1))) a).basis q=a.basis q) :
    (run (body j P) m s).basis q=s.basis q:=by
  simp only [body,run_append,run_take]
  exact (route_outside j 1 14 (by decide) q (named_range j 1 14 q (by decide) free) _ _).trans
    (admin.trans (route_outside j 0 1 (by decide) q (named_range j 0 1 q (by decide) free) s m))
theorem body_cover (j:Fin 23) (P:Program) (controls effects:List Wire)
    (clean:∀q∈controls,¬MayTouch j (windowNet j q)) (apart:∀q∈controls,q∉effects)
    (cover:wires P⊆effects.toFinset) (s:State) (m:List Bool) (q:Wire) (hit:q∈controls) :
    (run (body j P) m s).basis q=s.basis q:=
  through_body j P s m q (clean q hit) (run_preserves_outside P _ _ q
    (fun used=>apart q hit (List.mem_toFinset.mp (cover used))))
theorem keep_values (a b c:Wire) (saved:List Wire) (s t:State) (H:Nat) (f u:Bool)
    (agree:∀q∈[a,b,c]++saved,t.basis q=s.basis q) (h:regValue saved s.basis=H)
    (sa:s.basis a=false) (sb:s.basis b=f) (sc:s.basis c=u) :
    regValue saved t.basis=H ∧ t.basis a=false ∧ t.basis b=f ∧ t.basis c=u:=
  ⟨(regValue_congr _ _ _ (fun q m=>agree _ (List.mem_append_right _ m))).trans h,
    (agree a (by simp)).trans sa,(agree b (by simp)).trans sb,(agree c (by simp)).trans sc⟩
#print axioms through_body
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
def saved := [1718,1719,1720]++upperPairs.map Prod.snd
theorem high_from_cut (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^144)
    (packed:PackedCut lowerPairs upperPairs 240 1723 1721 1722 (negative S z.u) (decide (Shadow.far 144 15 z))
      (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) (pullState (OB5.sig 224) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue saved (run Partial.enter225 m cut).basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0 :=by
  have high:=SavedHigh.stored 163 raw cut z G S packed input layout.g0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨_,bits,outer⟩:=from_full raw cut z G S m small packed input
  have live:∀q∈upperPairs.map Prod.snd,q∉ports225:=by decide +kernel
  have bulk:=regValue_congr (upperPairs.map Prod.snd) (run Partial.enter225 m cut).basis cut.basis
    (fun q hit=>outer q (fun used=>live q hit (List.mem_toFinset.mp (programCover used))))
  apply SavedHigh.assemble 144 15 z G S _ 1718 1719 1720 _
  · exact bits 12 (by rw [forward_all];decide)
  · exact bits 13 (by rw [forward_all];decide)
  · exact bits 14 (by rw [forward_all];decide)
  · exact bulk.trans high
#print axioms high_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter225


end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
def saved := [1710,1711,1712]++upperPairs.map Prod.snd
theorem high_from_cut (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^136)
    (packed:PackedCut lowerPairs upperPairs 255 1715 1713 1714 (negative S z.u) (decide (Shadow.far 136 15 z))
      (decide (Shadow.far 136 15 z ∧ 2^136≤z.u)) (pullState (OB5.sig 239) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue saved (run Partial.enter240 m cut).basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0 :=by
  have high:=SavedHigh.stored 155 raw cut z G S packed input layout.g0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨_,bits,outer⟩:=from_full raw cut z G S m small packed input
  have live:∀q∈upperPairs.map Prod.snd,q∉ports240:=by decide +kernel
  have bulk:=regValue_congr (upperPairs.map Prod.snd) (run Partial.enter240 m cut).basis cut.basis
    (fun q hit=>outer q (fun used=>live q hit (List.mem_toFinset.mp (programCover used))))
  apply SavedHigh.assemble 136 15 z G S _ 1710 1711 1712 _
  · exact bits 12 (by rw [forward_all];decide)
  · exact bits 13 (by rw [forward_all];decide)
  · exact bits 14 (by rw [forward_all];decide)
  · exact bulk.trans high
#print axioms high_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter240


end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
def saved := [1703,1704,1705]++upperPairs.map Prod.snd
theorem high_from_cut (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^129)
    (packed:PackedCut lowerPairs upperPairs 270 1708 1706 1707 (negative S z.u) (decide (Shadow.far 129 15 z))
      (decide (Shadow.far 129 15 z ∧ 2^129≤z.u)) (pullState (OB5.sig 254) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue saved (run Partial.enter255 m cut).basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0 :=by
  have high:=SavedHigh.stored 148 raw cut z G S packed input layout.g0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨_,bits,outer⟩:=from_full raw cut z G S m small packed input
  have live:∀q∈upperPairs.map Prod.snd,q∉ports255:=by decide +kernel
  have bulk:=regValue_congr (upperPairs.map Prod.snd) (run Partial.enter255 m cut).basis cut.basis
    (fun q hit=>outer q (fun used=>live q hit (List.mem_toFinset.mp (programCover used))))
  apply SavedHigh.assemble 129 15 z G S _ 1703 1704 1705 _
  · exact bits 12 (by rw [forward_all];decide)
  · exact bits 13 (by rw [forward_all];decide)
  · exact bits 14 (by rw [forward_all];decide)
  · exact bulk.trans high
#print axioms high_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter255


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
theorem coherent_step {i:Nat} (hi:i<512) {a b:State} (same:Coherent i a b) (m:List Bool) :
    Coherent (i+1) (run (W.compactSkywalkTick base i) m a) (run (W.compactSkywalkTick base i) m b) := by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have on:∀q∈wires P,a.basis q=b.basis q:=fun q mem=>same.2 q (fun old=>away hi old (List.mem_toFinset.mp (sub mem)))
  have ste:=run_measured_locality P (wires P) (Finset.Subset.refl _) a b m same.1 on
  refine ⟨ste.1,?_⟩
  intro q outside
  by_cases inside:q∈wires P
  · exact ste.2 q inside
  · exact (run_preserves_outside _ m a _ inside).trans ((same.2 _ (fun e=>outside (earlier_mono (by omega) e))).trans
      (run_preserves_outside _ m b _ inside).symm)
theorem coherent_span (i n:Nat) (bound:i+n≤512) (a b:State) (same:Coherent i a b) (m:List Bool) :
    Coherent (i+n) (run (span i n) m a) (run (span i n) m b):=by
  induction n generalizing i a b m with
  | zero=>simpa [span,run] using same
  | succ n ih=>
    simp only [span,run_append,run_take]
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) (by omega) _ _ (coherent_step (by omega) same m) (m.drop _)

theorem past_slot (i q:Nat) (lo:15≤ i) (member:q∈sites i) : Earlier (i+15) q:=by
  obtain ⟨r,hr,he⟩:=List.mem_flatMap.mp member
  have lim:=List.mem_range'_1.mp hr
  have hr:r < i:=by
    by_cases h:i=225
    · subst i;simp [oldStart,oldCount] at lim;omega
    · simp [oldStart,oldCount,h] at lim;omega
  exact ⟨r,by omega,by simpa using he⟩
def Fixed (i:Nat) := ∀q∈sites i,OB5.sig (i+14) q=q
theorem fixed225:Fixed 225:=by unfold Fixed;decide +kernel
theorem fixed240:Fixed 240:=by unfold Fixed;decide +kernel
theorem fixed255:Fixed 255:=by unfold Fixed;decide +kernel

theorem after_coherent (i:Nat) (lo:15≤ i) (hi:i+15≤512) (fixed:Fixed i) (raw history ref:State)
    (same:Coherent i raw ref) :
    Coherent (i+15) (endRaw i raw history) (run (span i 15) [] ref) := by
  have c:=coherent_span i 15 hi raw ref same []
  refine ⟨c.1,?_⟩
  intro q off
  have invol:=OB5.sig_invol (i+14) (by omega) q
  have out:OB5.sig (i+14) q∉sites i:=by
    intro hit
    have h:=fixed _ hit
    rw [invol] at h
    exact off (h ▸ past_slot i _ lo hit)
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  rw [outside i raw history _ out,invol,c.2 q off]

def Domain (i x p:Nat) (s:State) := ∃ref:State,Coherent i s ref ∧
  W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i ref.basis

theorem full_span (i n x p:Nat) (hi:i+n≤512) (hp0:0<p) (hx0:0<x) (odd:p%2=1) (hp:p<2^256)
    (gap:p+2^32≤2^256) (hx:x<p) (cop:x.Coprime p) (s:State) (m:List Bool)
    (invariant:W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) (i+n) (run (span i n) m s).basis := by
  induction n generalizing i s m with
  | zero=>simpa [span,run] using invariant
  | succ n ih=>
    simp only [span,run_append,run_take]
    have tick:=(W.compactSkywalkStageStep base base_pool_nodup x p i hp0 hx0 odd hp gap hx cop (by omega) s m invariant).2
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) (by omega) _ (m.drop _) tick

theorem advance (i x p:Nat) (lo:15≤ i) (hi:i+15≤512) (fixed:Fixed i) (hp0:0<p) (hx0:0<x) (odd:p%2=1) (hp:p<2^256)
    (gap:p+2^32≤2^256) (hx:x<p) (cop:x.Coprime p) (raw history:State) (dom:Domain i x p raw) :
    Domain (i+15) x p (endRaw i raw history) := by
  obtain ⟨ref,same,valid⟩:=dom
  exact ⟨_,after_coherent i lo hi fixed raw history ref same,
    full_span i 15 x p hi hp0 hx0 odd hp gap hx cop ref [] valid⟩
#print axioms advance
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
set_option maxRecDepth 30000
attribute [local irreducible] run
theorem cells_congr (j:Fin 23) (s t:State) (C:∀r:Fin 15,
    cell (shape j) r (mappedBasis j s.basis)=cell (shape j) r (mappedBasis j t.basis)) (i n:Nat) (bound:i+n≤15) :
    readCells (shape j) i n (mappedBasis j s.basis)=readCells (shape j) i n (mappedBasis j t.basis) := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>
    simp only [readCells,C ⟨i,by omega⟩,ih (i+1) (by omega)]

namespace Leave225Records
open ArchiveBoundary240
theorem chosen : ∀r:Fin 15,watched (windowNet sourceIdx (ports (shape sourceIdx) r).a0)=true ∧
    watched (windowNet sourceIdx (ports (shape sourceIdx) r).history)=true := by decide +kernel
theorem history (s:State) (m:List Bool) :
    let t:=run Partial.leave225 m s
    readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx t.basis)=
      readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis) := by
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (preserves _ _ _ (chosen r).1) (preserves _ _ _ (chosen r).2)
end Leave225Records
namespace Leave240Records
open ArchiveBoundary255
theorem chosen : ∀r:Fin 15,watched (windowNet sourceIdx (ports (shape sourceIdx) r).a0)=true ∧
    watched (windowNet sourceIdx (ports (shape sourceIdx) r).history)=true := by decide +kernel
theorem history (s:State) (m:List Bool) :
    let t:=run Partial.leave240 m s
    readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx t.basis)=
      readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis) := by
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (preserves _ _ _ (chosen r).1) (preserves _ _ _ (chosen r).2)
end Leave240Records
namespace Leave255Records
open ArchiveBoundary270
theorem chosen : ∀r:Fin 15,watched (windowNet sourceIdx (ports (shape sourceIdx) r).a0)=true ∧
    watched (windowNet sourceIdx (ports (shape sourceIdx) r).history)=true := by decide +kernel
theorem history (s:State) (m:List Bool) :
    let t:=run Partial.leave255 m s
    readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx t.basis)=
      readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis) := by
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (preserves _ _ _ (chosen r).1) (preserves _ _ _ (chosen r).2)
end Leave255Records
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
theorem carry_member (i:Nat) (q:Wire) (mem:q∈(W.compactSkywalkTickLayout base i).carry) :
    q∈(W.compactSkywalkTickLayout base i).wires.toFinset := List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires,mem])
theorem previous_member (i:Nat) : (W.compactSkywalkTickLayout base i).previous∈(W.compactSkywalkTickLayout base i).wires.toFinset :=
  List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires])
theorem scratch_lanes : ∀k:Fin 134,1556+k.val∈L.carry ∧ 1556+k.val∈wireBlock base 1540 257 := by decide +kernel
theorem after_cells (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 270 original.basis) :
    (run canonical [] raw).basis 285=raw.basis 285 ∧
    ∀k:Fin 134,(run canonical [] raw).basis (1556+k.val)=false := by
  obtain ⟨ref,old,next,pre,post⟩:=after_reference d x hx0 hx raw original read stage
  have prev:285∈L.wires.toFinset:=previous_member 270
  have a:=pastG 270 269 (by decide) (by decide) _ _ old
  have b:=pastG 271 269 (by decide) (by decide) _ _ next
  exact ⟨(post _ prev).trans (b.trans (a.symm.trans (pre _ prev).symm)),
    fun k=>(post _ (carry_member 270 _ (scratch_lanes k).1)).trans (full_carry 271 (by decide) _ _ next _ (scratch_lanes k).2)⟩
#print axioms after_cells
end ECDSAAdd.Entrant.StairPacket.EndTick


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

abbrev L:=W.compactSkywalkTickLayout base 240
abbrev shortL:=IntegerPacket.ports (shape 10) 15

theorem shortMapping (i:Fin 144):
    windowNet 10 (shortL.a.getD i.val 0)=256+i.val ∧
    windowNet 10 (shortL.b.getD i.val 0)=786+i.val := by
  revert i; decide +kernel

theorem wideMapping (i:Fin 257):
    L.a.getD i.val 0=OB5.sig 239 (256+i.val) ∧
    L.b.getD i.val 0=OB5.sig 239 (786+i.val) := by
  revert i; decide +kernel

theorem wide (a:SkywalkNat.State) (G sg:Bool) (raw:State)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis)
    (i:Fin 257) :
    let o:=pullState (OB5.sig 239) raw
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    o.basis (256+i.val)=(if G then neg else pos) ∧ o.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:257≤L.a.length:=by decide +kernel
  have maxB:257≤L.b.length:=by decide +kernel
  have h:=pair L G sg a.u a.v i.val raw.basis input.1 input.2.1 input.2.2.1
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  rw [(wideMapping i).1,(wideMapping i).2] at h
  exact h

theorem short (a:SkywalkNat.State) (G sg:Bool) (s:State)
    (ready:onRails 10 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i:Fin 144) :
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    s.basis (256+i.val)=(if G then neg else pos) ∧ s.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:144≤shortL.a.length:=by decide +kernel
  have maxB:144≤shortL.b.length:=by decide +kernel
  have prev:mappedBasis 10 s.basis shortL.previous=G:=by cases G <;> exact ready.2.2.1
  have h:=pair shortL G sg a.u a.v i.val (mappedBasis 10 s.basis) ready.1 ready.2.1 prev
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  unfold mappedBasis at h
  dsimp only at h
  rw [(shortMapping i).1,(shortMapping i).2] at h
  exact h
end ECDSAAdd.Entrant.StairPacket.Leave225WideWords


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

abbrev L:=W.compactSkywalkTickLayout base 255
abbrev shortL:=IntegerPacket.ports (shape 11) 15

theorem shortMapping (i:Fin 136):
    windowNet 11 (shortL.a.getD i.val 0)=271+i.val ∧
    windowNet 11 (shortL.b.getD i.val 0)=786+i.val := by
  revert i; decide +kernel

theorem wideMapping (i:Fin 257):
    L.a.getD i.val 0=OB5.sig 254 (271+i.val) ∧
    L.b.getD i.val 0=OB5.sig 254 (786+i.val) := by
  revert i; decide +kernel

theorem wide (a:SkywalkNat.State) (G sg:Bool) (raw:State)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis)
    (i:Fin 257) :
    let o:=pullState (OB5.sig 254) raw
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    o.basis (271+i.val)=(if G then neg else pos) ∧ o.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:257≤L.a.length:=by decide +kernel
  have maxB:257≤L.b.length:=by decide +kernel
  have h:=pair L G sg a.u a.v i.val raw.basis input.1 input.2.1 input.2.2.1
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  rw [(wideMapping i).1,(wideMapping i).2] at h
  exact h

theorem short (a:SkywalkNat.State) (G sg:Bool) (s:State)
    (ready:onRails 11 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i:Fin 136) :
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    s.basis (271+i.val)=(if G then neg else pos) ∧ s.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:136≤shortL.a.length:=by decide +kernel
  have maxB:136≤shortL.b.length:=by decide +kernel
  have prev:mappedBasis 11 s.basis shortL.previous=G:=by cases G <;> exact ready.2.2.1
  have h:=pair shortL G sg a.u a.v i.val (mappedBasis 11 s.basis) ready.1 ready.2.1 prev
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  unfold mappedBasis at h
  dsimp only at h
  rw [(shortMapping i).1,(shortMapping i).2] at h
  exact h
end ECDSAAdd.Entrant.StairPacket.Leave240WideWords


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

abbrev L:=W.compactSkywalkTickLayout base 270
abbrev shortL:=IntegerPacket.ports (shape 12) 15

theorem shortMapping (i:Fin 129):
    windowNet 12 (shortL.a.getD i.val 0)=286+i.val ∧
    windowNet 12 (shortL.b.getD i.val 0)=786+i.val := by
  revert i; decide +kernel

theorem wideMapping (i:Fin 243):
    L.a.getD i.val 0=OB5.sig 269 (286+i.val) ∧
    L.b.getD i.val 0=OB5.sig 269 (786+i.val) := by
  revert i; decide +kernel

theorem wide (a:SkywalkNat.State) (G sg:Bool) (raw:State)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis)
    (i:Fin 243) :
    let o:=pullState (OB5.sig 269) raw
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    o.basis (286+i.val)=(if G then neg else pos) ∧ o.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:243≤L.a.length:=by decide +kernel
  have maxB:243≤L.b.length:=by decide +kernel
  have h:=pair L G sg a.u a.v i.val raw.basis input.1 input.2.1 input.2.2.1
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  rw [(wideMapping i).1,(wideMapping i).2] at h
  exact h

theorem short (a:SkywalkNat.State) (G sg:Bool) (s:State)
    (ready:onRails 12 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i:Fin 129) :
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    s.basis (286+i.val)=(if G then neg else pos) ∧ s.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:129≤shortL.a.length:=by decide +kernel
  have maxB:129≤shortL.b.length:=by decide +kernel
  have prev:mappedBasis 12 s.basis shortL.previous=G:=by cases G <;> exact ready.2.2.1
  have h:=pair shortL G sg a.u a.v i.val (mappedBasis 12 s.basis) ready.1 ready.2.1 prev
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  unfold mappedBasis at h
  dsimp only at h
  rw [(shortMapping i).1,(shortMapping i).2] at h
  exact h
end ECDSAAdd.Entrant.StairPacket.Leave255WideWords


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveTerminalBound
open SkywalkNat HighBankSum

/-- The stock stage at 270 has a narrower signed rail than the intermediate
    barrel. The fourteen sites above its physical destination contain zero. -/
theorem fit (x p : Nat) (xp:0<x) (pp:0<p) (odd:p%2=1) (bound:p<2^256)
    (small:x<p) (cop:x.Coprime p) :
    let z:=step^[255] (init x p)
    Leave255TrueMiddle.F z<2^113 := by
  have bounds:=iter_width p x 256 270 pp xp odd bound small cop (by decide)
  dsimp only at bounds
  change (step^[270] (init x p)).u<2^242 ∧ (step^[270] (init x p)).v<2^242 at bounds
  change total (step^[15] (step^[255] (init x p)))/2^130<2^113
  rw [←Function.iterate_add_apply]
  unfold total
  change ((step^[270] (init x p)).u+(step^[270] (init x p)).v)/2^130<2^113
  apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
  omega

theorem released (Z : Nat) (bound:Z<2^113) (s : ECDSAAdd.State)
    (stored:∀i<127,s.basis (Leave255OutputPorts.live i)=Z.testBit i) :
    ∀j:Fin 14,s.basis (1599+j.val)=false := by
  have sites : ∀i:Fin 14,Leave255OutputPorts.live (113+i.val)=1599+i.val := by decide +kernel
  intro j
  rw [←sites j,stored _ (by have h:=j.isLt;omega)]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))

end ECDSAAdd.Entrant.StairPacket.LeaveTerminalBound


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run routed unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
def protectedSites:List Wire:=[1723,1721,1722]++Enter225.saved

theorem free_native : ∀q∈protectedSites,¬MayTouch idx (windowNet idx q):=by decide +kernel
theorem free_admin : ∀q∈protectedSites,q∉support:=by decide +kernel
theorem keeps_stored (d:Bool) (s:State) (m:List Bool) (q:Wire) (hq:q∈protectedSites) :
    (run (body idx (program d)) m s).basis q=s.basis q:=
  body_cover idx (program d) protectedSites support free_native free_admin (packs d) s m q hq
theorem source_tags (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof.forward,s (map225 q)=(shadowRow 144 15 z G S).testBit q) :
    s 1723=false ∧ s 1721=decide (Shadow.far 144 15 z) ∧ s 1722=decide (Shadow.far 144 15 z ∧ 2^144≤z.u):=
  (actual_tags ports225 s 144 15 z G S hit).2
theorem relay (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue Enter225.saved s.basis=h) (hn:s.basis 1723=false) (hf:s.basis 1721=x) (hu:s.basis 1722=y) :
    let out:=run (body idx (program d)) m s
    regValue Enter225.saved out.basis=h ∧ out.basis 1723=false ∧ out.basis 1721=x ∧ out.basis 1722=y :=
  keep_values 1723 1721 1722 Enter225.saved s (run (body idx (program d)) m s) h x y (keeps_stored d s m) high hn hf hu
theorem saved_at_leave (d:Bool) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool)
    (small:min z.u z.v<2^144) (packed:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722
      (negative S z.u) (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u))
      (pullState (OB5.sig 224) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (body idx (program d)) ticks (run Partial.enter225 head cut)
    regValue Enter225.saved out.basis=(if Shadow.far 144 15 z then Shadow.high 144 15 z else 0) ∧
      out.basis 1723=false ∧ out.basis 1721=decide (Shadow.far 144 15 z) ∧
      out.basis 1722=decide (Shadow.far 144 15 z ∧ 2^144≤z.u):=by
  let pre:=run Partial.enter225 head cut
  have high:=Enter225.high_from_cut raw cut z G S head small packed input
  have body:=Enter225.from_full raw cut z G S head small packed input
  have tags:=source_tags pre.basis z G S body.2.1
  exact relay d pre ticks (if Shadow.far 144 15 z then Shadow.high 144 15 z else 0) _ _ high tags.1 tags.2.1 tags.2.2
#print axioms saved_at_leave
end ECDSAAdd.Entrant.StairPacket.NativePack225


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run routed unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
def protectedSites:List Wire:=[1715,1713,1714]++Enter240.saved

theorem admin_cover (d:Bool) : wires (withArchive d)⊆(support++ArchiveBoundary240.rawPortsList).toFinset:=by
  rw [withArchive,wires_append,List.toFinset_append]
  exact Finset.union_subset_union (packs d) (ArchiveBoundary240.load_cover d)

theorem free_native : ∀q∈protectedSites,¬MayTouch idx (windowNet idx q):=by decide +kernel
theorem free_admin : ∀q∈protectedSites,q∉(support++ArchiveBoundary240.rawPortsList):=by decide +kernel
theorem keeps_stored (d:Bool) (s:State) (m:List Bool) (q:Wire) (hq:q∈protectedSites) :
    (run (body idx (withArchive d)) m s).basis q=s.basis q:=
  body_cover idx (withArchive d) protectedSites (support++ArchiveBoundary240.rawPortsList) free_native free_admin (admin_cover d) s m q hq
theorem source_tags (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof.forward,s (map240 q)=(shadowRow 136 15 z G S).testBit q) :
    s 1715=false ∧ s 1713=decide (Shadow.far 136 15 z) ∧ s 1714=decide (Shadow.far 136 15 z ∧ 2^136≤z.u):=
  (actual_tags ports240 s 136 15 z G S hit).2
theorem relay (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue Enter240.saved s.basis=h) (hn:s.basis 1715=false) (hf:s.basis 1713=x) (hu:s.basis 1714=y) :
    let out:=run (body idx (withArchive d)) m s
    regValue Enter240.saved out.basis=h ∧ out.basis 1715=false ∧ out.basis 1713=x ∧ out.basis 1714=y :=
  keep_values 1715 1713 1714 Enter240.saved s (run (body idx (withArchive d)) m s) h x y (keeps_stored d s m) high hn hf hu
theorem saved_at_leave (d:Bool) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool)
    (small:min z.u z.v<2^136) (packed:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714
      (negative S z.u) (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (body idx (withArchive d)) ticks (run Partial.enter240 head cut)
    regValue Enter240.saved out.basis=(if Shadow.far 136 15 z then Shadow.high 136 15 z else 0) ∧
      out.basis 1715=false ∧ out.basis 1713=decide (Shadow.far 136 15 z) ∧
      out.basis 1714=decide (Shadow.far 136 15 z ∧ 2^136≤z.u):=by
  let pre:=run Partial.enter240 head cut
  have high:=Enter240.high_from_cut raw cut z G S head small packed input
  have body:=Enter240.from_full raw cut z G S head small packed input
  have tags:=source_tags pre.basis z G S body.2.1
  exact relay d pre ticks (if Shadow.far 136 15 z then Shadow.high 136 15 z else 0) _ _ high tags.1 tags.2.1 tags.2.2
#print axioms saved_at_leave
end ECDSAAdd.Entrant.StairPacket.NativePack240


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run routed unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
def protectedSites:List Wire:=[1708,1706,1707]++Enter255.saved

theorem admin_cover (d:Bool) : wires (withArchive d)⊆(support++ArchiveBoundary255.rawPortsList).toFinset:=by
  rw [withArchive,wires_append,List.toFinset_append]
  exact Finset.union_subset_union (packs d) (ArchiveBoundary255.load_cover d)

theorem free_native : ∀q∈protectedSites,¬MayTouch idx (windowNet idx q):=by decide +kernel
theorem free_admin : ∀q∈protectedSites,q∉(support++ArchiveBoundary255.rawPortsList):=by decide +kernel
theorem keeps_stored (d:Bool) (s:State) (m:List Bool) (q:Wire) (hq:q∈protectedSites) :
    (run (body idx (withArchive d)) m s).basis q=s.basis q:=
  body_cover idx (withArchive d) protectedSites (support++ArchiveBoundary255.rawPortsList) free_native free_admin (admin_cover d) s m q hq
theorem source_tags (s:BasisState) (z:SkywalkNat.State) (G S:Bool)
    (hit:∀q∈wires EnterProof.forward,s (map255 q)=(shadowRow 129 15 z G S).testBit q) :
    s 1708=false ∧ s 1706=decide (Shadow.far 129 15 z) ∧ s 1707=decide (Shadow.far 129 15 z ∧ 2^129≤z.u):=
  (actual_tags ports255 s 129 15 z G S hit).2
theorem relay (d:Bool) (s:State) (m:List Bool) (h:Nat) (x y:Bool)
    (high:regValue Enter255.saved s.basis=h) (hn:s.basis 1708=false) (hf:s.basis 1706=x) (hu:s.basis 1707=y) :
    let out:=run (body idx (withArchive d)) m s
    regValue Enter255.saved out.basis=h ∧ out.basis 1708=false ∧ out.basis 1706=x ∧ out.basis 1707=y :=
  keep_values 1708 1706 1707 Enter255.saved s (run (body idx (withArchive d)) m s) h x y (keeps_stored d s m) high hn hf hu
theorem saved_at_leave (d:Bool) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool)
    (small:min z.u z.v<2^129) (packed:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707
      (negative S z.u) (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) cut)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (body idx (withArchive d)) ticks (run Partial.enter255 head cut)
    regValue Enter255.saved out.basis=(if Shadow.far 129 15 z then Shadow.high 129 15 z else 0) ∧
      out.basis 1708=false ∧ out.basis 1706=decide (Shadow.far 129 15 z) ∧
      out.basis 1707=decide (Shadow.far 129 15 z ∧ 2^129≤z.u):=by
  let pre:=run Partial.enter255 head cut
  have high:=Enter255.high_from_cut raw cut z G S head small packed input
  have body:=Enter255.from_full raw cut z G S head small packed input
  have tags:=source_tags pre.basis z G S body.2.1
  exact relay d pre ticks (if Shadow.far 129 15 z then Shadow.high 129 15 z else 0) _ _ high tags.1 tags.2.1 tags.2.2
#print axioms saved_at_leave
end ECDSAAdd.Entrant.StairPacket.NativePack255


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
theorem history_only (i:Nat) (hi:i≤512) (d:Bool) (q:Wire)
    (mem:q∈wires (Rolling1588.Integer.encodePrefix base d i)) : Earlier i q:=by
  rw [Rolling1588.Integer.prefix_support_eq] at mem
  obtain ⟨j,rfl,h|⟨low,high⟩⟩:=StackOB5Base.encodePrefix_mem i hi _ mem
  · exact ⟨j,h,Or.inl rfl⟩
  · exact ⟨j-1028,by omega,Or.inr (congrArg base (by omega))⟩

theorem initial (i x p:Nat) (hi:i≤512) (d:Bool) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) : Domain i x p s:=by
  obtain ⟨raw,good,bits⟩:=stage
  refine ⟨⟨s.phase,raw.basis⟩,⟨rfl,?_⟩,good⟩
  intro q out
  change s.basis q=raw.basis q
  rw [bits];exact run_preserves_outside _ [] raw _ (fun mem=>out (history_only i hi d q mem))

theorem leaves_reference (i x p:Nat) (hi:i≤512) (d:Bool) (s:State) (dom:Domain i x p s) :
    ∃original:State,Rolling1588.Integer.Stage base d x p i original.basis ∧ Coherent i s original := by
  obtain ⟨ref,match',good⟩:=dom
  let original:State:=⟨s.phase,(run (Rolling1588.Integer.encodePrefix base d i) [] ref).basis⟩
  refine ⟨original,⟨ref,good,rfl⟩,rfl,?_⟩
  intro q off
  exact (match'.2 q off).trans (run_preserves_outside _ [] ref _ (fun mem=>off (history_only i hi d q mem))).symm

theorem reads_now {i:Nat} (hi:i<512) {s ref:State} (same:Coherent i s ref) :
    ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=ref.basis q :=
  fun q hit=>same.2 q (fun earlier=>away hi earlier (List.mem_toFinset.mp hit))

theorem match_input (L:SkywalkIntegerLayout) (A B:Int) (G:Bool) (a b:BasisState)
    (eq:∀q∈L.wires.toFinset,a q=b q) (input:SkywalkIntegerInput L A B G b) : SkywalkIntegerInput L A B G a := by
  have bits (q:Wire) (h:q∈L.a ∨ q∈L.b ∨ q=L.previous ∨ q=L.ext ∨ q=L.history ∨ q∈L.carry) : a q=b q:=by
    apply eq q <| List.mem_toFinset.mpr ?_
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.a,SkywalkIntegerLayout.b,List.mem_cons,List.mem_append] at *
    tauto
  have aw:=(signedRegValue_eq_iff _ a b).mpr (fun q h=>bits q (Or.inl h))
  have bw:=(signedRegValue_eq_iff _ a b).mpr (fun q h=>bits q (Or.inr (Or.inl h)))
  have cw:=regValue_congr L.carry a b (fun q h=>bits q (by simp [h]))
  obtain ⟨va,vb,g,e,h,c⟩:=input
  exact ⟨aw.trans va,bw.trans vb,(bits _ (by simp)).trans g,(bits _ (by simp)).trans e,(bits _ (by simp)).trans h,cw.trans c⟩

theorem true_input (i x p:Nat) (hi:i<512) (hp0:0<p) (hx0:0<x) (odd:p%2=1) (hp:p<2^256)
    (gap:p+2^32≤2^256) (hx:x<p) (cop:x.Coprime p) (s:State) (dom:Domain i x p s) :
    let z:=SkywalkNat.step^[i] (SkywalkNat.init x p)
    ∃G S:Bool,SkywalkIntegerInput (W.compactSkywalkTickLayout base i) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G s.basis := by
  obtain ⟨ref,stage,same⟩:=leaves_reference i x p (by omega) true s dom
  obtain ⟨G,S,input⟩:=PortalValues.real_input true x p i hp0 hx0 odd hp gap hx cop hi ref stage
  exact ⟨G,S,match_input _ _ _ _ _ _ (reads_now hi same) input⟩
#print axioms true_input
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary270 ParkEndpoint
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem no_phase (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 270 original.basis) : (run canonical [] raw).phase=raw.phase := by
  obtain ⟨ref,hs,ag⟩:=local_reference 270 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have step:=(W.compactSkywalkStageStep base base_pool_nodup x p 270 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).1
  have inc:=(run_local_increment canonical raw ref [] (fun q h=>by
    have mem:=(W.compactSkywalkTick_support base 270 (by decide) base_pool_nodup) h
    exact (read q mem).trans (ag q mem))).1
  change (run canonical [] ref).phase=ref.phase at step
  rw [step,Bool.xor_self] at inc
  cases h:(run canonical [] raw).phase <;> cases k:raw.phase <;> simp_all

theorem scratch_table : ∀i:Fin 157,23≤ i.val →
    rawPorts i∉dst ∧ OB5.sig 270 (rawPorts i)=1556+(i.val-23) ∧ ∀v:Fin 10,rawPorts i≠NativePack270.history v := by decide +kernel

theorem coordinate (s raw:State) : (stash s (pullState (OB5.sig 270) raw)).basis 285=raw.basis 285 ∧
    (stash s (pullState (OB5.sig 269) raw)).basis 285=raw.basis 285 := ⟨rfl,rfl⟩

theorem stash_slots (raw after tags:State) (phase:after.phase=raw.phase) (same:after.basis 285=raw.basis 285)
    (zero:∀k:Fin 134,after.basis (1556+k.val)=false) :
    let start:=stash tags (pullState (OB5.sig 269) raw)
    let out:=stash tags (pullState (OB5.sig 270) after)
    out.phase=start.phase ∧ out.basis 285=start.basis 285 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  refine ⟨phase,(coordinate _ _).1.trans (same.trans (coordinate _ _).2.symm),?_⟩
  intro i hi
  have ⟨off,eq,_⟩:=scratch_table i hi
  simp only [stash,if_neg off]
  exact (congrArg after.basis eq).trans (zero ⟨i.val-23,by have h:=i.isLt;omega⟩)

theorem exposed (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false) (m:List Bool) :
    let start:=stash tags (pullState (OB5.sig 269) raw)
    let out:=run physP m start
    out.phase=start.phase ∧ out.basis 285=start.basis 285 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  have out:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).1
  have bits:=after_cells d x hx0 hx raw original read stage
  dsimp only
  rw [out]
  exact stash_slots raw (run canonical [] raw) tags (no_phase d x hx0 hx raw original read stage) bits.1 bits.2
#print axioms exposed
end ECDSAAdd.Entrant.StairPacket.EndTick


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body
theorem masked_body (P Q:Program) (qs tags:List Wire) (s:State) (m t:List Bool)
    (blank:∀q∈tags,q∉wires P) (away:∀q∈qs,q∉tags)
    (steady:∀s:State,∀q∈qs,(run Q t s).basis q=s.basis q) :
    ∀q∈qs,(run Q t (run P m s)).basis q=(run Q t (run P m (eraseSites tags s))).basis q:=by
  intro q h
  rw [steady _ q h,steady _ q h,erase_run tags P blank]
  simp [eraseSites,away _ h]
namespace NativePack240
theorem saved_with_pending (d:Bool) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool)
    (small:min z.u z.v<2^136) (packed:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714
      (negative S z.u) (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending cut))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (body idx (withArchive d)) ticks (run Partial.enter240 head cut)
    regValue Enter240.saved out.basis=(if Shadow.far 136 15 z then Shadow.high 136 15 z else 0) ∧
      out.basis 1715=false ∧ out.basis 1713=decide (Shadow.far 136 15 z) ∧
      out.basis 1714=decide (Shadow.far 136 15 z ∧ 2^136≤z.u):=by
  have observed:=saved_at_leave d raw (eraseSites Enter240.pending cut) z G S head ticks small packed input
  have away:∀q∈protectedSites,q∉Enter240.pending:=by decide +kernel
  have eq:=masked_body Partial.enter240 (body idx (withArchive d)) protectedSites Enter240.pending cut head ticks Enter240.avoid_enter away
    (fun s=>keeps_stored d s ticks)
  exact keep_values 1715 1713 1714 Enter240.saved _ _ _ _ _ eq observed.1 observed.2.1 observed.2.2.1 observed.2.2.2
end NativePack240
namespace NativePack255
theorem saved_with_pending (d:Bool) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (head ticks:List Bool)
    (small:min z.u z.v<2^129) (packed:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707
      (negative S z.u) (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending cut))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let out:=run (body idx (withArchive d)) ticks (run Partial.enter255 head cut)
    regValue Enter255.saved out.basis=(if Shadow.far 129 15 z then Shadow.high 129 15 z else 0) ∧
      out.basis 1708=false ∧ out.basis 1706=decide (Shadow.far 129 15 z) ∧
      out.basis 1707=decide (Shadow.far 129 15 z ∧ 2^129≤z.u):=by
  have observed:=saved_at_leave d raw (eraseSites Enter255.pending cut) z G S head ticks small packed input
  have away:∀q∈protectedSites,q∉Enter255.pending:=by decide +kernel
  have eq:=masked_body Partial.enter255 (body idx (withArchive d)) protectedSites Enter255.pending cut head ticks Enter255.avoid_enter away
    (fun s=>keeps_stored d s ticks)
  exact keep_values 1708 1706 1707 Enter255.saved _ _ _ _ _ eq observed.1 observed.2.1 observed.2.2.1 observed.2.2.2
end NativePack255
#print axioms NativePack255.saved_with_pending
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed IntegerPacket RailPair Portal270Flag ArchiveBoundary270
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
theorem past_sites : ∀r:Fin 15,ordinary (windowNet sourceIdx (ports (shape sourceIdx) r).a0) ∧
    ordinary (windowNet sourceIdx (ports (shape sourceIdx) r).history) := by decide +kernel
theorem earlier (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 n f u
    (pullState (OB5.sig 269) raw) (eraseSites src s)) (q:Wire) (clean:ordinary q) :
    (stash s (pullState (OB5.sig 269) raw)).basis q=s.basis q := by
  obtain ⟨hs,hd,hn,hf,hu,hh⟩:=clean
  have eq:=cut.unchanged _ hn hf hu hh
  simpa [stash,eraseSites,hs,hd] using eq.symm

theorem past_cells (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 n f u
    (pullState (OB5.sig 269) raw) (eraseSites src s)) :
    physicalCells sourceIdx (stash s (pullState (OB5.sig 269) raw))=physicalCells sourceIdx s := by
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (earlier _ _ _ _ _ cut _ (past_sites r).1) (earlier _ _ _ _ _ cut _ (past_sites r).2)
theorem tag_address (s other:State) :
    (stash s other).basis (rawPorts 20)=s.basis 1701 ∧
    (stash s other).basis (rawPorts 21)=s.basis 1702 ∧
    (stash s other).basis (rawPorts 22)=s.basis 1703:=⟨rfl,rfl,rfl⟩
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
def canonical (i x p:Nat) := SkywalkTrace.next^[i] (encode false false x p)
def unsigned (i x p:Nat) := SkywalkNat.step^[i] (SkywalkNat.init x p)
structure Bounds (x p:Nat) : Prop where
  positive : 0<p
  nonzero : 0<x
  odd : p%2=1
  cap : p<2^256
  gap : p+2^32≤2^256
  small : x<p
  coprime : x.Coprime p
def InputAt (i:Nat) (z:SkywalkRails.State) (s:State):=SkywalkIntegerInput (W.compactSkywalkTickLayout base i) z.a z.b z.g s.basis
theorem fixed_input (i x p:Nat) (hi:i<512) (good:Bounds x p) (s:State) (dom:Domain i x p s):
    InputAt i (canonical i x p) s:=by
  obtain ⟨ref,stage,match'⟩:=leaves_reference i x p (by omega) true s dom
  exact match_input _ _ _ _ _ _ (reads_now hi match')
    (original_input true x p i good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime hi ref stage)
theorem unique_input {i:Nat} {s:State} {a b:SkywalkRails.State} (left:InputAt i a s) (right:InputAt i b s):a=b:=
  SkywalkRails.State.ext (left.1.symm.trans right.1) (left.2.1.symm.trans right.2.1) (left.2.2.1.symm.trans right.2.2.1)
theorem encode_route (g sg:Bool) (z:SkywalkNat.State) : (encode g sg z.u z.v).g=g:=by cases g <;> rfl
theorem advance_signed (i b x p:Nat) (lo:15≤ i) (hi:i+15<512) (fixed:Fixed i) (good:Bounds x p)
    (raw history:State) (dom:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (small:min (unsigned i x p).u (unsigned i x p).v<2^b) :
    let z:=unsigned i x p
    let t:=Shadow.reduced b 15 z
    let flags:=SharedSigned.flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    let endState:=unsigned (i+15) x p
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode flags.1 flags.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
      InputAt (i+15) (encode flags.1 flags.2 endState.u endState.v) (endRaw i raw history):=by
  let z:=unsigned i x p
  have odd:z.v%2=1:=(SkywalkNat.iter_valid i (SkywalkNat.init x p) good.positive good.odd).2.1
  obtain ⟨a,b'⟩:=SharedSigned.same b z small odd G S
  have eq:=unique_input input (fixed_input i x p (by omega) good raw dom)
  have stepRel:canonical (i+15) x p=SkywalkTrace.next^[15] (canonical i x p):=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have numRel:unsigned (i+15) x p=SkywalkNat.step^[15] z:=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have nextDom:=advance i x p lo (by omega) fixed good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw history dom
  have active:=fixed_input (i+15) x p hi good (endRaw i raw history) nextDom
  dsimp only
  refine ⟨a,?_⟩
  rw [stepRel,←eq,b'] at active
  simpa only [numRel] using active
#print axioms advance_signed
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
theorem native_carry (j:Fin 23) (z:SkywalkRails.State) (s:State) (ready:onRails j 15 z s.basis) (q:Wire)
    (mem:q∈((ports (shape j) 15).carry.map (windowNet j))) : s.basis q=false:=by
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp mem
  exact (regValue_zero _ _).mp ready.2.2.2.1 _ hw
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000
theorem carry225 (z:SkywalkRails.State) (s:State) (ready:onRails 10 15 z s.basis) :
    ∀q:Wire,1556≤q → q≤1717 → s.basis q=false:=by
  have portsEq:((ports (shape 10) 15).carry.map (windowNet 10))=List.range' 1556 162:=by decide +kernel
  intro q low high
  apply native_carry _ _ _ ready
  rw [portsEq,List.mem_range'_1];exact ⟨low,Nat.lt_succ_of_le high⟩
theorem carry240 (z:SkywalkRails.State) (s:State) (ready:onRails 11 15 z s.basis) :
    ∀q:Wire,1556≤q → q≤1709 → s.basis q=false:=by
  have portsEq:((ports (shape 11) 15).carry.map (windowNet 11))=List.range' 1556 154:=by decide +kernel
  intro q low high
  apply native_carry _ _ _ ready
  rw [portsEq,List.mem_range'_1];exact ⟨low,Nat.lt_succ_of_le high⟩
theorem carry255 (z:SkywalkRails.State) (s:State) (ready:onRails 12 15 z s.basis) :
    ∀q:Wire,1556≤q → q≤1702 → s.basis q=false:=by
  have portsEq:((ports (shape 12) 15).carry.map (windowNet 12))=List.range' 1556 147:=by decide +kernel
  intro q low high
  apply native_carry _ _ _ ready
  rw [portsEq,List.mem_range'_1];exact ⟨low,Nat.lt_succ_of_le high⟩
#print axioms carry255
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary270 ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run routed

theorem pack_support (d:Bool) : wires (program d) ⊆ ((List.finRange 10).map history).toFinset := by cases d <;> decide +kernel
theorem outside (d:Bool) (q:Wire) (no:∀v:Fin 10,q≠history v) (m:List Bool) (s:State) :
    (run (program d) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro mem
  obtain ⟨v,_,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp (pack_support d mem))
  exact no v eq.symm
theorem bank_out : ∀q:Fin 23,∀v:Fin 10,rawPorts ⟨q,Nat.lt_trans q.isLt (by decide : 23<157)⟩≠history v := by decide +kernel
theorem archive_ready (d:Bool) (start tick:State) (m:List Bool) (past:SkywalkNat.State) (g sign cross:Bool)
    (odd:past.v%2=1) (small:min past.u past.v<2^129) (prior:PastFacts sourceIdx rawPorts 129 past g sign cross start)
    (keptFive:∀i,tick.basis (history i)=start.basis (history i))
    (bank:∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩))
    (scratch:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) :
    MeasuredCodec5.legalAt history tick.basis ∧ ∃row<63145,ArchivePortAction.Frame rawPorts raw row (run (program d) m tick) := by
  let cells:=physicalCells sourceIdx start
  let f:=decide (Shadow.far 129 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  let out:=run (program d) m tick
  have legal:StairArchiveRaw.legal (physicalCells sourceIdx start):=by rw [prior.records];exact legal_signed 15 past g sign (by omega) odd
  have same (i:Fin 23) : out.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=
      start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩):=
    (outside d _ (bank_out i) m tick).trans (bank i)
  have tags:out.basis (rawPorts 20)=f ∧ out.basis (rawPorts 21)=u ∧ out.basis (rawPorts 22)=c:=
    ⟨(same 20).trans prior.far,(same 21).trans prior.suffix,(same 22).trans prior.crossed⟩
  have hw:∀i:Fin 157,i.val<23 → out.basis (rawPorts i)=data i :=
    observed start out (fun q=>same ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  have fresh (i:Fin 157) (hi:23≤ i.val) : out.basis (rawPorts i)=false :=
    (outside d _ (EndTick.scratch_table i hi).2.2 m tick).trans (scratch i hi)
  obtain ⟨row,limit,matchRow⟩:=interrupted_row 129 past small odd g sign cross cells
    (prior.records.trans (true_records _ _ small odd _ _).symm)
  exact ⟨legal_prefix _ _ legal keptFive,row,limit,starting_frame rawPorts out row data matchRow hw fresh⟩
#print axioms archive_ready
end ECDSAAdd.Entrant.StairPacket.NativePack270


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxHeartbeats 2300000
set_option maxRecDepth 18000
attribute [local irreducible] run
theorem fixed_step (lo i:Nat) (hlo:lo ≤ i) (hi:i<512) {a b:State} (same:Coherent lo a b) (m:List Bool) :
    Coherent lo (run (W.compactSkywalkTick base i) m a) (run (W.compactSkywalkTick base i) m b):=by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have eq:=run_measured_locality P (wires P) (Finset.Subset.refl _) a b m same.1 (fun q mem=>
    same.2 q (fun old=>away hi (earlier_mono hlo old) (List.mem_toFinset.mp (sub mem))))
  refine ⟨eq.1,?_⟩
  intro q fresh
  by_cases used:q∈wires P
  · exact eq.2 q used
  · exact (run_preserves_outside _ _ _ _ used).trans ((same.2 _ fresh).trans (run_preserves_outside _ _ _ _ used).symm)
theorem fixed_span (lo i n:Nat) (hlo:lo ≤ i) (lim:i+n≤512) (a b:State) (m:List Bool) (same:Coherent lo a b) :
    Coherent lo (run (span i n) m a) (run (span i n) m b):=by
  induction n generalizing i a b m with
  | zero=>simpa [span,run] using same
  | succ n ih=>
    simp only [span,run_append,run_take]
    exact ih (i+1) (by omega) (by omega) _ _ _ (fixed_step lo i hlo (by omega) same m)
theorem trace_sites (i n x p:Nat) (lim:i+n≤512) (good:Bounds x p) (raw:State) (m:List Bool) (domain:Domain i x p raw)
    (r:Nat) (first:i≤r) (last:r < i+n) :
    let out:=run (span i n) m raw
    let cell:=SkywalkTrace.code (canonical r x p)
    out.basis (base r)=cell.1 ∧ out.basis (base (1028+r))=cell.2:=by
  obtain ⟨ref,match',stage⟩:=domain
  have final:=full_span i n x p lim good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have bits:=(W.compactSkywalkStage_fields_iff base _ (i+n) lim base_pool_nodup _).mp final
  have hist:=bits.2.2.2.1 r last
  have link:=fixed_span i i n (Nat.le_refl _) lim raw ref m match'
  have unmarked:∀q∈[base r,base (1028+r)],¬Earlier i q:=by
    intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rintro ⟨t,ht,h|h⟩ <;> simp only [base,Wire] at h <;> omega
  exact ⟨(link.2 _ (unmarked _ (by simp))).trans hist.1,(link.2 _ (unmarked _ (by simp))).trans hist.2⟩
#print axioms trace_sites
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run

theorem span_phase (i n x p:Nat) (bounds:i+n≤512) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    (run (span i n) m s).phase=s.phase := by
  induction n generalizing i s m with
  | zero => simp [span,run]
  | succ n ih =>
    have first:=W.compactSkywalkStageStep base base_pool_nodup x p i good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime (by omega) s m stage
    rw [span,run_append,run_take]
    exact (ih (i+1) (by omega) _ _ first.2).trans first.1

theorem origin_phase (i x p:Nat) (bounds:i+15≤512) (good:Bounds x p) (raw history:State)
    (dom:Domain i x p raw) : (origin i raw history).phase=raw.phase := by
  obtain ⟨ref,same,stage⟩:=dom
  have match':=fixed_span i i 15 (Nat.le_refl _) bounds raw ref [] same
  exact match'.1.trans ((span_phase _ _ _ _ bounds good ref [] stage).trans same.1.symm)
theorem endRaw_phase (i x p:Nat) (bounds:i+15≤512) (good:Bounds x p) (raw history:State)
    (dom:Domain i x p raw) : (endRaw i raw history).phase=raw.phase :=
  origin_phase i x p bounds good raw history dom
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body
namespace NativePack225
def spares:=List.range' 1724 2
theorem extra_geometry : ∀q∈spares,¬MayTouch idx (windowNet idx q) ∧ q∉support ∧ q∉ports225 ∧
    OB5.sig 224 q∈(W.compactSkywalkTickLayout base 225).carry ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ q∉RailPair.sites Enter225.upperPairs :=by decide +kernel
theorem spare_unchanged (d:Bool) (s:State) (a b:List Bool) (q:Wire) (member:q∈spares) :
    (run (body idx (program d)) b (run Partial.enter225 a s)).basis q=s.basis q:=by
  have first:=body_cover idx (program d) spares support (fun v h=>(extra_geometry v h).1)
    (fun v h=>(extra_geometry v h).2.1) (packs d) (run Partial.enter225 a s) b q member
  exact first.trans (run_preserves_outside _ a s q (fun mem=>(extra_geometry _ member).2.2.1 (List.mem_toFinset.mp (Enter225.programCover mem))))
theorem extra_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long (pullState (OB5.sig 224) raw) s)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) A B G raw.basis) :
    ∀q∈spares,(run (body idx (program d)) b (run Partial.enter225 a s)).basis q=false:=by
  intro q h
  obtain ⟨_,_,_,carry,hn,hf,hu,hi⟩:=extra_geometry q h
  have stored:=cut.unchanged q hn hf hu hi
  have original:=stored
  exact (spare_unchanged d s a b q h).trans (original.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack225
namespace NativePack255
def spares:=List.range' 1713 6
theorem extra_geometry : ∀q∈spares,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧ q∉ports255 ∧
    OB5.sig 254 q∈(W.compactSkywalkTickLayout base 255).carry ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ q∉RailPair.sites Enter255.upperPairs :=by decide +kernel
theorem spare_unchanged (d:Bool) (s:State) (a b:List Bool) (q:Wire) (member:q∈spares) :
    (run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=s.basis q:=by
  have first:=body_cover idx (withArchive d) spares (support++ArchiveBoundary255.rawPortsList) (fun v h=>(extra_geometry v h).1)
    (fun v h=>(extra_geometry v h).2.1) (admin_cover d) (run Partial.enter255 a s) b q member
  exact first.trans (run_preserves_outside _ a s q (fun mem=>(extra_geometry _ member).2.2.1 (List.mem_toFinset.mp (Enter255.programCover mem))))
theorem extra_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) A B G raw.basis) :
    ∀q∈spares,(run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=false:=by
  intro q h
  obtain ⟨_,_,_,carry,hn,hf,hu,hi⟩:=extra_geometry q h
  have stored:=cut.unchanged q hn hf hu hi
  have same:∀q∈spares,q∉Enter255.pending:=by decide +kernel
  have original:s.basis q=raw.basis (OB5.sig 254 q):=by simpa [eraseSites,same _ h] using stored
  exact (spare_unchanged d s a b q h).trans (original.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack255
#print axioms NativePack255.extra_clean
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
def endSlice (d:Bool) := EndTick.physP ++ (program d ++ Partial.archiveLoad270 d)
def endUndo (d:Bool) := Partial.archiveRestore270 d ++ (reverse d ++ EndTick.physQ)
structure Transition (inverse:Program) (s tick:State) : Prop where
  phase : tick.phase=s.phase
  keptFive : ∀i,tick.basis (history i)=s.basis (history i)
  keptBank : ∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)
  scratch : ∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false
  undo : ∀n,run inverse n tick=s

abbrev TickStep:=Transition EndTick.physQ

theorem tick_intro (s tick:State) (ph:tick.phase=s.phase)
    (obs:∀q,EndTick.readOnly q → tick.basis q=s.basis q)
    (zero:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) (undo:∀m,run EndTick.physQ m tick=s) :
    TickStep s tick :=
  ⟨ph,fun i=>obs _ (EndTick.oldPrefix i),fun i=>obs _ (EndTick.oldBank i),zero,undo⟩

theorem observe_tick (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:EndTick.Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false) (m:List Bool) :
    let start:=ParkEndpoint.stash tags (pullState (OB5.sig 269) raw)
    TickStep start (run EndTick.physP m start) := by
  let s:=ParkEndpoint.stash tags (pullState (OB5.sig 269) raw)
  have h:=EndTick.exposed d x hx0 hx raw original tags read stage hist swapSlot m
  have u:=(EndTick.physical d x hx0 hx raw original tags read stage hist swapSlot m).2
  exact tick_intro s (run EndTick.physP m s) h.1 (fun q hq=>EndTick.observes q hq s m h.2.1) h.2.2 u

theorem sequence_law (p e f r v q:Program) (s:State) (m:List Bool) (claim:State→Prop)
    (tick:State) (first:run p m s=tick) (phase:tick.phase=s.phase) (inv:∀a,run q a tick=s)
    (packed:State) (store:run e (m.drop (measurementCount p)) tick=packed) (middle:packed.phase=tick.phase)
    (unpack:∀a,run v a packed=tick) (out:State)
    (written:run f ((m.drop (measurementCount p)).drop (measurementCount e)) packed=out)
    (endPhase:out.phase=packed.phase) (good:claim out) (unwrite:∀a,run r a out=packed) :
    let result:=run (p++(e++f)) m s
    result.phase=s.phase ∧ claim result ∧ ∀a,run (r++(v++q)) a result=s := by
  dsimp only
  simp only [run_append,run_take,first,store,written]
  exact ⟨endPhase.trans (middle.trans phase),good,fun a=>by rw [unwrite,unpack,inv]⟩

theorem finish_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (p ++ (program d ++ Partial.archiveLoad270 d)) m s
    out.phase=s.phase ∧ (∃row<63145,Frame codePorts (code d) row out) ∧
      ∀n,run (Partial.archiveRestore270 d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) (Partial.archiveLoad270 d) (Partial.archiveRestore270 d)
    (reverse d) q s m (fun out=>∃row<63145,Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Partial.archiveLoad270 d) f pre) rfl act.1
    ⟨row,limit,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem finish_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  finish_generic EndTick.physP EndTick.physQ d s m step past G S cross odd small prior
#print axioms finish_slice
end ECDSAAdd.Entrant.StairPacket.NativePack270


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed IntegerPacket SkywalkRails StairArchiveRaw
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem read_trace (n r:Nat) (h:r<n) (s:SkywalkRails.State) :
    read (SkywalkTrace.trace n s) r=SkywalkTrace.code (SkywalkTrace.next^[r] s):=by
  induction n generalizing r s with
  | zero=>omega
  | succ n ih=>
    cases r with
    | zero=>rfl
    | succ r=>
      simpa only [SkywalkTrace.trace,StairArchiveRaw.read,List.getElem?_cons_succ,Function.iterate_succ_apply] using ih r (by omega) (SkywalkTrace.next s)
def Geometry (i:Nat) (j:Fin 23) := ∀r:Fin 15,
  let q:=windowNet j (ports (shape j) r).a0
  let w:=windowNet j (ports (shape j) r).history
  q∉sites i ∧ w∉sites i ∧ OB5.sig (i+14) q=base (i+r.val) ∧ OB5.sig (i+14) w=base (1028+(i+r.val))
theorem places225:Geometry 225 10:=by unfold Geometry;decide +kernel
theorem places240:Geometry 240 11:=by unfold Geometry;decide +kernel
theorem places255:Geometry 255 12:=by unfold Geometry;decide +kernel
theorem reference_cells (i:Nat) (j:Fin 23) (x p:Nat) (lim:i+15≤512) (place:Geometry i j) (good:Bounds x p)
    (raw history:State) (r:Fin 15) (domain:Domain i x p raw):
    cell (shape j) r (mappedBasis j (origin i raw history).basis)=SkywalkTrace.code (canonical (i+r.val) x p):=by
  have hist:=trace_sites i 15 x p lim good raw [] domain (i+r.val) (by omega) (by have hr:=r.isLt;omega)
  obtain ⟨noA,noB,a,b⟩:=place r
  unfold cell mappedBasis
  rw [outside i raw history _ noA,outside i raw history _ noB,a,b]
  exact Prod.ext hist.1 hist.2
theorem recorded_equal (i:Nat) (j:Fin 23) (x p:Nat) (lim:i+15≤512) (place:Geometry i j) (good:Bounds x p)
    (raw history:State) (domain:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (trace:physicalCells j history=SkywalkTrace.trace 15 (encode G S (unsigned i x p).u (unsigned i x p).v)) (r:Fin 15) :
    cell (shape j) r (mappedBasis j history.basis)=cell (shape j) r (mappedBasis j (origin i raw history).basis):=by
  have eq:=unique_input input (fixed_input _ _ _ (by omega) good raw domain)
  rw [eq] at trace
  have seen:=congrArg (fun xs=>read xs r) trace
  change read (readCells (shape j) 0 15 (mappedBasis j history.basis)) r=read (SkywalkTrace.trace 15 (canonical i x p)) r at seen
  rw [read_cells _ _ _ _ _ r.isLt,Nat.zero_add,read_trace _ _ r.isLt] at seen
  rw [reference_cells i j x p lim place good raw history r domain]
  have reorder:canonical (i+r.val) x p=SkywalkTrace.next^[r.val] (canonical i x p):=by
    rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  exact seen.trans (congrArg _ reorder.symm)
#print axioms recorded_equal
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
def RawRead (k q:Nat) :=
  let n:=W.compactSkywalkTickPreWidth k
  (k+16≤q ∧ q≤k+16+n) ∨ (786≤q ∧ q<786+n) ∨ q=1044+k ∨ q=base (skywalkPoolPreviousId k) ∨
  (1556≤q ∧ q+1<1556+n)
instance (k q:Nat) : Decidable (RawRead k q):=by unfold RawRead;infer_instance
theorem member_block (a n q:Nat) (m:q∈wireBlock base a n) : a+16≤q ∧ q<a+n+16:=by
  obtain ⟨r,hit,rfl⟩:=List.mem_map.mp m
  have b:=List.mem_range'_1.mp hit
  change a+16≤r+16 ∧ r+16<a+n+16;omega
theorem layout_choices (L:SkywalkIntegerLayout) (q:Wire) (h:q∈L.wires) :
    q=L.previous ∨ q=L.ext ∨ q=L.history ∨ q∈L.a ∨ q∈L.b ∨ q∈L.carry := by
  simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.a,SkywalkIntegerLayout.b,List.mem_cons,List.mem_append] at h ⊢
  tauto
theorem contained (k q:Nat) (lim:k<512) (used:q∈wires (W.compactSkywalkTick base k)) : RawRead k q:=by
  have h:=List.mem_toFinset.mp (W.compactSkywalkTick_support base k lim base_pool_nodup used)
  have cases':=layout_choices _ q h
  rw [W.compactSkywalkTick_a base k lim,W.compactSkywalkTick_b base k lim] at cases'
  let n:=W.compactSkywalkTickPreWidth k
  have positive:3≤n:=(W.compactSkywalkTick_width_bounds k lim).1
  change (k+16≤q ∧ q≤k+16+n) ∨ (786≤q ∧ q<786+n) ∨ q=1044+k ∨ q=base (skywalkPoolPreviousId k) ∨ (1556≤q ∧ q+1<1556+n)
  rcases cases' with prev|ext|hist|ha|hb|hc
  · exact Or.inr (Or.inr (Or.inr (Or.inl prev)))
  · apply Or.inl;change q=k+n+16 at ext;omega
  · apply Or.inr <| Or.inr <| Or.inl ?_;change q=1028+k+16 at hist;omega
  · apply Or.inl;have lim:=member_block k n q ha;omega
  · apply Or.inr <| Or.inl ?_;have lim:=member_block 770 n q hb;omega
  · apply Or.inr <| Or.inr <| Or.inr <| Or.inr ?_;have lim:=member_block 1540 (n-1) q hc;omega
theorem span_unchanged (i n q:Nat) (bound:i+n≤512) (clear:∀a<n,¬RawRead (i+a) q) (s:State) (m:List Bool) :
    (run (span i n) m s).basis q=s.basis q:=by
  induction n generalizing i s m with
  | zero=>simp [span,run]
  | succ n ih=>
    simp only [span,run_append,run_take]
    have tail:∀a<n,¬RawRead (i+1+a) q:=by intro a h;simpa only [Nat.add_assoc,Nat.add_comm 1 a] using clear (a+1) (by omega)
    rw [ih (i+1) (by omega) tail]
    exact run_preserves_outside _ _ _ _ (fun used=>clear 0 (by omega) (by simpa only [Nat.add_zero] using contained i q (by omega) used))
#print axioms span_unchanged
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270 ParkEndpoint Portal270Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def lastWindow (d:Bool) := Partial.park270 ++ (Partial.portal270Inv ++ endSlice d)
def lastUnwind (d:Bool) := endUndo d ++ (Partial.portal270 ++ Partial.park270Inv)

theorem after_park (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 n f u (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (G S cross:Bool)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode G S past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (orientation:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    PastFacts sourceIdx rawPorts 129 past G S cross (stash s (pullState (OB5.sig 269) raw)) := by
  have cells:=past_cells raw s n f u cut
  have tag:=tag_address s (pullState (OB5.sig 269) raw)
  refine ⟨cells.trans records,tag.1.trans mode,?_,tag.2.2.trans flipped⟩
  rw [cells];exact tag.2.1.trans orientation

theorem last_window (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount Partial.park270)
  let one:=run Partial.portal270Inv n (run Partial.park270 m s)
  let tape:=n.drop (measurementCount Partial.portal270Inv)
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 269) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 129 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick.physP tape one):=by rw [eqOne];exact tick
  have body:=finish_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
#print axioms last_window
end ECDSAAdd.Entrant.StairPacket.NativePack270


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
attribute [local irreducible] run routed measurementCount
theorem after_encoded (j:Fin 23) (P:Program) (outPorts:Ports) (d:Bool) (row:Nat) (src:State) (m:List Bool)
    (final:Frame outPorts (code d) row (run P (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m src)))
    (i:Fin 157) (hi:16 ≤ i.val) (q:Wire) (slot:outPorts i=q) (free:¬MayTouch j (windowNet j q)) :
    (run (body j P) m src).basis q=false:=by
  simp only [body,run_append,run_take]
  apply (route_outside j 1 14 (by decide) q (named_range j 1 14 q (by decide) free) _ _).trans
  rw [←slot,final,archive_blank _ _ hi,Nat.zero_testBit]
namespace NativePack240
open ArchiveBoundary240
theorem popped (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m src))) :
    ∀k:Fin 3,(run (body idx (withArchive d)) m src).basis (1716+k.val)=false:=by
  have phys:∀k:Fin 3,codePorts ⟨154+k.val,by omega⟩=1716+k.val ∧ ¬MayTouch idx (windowNet idx (1716+k.val)):=by decide +kernel
  intro k
  exact after_encoded idx (withArchive d) codePorts d row src m frame ⟨154+k.val,by omega⟩ (by dsimp;omega) _
    (phys k).1 (phys k).2
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem popped (d:Bool) (src:State) (m:List Bool) (row:Nat)
    (frame:Frame codePorts (code d) row (run (withArchive d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m src))) :
    ∀k:Fin 3,(run (body idx (withArchive d)) m src).basis (1709+k.val)=false:=by
  have phys:∀k:Fin 3,codePorts ⟨154+k.val,by omega⟩=1709+k.val ∧ ¬MayTouch idx (windowNet idx (1709+k.val)):=by decide +kernel
  intro k
  exact after_encoded idx (withArchive d) codePorts d row src m frame ⟨154+k.val,by omega⟩ (by dsimp;omega) _
    (phys k).1 (phys k).2
end NativePack255
#print axioms NativePack255.popped
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run routed measurementCount body
theorem from_append {P Q:Program} {s:State} {t:List Bool} {prop:State→Prop}
    (after:prop (run Q (t.drop (measurementCount P)) (run P t s))) : prop (run (P++Q) t s):=by
  rwa [run_append,run_take]
namespace NativePack240
open ArchiveBoundary240
theorem archive_result (d:Bool) (row:Nat) (lim:row<63145) (s:State) (m:List Bool)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    Frame codePorts (code d) row (run (withArchive d) m s) :=
  from_append (prop:=Frame codePorts (code d) row)
    (load_run d row lim _ (m.drop (measurementCount (program d))) raw).2.1
theorem receipt (d:Bool) (s:State) (m:List Bool) (row:Nat) (lim:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (body idx (withArchive d)) m s) ∧
      ∀k:Fin 3,(run (body idx (withArchive d)) m s).basis (1716+k.val)=false:=by
  have frame:=archive_result d row lim _ _ raw
  exact ⟨body_keeps idx (withArchive d) codePorts d row s m encoded_outside frame,popped d s m row frame⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem archive_result (d:Bool) (row:Nat) (lim:row<63145) (s:State) (m:List Bool)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    Frame codePorts (code d) row (run (withArchive d) m s) :=
  from_append (prop:=Frame codePorts (code d) row)
    (load_run d row lim _ (m.drop (measurementCount (program d))) raw).2.1
theorem receipt (d:Bool) (s:State) (m:List Bool) (row:Nat) (lim:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s))) :
    Kept codePorts d row (run (body idx (withArchive d)) m s) ∧
      ∀k:Fin 3,(run (body idx (withArchive d)) m s).basis (1709+k.val)=false:=by
  have frame:=archive_result d row lim _ _ raw
  exact ⟨body_keeps idx (withArchive d) codePorts d row s m encoded_outside frame,popped d s m row frame⟩
end NativePack255
#print axioms NativePack255.receipt
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem outside_between {i q:Nat} (lo:i+16<q) (hi:q<1044) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
theorem outside_above {i q:Nat} (hi:1044+i≤q) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
theorem carry {i x p:Nat} (hi:i≤512) {s:State} (dom:Domain i x p s) : s.basis 1812=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p hi true s dom
  exact (link.2 _ (outside_above (by omega))).trans (stock_carry_end true x p i hi ref stage)
theorem future_history {i j x p:Nat} (h:i≤j) (hj:j<512) {s:State} (dom:Domain i x p s) :
    s.basis (base (1028+j))=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p (by omega) true s dom
  have lim:1044+i≤base (1028+j):=by change 1044+i≤1028+j+16;omega
  exact (link.2 _ (outside_above lim)).trans (stock_history true x p i ref stage j h hj)
theorem terminal (d:Bool) (x:Nat) (s:State) (dom:Domain 270 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 270 ref.basis ∧ EndTick.Reads s ref ∧
    s.basis (base (1028+270))=false ∧ s.basis (base (2053-270))=false ∧
    ∀q∈ParkEndpoint.dst,(pullState (OB5.sig 269) s).basis q=false := by
  obtain ⟨ref,stage,link⟩:=leaves_reference 270 x p (by decide) d s dom
  have bounds:∀q∈ParkEndpoint.dst,270+16<OB5.sig 269 q ∧ OB5.sig 269 q<1044:=by decide +kernel
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) dom,?_,?_⟩
  · exact (link.2 _ (outside_above (by decide))).trans ((Rolling1588.Integer.stage_zero d x 270 (by decide) _ stage).2 (by decide))
  · intro q hit
    exact (link.2 _ (outside_between (bounds _ hit).1 (bounds _ hit).2)).trans (ParkEndpoint.clear_dest d x p ref stage q hit)
#print axioms terminal
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
attribute [local irreducible] run routed unrouted renameProgram portal225 enter225 enter240 enter255 leave225 leave240 leave255
  portal225Inv enter225Inv enter240Inv enter255Inv leave225Inv leave240Inv leave255Inv park270 park270Inv portal270 portal270Inv
  archiveLoad240 archiveLoad255 archiveLoad270 archiveRestore240 archiveRestore255 archiveRestore270
theorem assembly (d:Bool) : forward45plus1 d =
    NativePack225.firstWindow d ++ leave225 ++ NativePack240.nextWindow d ++ leave240 ++ NativePack255.nextWindow d ++ leave255 ++ NativePack270.lastWindow d := by
  simp only [forward45plus1,NativePack225.firstWindow,NativePack240.nextWindow,NativePack255.nextWindow,NativePack270.lastWindow,
    NativePack225.window,NativePack240.window,NativePack255.window,NativePack270.endSlice,body,
    NativePack240.withArchive,NativePack255.withArchive, List.append_assoc]
  rfl
theorem unwind_assembly (d:Bool) : reverse45plus1 d =
    NativePack270.lastUnwind d ++ leave255Inv ++ NativePack255.nextUnwind d ++ leave240Inv ++ NativePack240.nextUnwind d ++ leave225Inv ++ NativePack225.firstUnwind d := by
  simp only [reverse45plus1,NativePack270.lastUnwind,NativePack255.nextUnwind,NativePack240.nextUnwind,NativePack225.firstUnwind,
    NativePack225.unwind,NativePack240.unwind,NativePack255.unwind,NativePack270.endUndo,unbody,
    NativePack240.fromArchive,NativePack255.fromArchive,List.append_assoc]
  rfl
#print axioms assembly
#print axioms unwind_assembly
end ECDSAAdd.Entrant.StairPacket.Partial


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run routed measurementCount body
namespace NativePack240
open ArchiveBoundary240
theorem real_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1716+k.val)=false:=by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,final⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem real_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1709+k.val)=false:=by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,final⟩
end NativePack255
#print axioms NativePack255.real_receipt
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270 ParkEndpoint Portal270Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
theorem empty_from_cut (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 n f u (pullState (OB5.sig 269) raw) (eraseSites src s))
    (source:∀q∈dst,(pullState (OB5.sig 269) raw).basis q=false) : ∀q∈dst,s.basis q=false:=by
  have regular:∀q∈dst,q∉src ∧ q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉RailPair.sites hiPairs:=by decide +kernel
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩:=regular _ member
  have eq:=cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source _ member)
theorem from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 270 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal d x raw domain
  exact last_window d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
#print axioms from_domain
end ECDSAAdd.Entrant.StairPacket.NativePack270


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StairArchiveRaw CodecBitSliceVerify
attribute [local irreducible] onRails run routed measurementCount body
def RowTruth (past:SkywalkNat.State) (g sg:Bool) (row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (encode g sg past.u past.v)).drop 5) (q.val/2)) q

theorem row_truth (j:Fin 23) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
    (row:Nat) (past:SkywalkNat.State) (g sg:Bool) (before out:State)
    (rec:physicalCells j before=SkywalkTrace.trace 15 (encode g sg past.u past.v))
    (bk:∀i:Fin 23,out.basis (ps ⟨i,by omega⟩)=before.basis (ps ⟨i,by omega⟩))
    (frame:Frame ps raw row out):RowTruth past g sg row:=by
  intro q
  let i:Fin 157:=⟨q,by omega⟩
  have eq:(rawCol q).testBit row=out.basis (ps i):=
    (congrArg (fun n:Nat=>n.testBit row) (io true true i).1).trans (frame i).symm
  have h:=native_raw_read j before q q.isLt
  change before.basis (nativeRawPort j q)=letterBit (read ((physicalCells j before).drop 5) (q.val/2)) q at h
  rw [rec] at h
  exact eq.trans ((bk ⟨q,by omega⟩).trans ((congrArg before.basis (chron q)).trans h))
namespace NativePack240
open ArchiveBoundary240
theorem matched_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1716+k.val)=false:=by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have matchRow:=row_truth sourceIdx rawPorts chronological row past pg ps s _ prior.records (bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1) frame
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem matched_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    ∃row<63145, RowTruth past pg ps row ∧ Kept codePorts d row out ∧ ∀k:Fin 3,out.basis (1709+k.val)=false:=by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have matchRow:=row_truth sourceIdx rawPorts chronological row past pg ps s _ prior.records (bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1) frame
  have final:=receipt d pre tape row limit frame
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨row,limit,matchRow,final⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 16000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
/-- Addresses outside the complete running A and B rails, current records, and
the carry and OB5 mirror bank. Historical packets remain observable here. -/
def Exterior (i top q:Nat):Prop :=
  ¬((i+15≤q ∧ q≤top) ∨ (786≤q ∧ q≤1042) ∨ (1556≤q ∧ q≤1812) ∨ (1044+i≤q ∧ q<1044+i+15))
instance (i top q:Nat) : Decidable (Exterior i top q):=by unfold Exterior;infer_instance
theorem raw_away {i top:Nat} (hpos:0 < i) (width:∀a:Fin 15,W.compactSkywalkTickPreWidth (i+a.val)≤257 ∧
    i+a.val+16+W.compactSkywalkTickPreWidth (i+a.val)≤top) {q:Wire} (clear:Exterior i top q):
    ∀a<15,¬RawRead (i+a) q:=by
  intro a ha hit
  obtain ⟨n1,n2⟩:=width ⟨a,ha⟩
  apply clear
  unfold RawRead at hit
  have pos:i+a≠0:=by omega
  simp only [skywalkPoolPreviousId,if_neg pos,base,Wire] at hit
  rcases hit with h|h|h|h|h <;> dsimp only at n1 n2 <;> omega
theorem exterior_origin {i top q:Nat} (lo:0 < i) (bound:i+15≤512)
    (width:∀a:Fin 15,W.compactSkywalkTickPreWidth (i+a.val)≤257 ∧ i+a.val+16+W.compactSkywalkTickPreWidth (i+a.val)≤top)
    (ext:Exterior i top q) (newMap:OB5.sig (i+14) q=q) (oldMap:OB5.sig (i-1) q=q)
    (raw history:State) (same:q∉sites i → history.basis q=(pullState (OB5.sig (i-1)) raw).basis q):
    history.basis q=(origin i raw history).basis q:=by
  by_cases h:q∈sites i
  · exact (inside i raw history q h).symm
  · rw [outside i raw history q h,newMap,span_unchanged i 15 q bound (raw_away lo width ext)]
    simpa only [pullState,oldMap] using same h
theorem ext_head (P:Program) (j:Fin 23) (Q:Program) (effects:List Wire) (s:State) (m n:List Bool) (q:Wire)
    (native:¬MayTouch j (windowNet j q)) (enter:q∉wires P) (admin:q∉effects) (cover:wires Q⊆effects.toFinset) :
    (run (body j Q) n (run P m s)).basis q=s.basis q:=
  (through_body j Q _ n q native (run_preserves_outside Q _ _ q (fun used=>admin (List.mem_toFinset.mp (cover used))))).trans
    (run_preserves_outside P _ _ q enter)
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (225+r.val)≤257 ∧
    225+r.val+16+W.compactSkywalkTickPreWidth (225+r.val)≤512:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 225 512 q) :
    (OB5.sig (225+14) q=q ∧ OB5.sig (225-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (225+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (225-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (225+14) q)
  rw [newid]
  change ¬((225+15≤q ∧ q≤225+14+16+161+2) ∨ (786≤q ∧ q≤787+161) ∨
    (1556≤q ∧ q≤1556+161) ∨ (1044+225≤q ∧ q<1044+225+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports225++[1723,1721,1722]++RailPair.sites Enter225.upperPairs++([]:List Wire),
    ¬Exterior 225 512 q:=by decide +kernel
theorem admin_set : ∀q∈support, ¬Exterior 225 512 q ∨ q∈sites 225:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long
      (pullState (OB5.sig 224) raw) s) (q:Wire) (ext:Exterior 225 512 q) :
    let history:=run (body idx (program d)) t (run Partial.enter225 m s)
    history.basis q=(origin 225 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports225++[1723,1721,1722]++RailPair.sites Enter225.upperPairs++([]:List Wire):=fun h=>local_set q h ext
  have noPort : q∉ports225:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter225.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter225 idx (program d) support s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter225.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (packs d)
  have old:=packed.unchanged q (fun eq:q=1723=>no (by simp [eq])) (fun eq:q=1721=>no (by simp [eq])) (fun eq:q=1722=>no (by simp [eq])) noHi
  exact stay.trans old
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack225


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (240+r.val)≤257 ∧
    240+r.val+16+W.compactSkywalkTickPreWidth (240+r.val)≤527:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 240 527 q) :
    (OB5.sig (240+14) q=q ∧ OB5.sig (240-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (240+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (240-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (240+14) q)
  rw [newid]
  change ¬((240+15≤q ∧ q≤240+14+16+153+2) ∨ (786≤q ∧ q≤787+153) ∨
    (1556≤q ∧ q≤1556+153) ∨ (1044+240≤q ∧ q<1044+240+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports240++[1715,1713,1714]++RailPair.sites Enter240.upperPairs++Enter240.pending,
    ¬Exterior 240 527 q:=by decide +kernel
theorem admin_set : ∀q∈(support++ArchiveBoundary240.rawPortsList), ¬Exterior 240 527 q ∨ q∈sites 240:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s)) (q:Wire) (ext:Exterior 240 527 q) :
    let history:=run (body idx (withArchive d)) t (run Partial.enter240 m s)
    history.basis q=(origin 240 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports240++[1715,1713,1714]++RailPair.sites Enter240.upperPairs++Enter240.pending:=fun h=>local_set q h ext
  have noPort : q∉ports240:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter240.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter240.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (admin_cover d)
  have old:=packed.unchanged q (fun eq:q=1715=>no (by simp [eq])) (fun eq:q=1713=>no (by simp [eq])) (fun eq:q=1714=>no (by simp [eq])) noHi
  have unmasked:q∉Enter240.pending:=fun hit=>no (by simp [hit])
  exact stay.trans (by simpa [eraseSites,unmasked] using old)
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack240


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body
theorem full_widths : ∀r:Fin 15,W.compactSkywalkTickPreWidth (255+r.val)≤257 ∧
    255+r.val+16+W.compactSkywalkTickPreWidth (255+r.val)≤529:=by decide +kernel
theorem placements (q:Nat) (ext:Exterior 255 529 q) :
    (OB5.sig (255+14) q=q ∧ OB5.sig (255-1) q=q) ∧ ¬MayTouch idx (windowNet idx q):=by
  unfold Exterior at ext
  have newid:OB5.sig (255+14) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  have oldid:OB5.sig (255-1) q=q:=by unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
  refine ⟨⟨newid,oldid⟩,?_⟩
  change ¬MayTouch idx (OB5.sig (255+14) q)
  rw [newid]
  change ¬((255+15≤q ∧ q≤255+14+16+146+2) ∨ (786≤q ∧ q≤787+146) ∨
    (1556≤q ∧ q≤1556+146) ∨ (1044+255≤q ∧ q<1044+255+15))
  simp only [Wire] at *
  omega
theorem local_set : ∀q∈ports255++[1708,1706,1707]++RailPair.sites Enter255.upperPairs++Enter255.pending,
    ¬Exterior 255 529 q:=by decide +kernel
theorem admin_set : ∀q∈(support++ArchiveBoundary255.rawPortsList), ¬Exterior 255 529 q ∨ q∈sites 255:=by decide +kernel
theorem agree_origin (d:Bool) (raw s:State) (m t:List Bool) (neg far long:Bool)
    (packed:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s)) (q:Wire) (ext:Exterior 255 529 q) :
    let history:=run (body idx (withArchive d)) t (run Partial.enter255 m s)
    history.basis q=(origin 255 raw history).basis q:=by
  have maps:=placements q ext
  apply exterior_origin (by decide) (by decide) full_widths ext maps.1.1 maps.1.2
  intro prev
  have no:q∉ports255++[1708,1706,1707]++RailPair.sites Enter255.upperPairs++Enter255.pending:=fun h=>local_set q h ext
  have noPort : q∉ports255:=fun hit=>no (by simp [hit])
  have noHi : q∉RailPair.sites Enter255.upperPairs:=fun hit=>no (by simp [hit])
  have stay:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s m t q maps.2
    (fun used=>noPort (List.mem_toFinset.mp (Enter255.programCover used)))
    (fun hit=>(admin_set q hit).elim (fun bad=>bad ext) prev) (admin_cover d)
  have old:=packed.unchanged q (fun eq:q=1708=>no (by simp [eq])) (fun eq:q=1706=>no (by simp [eq])) (fun eq:q=1707=>no (by simp [eq])) noHi
  have unmasked:q∉Enter255.pending:=fun hit=>no (by simp [hit])
  exact stay.trans (by simpa [eraseSites,unmasked] using old)
#print axioms agree_origin
end ECDSAAdd.Entrant.StairPacket.NativePack255


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
theorem matched_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (p ++ (program d ++ Partial.archiveLoad270 d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (Partial.archiveRestore270 d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) (Partial.archiveLoad270 d) (Partial.archiveRestore270 d)
    (reverse d) q s m (fun out=>∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Partial.archiveLoad270 d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem matched_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  matched_generic EndTick.physP EndTick.physQ d s m step past G S cross odd small prior
theorem matched_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount Partial.park270)
  let one:=run Partial.portal270Inv n (run Partial.park270 m s)
  let tape:=n.drop (measurementCount Partial.portal270Inv)
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 269) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 129 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick.physP tape one):=by rw [eqOne];exact tick
  have body:=matched_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem matched_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 270 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal d x raw domain
  exact matched_last d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack270


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 225 512 (target g))
private theorem maskleave225Part0 : leave225Part0.all writesInside=true:=by decide +kernel
private theorem maskleave225Part1 : leave225Part1.all writesInside=true:=by decide +kernel
private theorem maskleave225Part2 : leave225Part2.all writesInside=true:=by decide +kernel
private theorem maskleave225Part3 : leave225Part3.all writesInside=true:=by decide +kernel
private theorem maskleave225Part4 : leave225Part4.all writesInside=true:=by decide +kernel
private theorem maskleave225Part5 : leave225Part5.all writesInside=true:=by decide +kernel
private theorem maskleave225Part6 : leave225Part6.all writesInside=true:=by decide +kernel
private theorem maskleave225Part7 : leave225Part7.all writesInside=true:=by decide +kernel
private theorem maskleave225Part8 : leave225Part8.all writesInside=true:=by decide +kernel
private theorem maskleave225Part9 : leave225Part9.all writesInside=true:=by decide +kernel
private theorem maskleave225Part10 : leave225Part10.all writesInside=true:=by decide +kernel
private theorem maskleave225Part11 : leave225Part11.all writesInside=true:=by decide +kernel
private theorem maskleave225Part12 : leave225Part12.all writesInside=true:=by decide +kernel
private theorem maskleave225Part13 : leave225Part13.all writesInside=true:=by decide +kernel
private theorem maskleave225Part14 : leave225Part14.all writesInside=true:=by decide +kernel
private theorem maskleave225Part15 : leave225Part15.all writesInside=true:=by decide +kernel
private theorem maskleave225Part16 : leave225Part16.all writesInside=true:=by decide +kernel
private theorem maskleave225Part17 : leave225Part17.all writesInside=true:=by decide +kernel
private theorem maskleave225Part18 : leave225Part18.all writesInside=true:=by decide +kernel
private theorem maskleave225Part19 : leave225Part19.all writesInside=true:=by decide +kernel
private theorem maskleave225Part20 : leave225Part20.all writesInside=true:=by decide +kernel
private theorem maskleave225Part21 : leave225Part21.all writesInside=true:=by decide +kernel
private theorem maskleave225Part22 : leave225Part22.all writesInside=true:=by decide +kernel
private theorem maskleave225Part23 : leave225Part23.all writesInside=true:=by decide +kernel
private theorem maskleave225Part24 : leave225Part24.all writesInside=true:=by decide +kernel
private theorem maskleave225Part25 : leave225Part25.all writesInside=true:=by decide +kernel
private theorem maskleave225Part26 : leave225Part26.all writesInside=true:=by decide +kernel
private theorem maskleave225Part27 : leave225Part27.all writesInside=true:=by decide +kernel
private theorem maskleave225Part28 : leave225Part28.all writesInside=true:=by decide +kernel
private theorem maskleave225Part29 : leave225Part29.all writesInside=true:=by decide +kernel
private theorem maskleave225Part30 : leave225Part30.all writesInside=true:=by decide +kernel
private theorem maskleave225Part31 : leave225Part31.all writesInside=true:=by decide +kernel
private theorem maskleave225Part32 : leave225Part32.all writesInside=true:=by decide +kernel
private theorem maskleave225Part33 : leave225Part33.all writesInside=true:=by decide +kernel
theorem writes : leave225.all writesInside=true:=by
  simp only [leave225,List.all_append,maskleave225Part0,maskleave225Part1,maskleave225Part2,maskleave225Part3,maskleave225Part4,maskleave225Part5,maskleave225Part6,maskleave225Part7,maskleave225Part8,maskleave225Part9,maskleave225Part10,maskleave225Part11,maskleave225Part12,maskleave225Part13,maskleave225Part14,maskleave225Part15,maskleave225Part16,maskleave225Part17,maskleave225Part18,maskleave225Part19,maskleave225Part20,maskleave225Part21,maskleave225Part22,maskleave225Part23,maskleave225Part24,maskleave225Part25,maskleave225Part26,maskleave225Part27,maskleave225Part28,maskleave225Part29,maskleave225Part30,maskleave225Part31,maskleave225Part32,maskleave225Part33,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 225 512 q):
    (run leave225 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 225 512 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave225InvPart0 : leave225InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart1 : leave225InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart2 : leave225InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart3 : leave225InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart4 : leave225InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart5 : leave225InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart6 : leave225InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart7 : leave225InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart8 : leave225InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart9 : leave225InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart10 : leave225InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart11 : leave225InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart12 : leave225InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart13 : leave225InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart14 : leave225InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart15 : leave225InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart16 : leave225InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart17 : leave225InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart18 : leave225InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart19 : leave225InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart20 : leave225InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart21 : leave225InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart22 : leave225InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart23 : leave225InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart24 : leave225InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart25 : leave225InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart26 : leave225InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart27 : leave225InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart28 : leave225InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart29 : leave225InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart30 : leave225InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart31 : leave225InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart32 : leave225InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave225InvPart33 : leave225InvPart33.all writesInside=true:=by decide +kernel
theorem writesInv : leave225Inv.all writesInside=true:=by
  simp only [leave225Inv,List.all_append,maskleave225InvPart0,maskleave225InvPart1,maskleave225InvPart2,maskleave225InvPart3,maskleave225InvPart4,maskleave225InvPart5,maskleave225InvPart6,maskleave225InvPart7,maskleave225InvPart8,maskleave225InvPart9,maskleave225InvPart10,maskleave225InvPart11,maskleave225InvPart12,maskleave225InvPart13,maskleave225InvPart14,maskleave225InvPart15,maskleave225InvPart16,maskleave225InvPart17,maskleave225InvPart18,maskleave225InvPart19,maskleave225InvPart20,maskleave225InvPart21,maskleave225InvPart22,maskleave225InvPart23,maskleave225InvPart24,maskleave225InvPart25,maskleave225InvPart26,maskleave225InvPart27,maskleave225InvPart28,maskleave225InvPart29,maskleave225InvPart30,maskleave225InvPart31,maskleave225InvPart32,maskleave225InvPart33,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 225 512 q):
    (run leave225Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 225 512 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack225


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 240 527 (target g))
private theorem maskleave240Part0 : leave240Part0.all writesInside=true:=by decide +kernel
private theorem maskleave240Part1 : leave240Part1.all writesInside=true:=by decide +kernel
private theorem maskleave240Part2 : leave240Part2.all writesInside=true:=by decide +kernel
private theorem maskleave240Part3 : leave240Part3.all writesInside=true:=by decide +kernel
private theorem maskleave240Part4 : leave240Part4.all writesInside=true:=by decide +kernel
private theorem maskleave240Part5 : leave240Part5.all writesInside=true:=by decide +kernel
private theorem maskleave240Part6 : leave240Part6.all writesInside=true:=by decide +kernel
private theorem maskleave240Part7 : leave240Part7.all writesInside=true:=by decide +kernel
private theorem maskleave240Part8 : leave240Part8.all writesInside=true:=by decide +kernel
private theorem maskleave240Part9 : leave240Part9.all writesInside=true:=by decide +kernel
private theorem maskleave240Part10 : leave240Part10.all writesInside=true:=by decide +kernel
private theorem maskleave240Part11 : leave240Part11.all writesInside=true:=by decide +kernel
private theorem maskleave240Part12 : leave240Part12.all writesInside=true:=by decide +kernel
private theorem maskleave240Part13 : leave240Part13.all writesInside=true:=by decide +kernel
private theorem maskleave240Part14 : leave240Part14.all writesInside=true:=by decide +kernel
private theorem maskleave240Part15 : leave240Part15.all writesInside=true:=by decide +kernel
private theorem maskleave240Part16 : leave240Part16.all writesInside=true:=by decide +kernel
private theorem maskleave240Part17 : leave240Part17.all writesInside=true:=by decide +kernel
private theorem maskleave240Part18 : leave240Part18.all writesInside=true:=by decide +kernel
private theorem maskleave240Part19 : leave240Part19.all writesInside=true:=by decide +kernel
private theorem maskleave240Part20 : leave240Part20.all writesInside=true:=by decide +kernel
private theorem maskleave240Part21 : leave240Part21.all writesInside=true:=by decide +kernel
private theorem maskleave240Part22 : leave240Part22.all writesInside=true:=by decide +kernel
private theorem maskleave240Part23 : leave240Part23.all writesInside=true:=by decide +kernel
private theorem maskleave240Part24 : leave240Part24.all writesInside=true:=by decide +kernel
private theorem maskleave240Part25 : leave240Part25.all writesInside=true:=by decide +kernel
private theorem maskleave240Part26 : leave240Part26.all writesInside=true:=by decide +kernel
private theorem maskleave240Part27 : leave240Part27.all writesInside=true:=by decide +kernel
private theorem maskleave240Part28 : leave240Part28.all writesInside=true:=by decide +kernel
private theorem maskleave240Part29 : leave240Part29.all writesInside=true:=by decide +kernel
private theorem maskleave240Part30 : leave240Part30.all writesInside=true:=by decide +kernel
private theorem maskleave240Part31 : leave240Part31.all writesInside=true:=by decide +kernel
private theorem maskleave240Part32 : leave240Part32.all writesInside=true:=by decide +kernel
private theorem maskleave240Part33 : leave240Part33.all writesInside=true:=by decide +kernel
private theorem maskleave240Part34 : leave240Part34.all writesInside=true:=by decide +kernel
private theorem maskleave240Part35 : leave240Part35.all writesInside=true:=by decide +kernel
theorem writes : leave240.all writesInside=true:=by
  simp only [leave240,List.all_append,maskleave240Part0,maskleave240Part1,maskleave240Part2,maskleave240Part3,maskleave240Part4,maskleave240Part5,maskleave240Part6,maskleave240Part7,maskleave240Part8,maskleave240Part9,maskleave240Part10,maskleave240Part11,maskleave240Part12,maskleave240Part13,maskleave240Part14,maskleave240Part15,maskleave240Part16,maskleave240Part17,maskleave240Part18,maskleave240Part19,maskleave240Part20,maskleave240Part21,maskleave240Part22,maskleave240Part23,maskleave240Part24,maskleave240Part25,maskleave240Part26,maskleave240Part27,maskleave240Part28,maskleave240Part29,maskleave240Part30,maskleave240Part31,maskleave240Part32,maskleave240Part33,maskleave240Part34,maskleave240Part35,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 240 527 q):
    (run leave240 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 240 527 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave240InvPart0 : leave240InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart1 : leave240InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart2 : leave240InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart3 : leave240InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart4 : leave240InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart5 : leave240InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart6 : leave240InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart7 : leave240InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart8 : leave240InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart9 : leave240InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart10 : leave240InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart11 : leave240InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart12 : leave240InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart13 : leave240InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart14 : leave240InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart15 : leave240InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart16 : leave240InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart17 : leave240InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart18 : leave240InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart19 : leave240InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart20 : leave240InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart21 : leave240InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart22 : leave240InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart23 : leave240InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart24 : leave240InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart25 : leave240InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart26 : leave240InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart27 : leave240InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart28 : leave240InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart29 : leave240InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart30 : leave240InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart31 : leave240InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart32 : leave240InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart33 : leave240InvPart33.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart34 : leave240InvPart34.all writesInside=true:=by decide +kernel
private theorem maskleave240InvPart35 : leave240InvPart35.all writesInside=true:=by decide +kernel
theorem writesInv : leave240Inv.all writesInside=true:=by
  simp only [leave240Inv,List.all_append,maskleave240InvPart0,maskleave240InvPart1,maskleave240InvPart2,maskleave240InvPart3,maskleave240InvPart4,maskleave240InvPart5,maskleave240InvPart6,maskleave240InvPart7,maskleave240InvPart8,maskleave240InvPart9,maskleave240InvPart10,maskleave240InvPart11,maskleave240InvPart12,maskleave240InvPart13,maskleave240InvPart14,maskleave240InvPart15,maskleave240InvPart16,maskleave240InvPart17,maskleave240InvPart18,maskleave240InvPart19,maskleave240InvPart20,maskleave240InvPart21,maskleave240InvPart22,maskleave240InvPart23,maskleave240InvPart24,maskleave240InvPart25,maskleave240InvPart26,maskleave240InvPart27,maskleave240InvPart28,maskleave240InvPart29,maskleave240InvPart30,maskleave240InvPart31,maskleave240InvPart32,maskleave240InvPart33,maskleave240InvPart34,maskleave240InvPart35,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 240 527 q):
    (run leave240Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 240 527 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack240


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def writesInside (g:Instr) := decide (¬Exterior 255 529 (target g))
private theorem maskleave255Part0 : leave255Part0.all writesInside=true:=by decide +kernel
private theorem maskleave255Part1 : leave255Part1.all writesInside=true:=by decide +kernel
private theorem maskleave255Part2 : leave255Part2.all writesInside=true:=by decide +kernel
private theorem maskleave255Part3 : leave255Part3.all writesInside=true:=by decide +kernel
private theorem maskleave255Part4 : leave255Part4.all writesInside=true:=by decide +kernel
private theorem maskleave255Part5 : leave255Part5.all writesInside=true:=by decide +kernel
private theorem maskleave255Part6 : leave255Part6.all writesInside=true:=by decide +kernel
private theorem maskleave255Part7 : leave255Part7.all writesInside=true:=by decide +kernel
private theorem maskleave255Part8 : leave255Part8.all writesInside=true:=by decide +kernel
private theorem maskleave255Part9 : leave255Part9.all writesInside=true:=by decide +kernel
private theorem maskleave255Part10 : leave255Part10.all writesInside=true:=by decide +kernel
private theorem maskleave255Part11 : leave255Part11.all writesInside=true:=by decide +kernel
private theorem maskleave255Part12 : leave255Part12.all writesInside=true:=by decide +kernel
private theorem maskleave255Part13 : leave255Part13.all writesInside=true:=by decide +kernel
private theorem maskleave255Part14 : leave255Part14.all writesInside=true:=by decide +kernel
private theorem maskleave255Part15 : leave255Part15.all writesInside=true:=by decide +kernel
private theorem maskleave255Part16 : leave255Part16.all writesInside=true:=by decide +kernel
private theorem maskleave255Part17 : leave255Part17.all writesInside=true:=by decide +kernel
private theorem maskleave255Part18 : leave255Part18.all writesInside=true:=by decide +kernel
private theorem maskleave255Part19 : leave255Part19.all writesInside=true:=by decide +kernel
private theorem maskleave255Part20 : leave255Part20.all writesInside=true:=by decide +kernel
private theorem maskleave255Part21 : leave255Part21.all writesInside=true:=by decide +kernel
private theorem maskleave255Part22 : leave255Part22.all writesInside=true:=by decide +kernel
private theorem maskleave255Part23 : leave255Part23.all writesInside=true:=by decide +kernel
private theorem maskleave255Part24 : leave255Part24.all writesInside=true:=by decide +kernel
private theorem maskleave255Part25 : leave255Part25.all writesInside=true:=by decide +kernel
private theorem maskleave255Part26 : leave255Part26.all writesInside=true:=by decide +kernel
private theorem maskleave255Part27 : leave255Part27.all writesInside=true:=by decide +kernel
private theorem maskleave255Part28 : leave255Part28.all writesInside=true:=by decide +kernel
private theorem maskleave255Part29 : leave255Part29.all writesInside=true:=by decide +kernel
private theorem maskleave255Part30 : leave255Part30.all writesInside=true:=by decide +kernel
private theorem maskleave255Part31 : leave255Part31.all writesInside=true:=by decide +kernel
private theorem maskleave255Part32 : leave255Part32.all writesInside=true:=by decide +kernel
private theorem maskleave255Part33 : leave255Part33.all writesInside=true:=by decide +kernel
private theorem maskleave255Part34 : leave255Part34.all writesInside=true:=by decide +kernel
private theorem maskleave255Part35 : leave255Part35.all writesInside=true:=by decide +kernel
private theorem maskleave255Part36 : leave255Part36.all writesInside=true:=by decide +kernel
theorem writes : leave255.all writesInside=true:=by
  simp only [leave255,List.all_append,maskleave255Part0,maskleave255Part1,maskleave255Part2,maskleave255Part3,maskleave255Part4,maskleave255Part5,maskleave255Part6,maskleave255Part7,maskleave255Part8,maskleave255Part9,maskleave255Part10,maskleave255Part11,maskleave255Part12,maskleave255Part13,maskleave255Part14,maskleave255Part15,maskleave255Part16,maskleave255Part17,maskleave255Part18,maskleave255Part19,maskleave255Part20,maskleave255Part21,maskleave255Part22,maskleave255Part23,maskleave255Part24,maskleave255Part25,maskleave255Part26,maskleave255Part27,maskleave255Part28,maskleave255Part29,maskleave255Part30,maskleave255Part31,maskleave255Part32,maskleave255Part33,maskleave255Part34,maskleave255Part35,maskleave255Part36,Bool.and_self]
theorem exterior (s:State) (m:List Bool) (q:Wire) (ext:Exterior 255 529 q):
    (run leave255 m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 255 529 (target g):=of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)
private theorem maskleave255InvPart0 : leave255InvPart0.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart1 : leave255InvPart1.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart2 : leave255InvPart2.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart3 : leave255InvPart3.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart4 : leave255InvPart4.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart5 : leave255InvPart5.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart6 : leave255InvPart6.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart7 : leave255InvPart7.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart8 : leave255InvPart8.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart9 : leave255InvPart9.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart10 : leave255InvPart10.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart11 : leave255InvPart11.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart12 : leave255InvPart12.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart13 : leave255InvPart13.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart14 : leave255InvPart14.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart15 : leave255InvPart15.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart16 : leave255InvPart16.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart17 : leave255InvPart17.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart18 : leave255InvPart18.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart19 : leave255InvPart19.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart20 : leave255InvPart20.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart21 : leave255InvPart21.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart22 : leave255InvPart22.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart23 : leave255InvPart23.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart24 : leave255InvPart24.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart25 : leave255InvPart25.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart26 : leave255InvPart26.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart27 : leave255InvPart27.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart28 : leave255InvPart28.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart29 : leave255InvPart29.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart30 : leave255InvPart30.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart31 : leave255InvPart31.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart32 : leave255InvPart32.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart33 : leave255InvPart33.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart34 : leave255InvPart34.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart35 : leave255InvPart35.all writesInside=true:=by decide +kernel
private theorem maskleave255InvPart36 : leave255InvPart36.all writesInside=true:=by decide +kernel
theorem writesInv : leave255Inv.all writesInside=true:=by
  simp only [leave255Inv,List.all_append,maskleave255InvPart0,maskleave255InvPart1,maskleave255InvPart2,maskleave255InvPart3,maskleave255InvPart4,maskleave255InvPart5,maskleave255InvPart6,maskleave255InvPart7,maskleave255InvPart8,maskleave255InvPart9,maskleave255InvPart10,maskleave255InvPart11,maskleave255InvPart12,maskleave255InvPart13,maskleave255InvPart14,maskleave255InvPart15,maskleave255InvPart16,maskleave255InvPart17,maskleave255InvPart18,maskleave255InvPart19,maskleave255InvPart20,maskleave255InvPart21,maskleave255InvPart22,maskleave255InvPart23,maskleave255InvPart24,maskleave255InvPart25,maskleave255InvPart26,maskleave255InvPart27,maskleave255InvPart28,maskleave255InvPart29,maskleave255InvPart30,maskleave255InvPart31,maskleave255InvPart32,maskleave255InvPart33,maskleave255InvPart34,maskleave255InvPart35,maskleave255InvPart36,Bool.and_self]
theorem exteriorInv (s:State) (m:List Bool) (q:Wire) (ext:Exterior 255 529 q):
    (run leave255Inv m s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have clean:¬Exterior 255 529 (target g):=of_decide_eq_true (List.all_eq_true.mp writesInv g hit)
  exact clean (eq.symm ▸ ext)
#print axioms exteriorInv
end ECDSAAdd.Entrant.StairPacket.NativePack255


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Word Leave225Join Leave225Close
theorem untouchedHigh (q:Nat) (h:419≤q ∧ q≤512) : q∉Leave225StoreMapped.program.map destination := by
  have all:Leave225StoreMapped.program.all (fun g=>decide (destination g<419 ∨ 512<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) (top:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    ∀i:Fin 102,(run Leave225StoreMapped.program m s).basis (411+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  have front:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 112,97 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave225Hit.swaps i):=by decide +kernel
  have used:=Leave225Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave225EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave225EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave225RoutedRestore.result z sg a n (n.drop (measurementCount Leave225Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=411+i.val
  by_cases ext:419≤q
  · have hi:q≤512 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave225StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<8 := by dsimp [q] at ext;omega
    let j:Fin 8:=⟨i.val,lim⟩
    have geom:∀j:Fin 8,let q:Nat:=411+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave225FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave225HighZero


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Word Leave240Join Leave240Close
theorem untouchedHigh (q:Nat) (h:426≤q ∧ q≤527) : q∉Leave240StoreMapped.program.map destination := by
  have all:Leave240StoreMapped.program.all (fun g=>decide (destination g<426 ∨ 527<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) (top:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    ∀i:Fin 109,(run Leave240StoreMapped.program m s).basis (419+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave240RoutedRestore.result z sg a n (n.drop (measurementCount Leave240Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=419+i.val
  by_cases ext:426≤q
  · have hi:q≤527 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave240StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<7 := by dsimp [q] at ext;omega
    let j:Fin 7:=⟨i.val,lim⟩
    have geom:∀j:Fin 7,let q:Nat:=419+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave240FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave240HighZero


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Word Leave255Join Leave255Close
theorem untouchedHigh (q:Nat) (h:434≤q ∧ q≤528) : q∉Leave255StoreMapped.program.map destination := by
  have all:Leave255StoreMapped.program.all (fun g=>decide (destination g<434 ∨ 528<destination g))=true:=by decide +kernel
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) (top:∀q:Nat,434≤q → q≤528 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    ∀i:Fin 103,(run Leave255StoreMapped.program m s).basis (426+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave255RoutedRestore.result z sg a n (n.drop (measurementCount Leave255Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=426+i.val
  by_cases ext:434≤q
  · have hi:q≤528 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave255StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<8 := by dsimp [q] at ext;omega
    let j:Fin 8:=⟨i.val,lim⟩
    have geom:∀j:Fin 8,let q:Nat:=426+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by decide +kernel
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave255FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave255HighZero


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body
namespace NativePack225
def tailTemps := List.range' 1724 89
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉support ∧ q∉ports225 ∧
    OB5.sig 224 q=q ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ q∉RailPair.sites Enter225.upperPairs ∧ q∉([]:List Wire):=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 225).carry:=by
  have range:(W.compactSkywalkTickLayout base 225).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long (pullState (OB5.sig 224) raw) s)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (program d)) b (run Partial.enter225 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter225 idx (program d) support s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter225.programCover used))) away (packs d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack225
namespace NativePack240
def tailTemps := List.range' 1719 94
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary240.rawPortsList) ∧ q∉ports240 ∧
    OB5.sig 239 q=q ∧ q≠1715 ∧ q≠1713 ∧ q≠1714 ∧ q∉RailPair.sites Enter240.upperPairs ∧ q∉Enter240.pending:=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 240).carry:=by
  have range:(W.compactSkywalkTickLayout base 240).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (withArchive d)) b (run Partial.enter240 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter240.programCover used))) away (admin_cover d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg mask] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack240
namespace NativePack255
def tailTemps := List.range' 1712 88
theorem tail_routing:∀q∈tailTemps,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧ q∉ports255 ∧
    OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ q∉RailPair.sites Enter255.upperPairs ∧ q∉Enter255.pending:=by decide +kernel
theorem tail_inputs:∀q∈tailTemps,q=1812 ∨ q∈(W.compactSkywalkTickLayout base 255).carry:=by
  have range:(W.compactSkywalkTickLayout base 255).carry=List.range' 1556 256:=by decide +kernel
  rw [range];intro q seen;have b:=List.mem_range'_1.mp seen;rw [List.mem_range'_1]
  simp only [Wire] at *;omega
theorem tail_clean (d:Bool) (raw s:State) (a b:List Bool) (neg far long G:Bool) (A B:Int)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) A B G raw.basis) (endBit:raw.basis 1812=false) :
    ∀q∈tailTemps,(run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=false:=by
  intro q hit
  obtain ⟨live,away,head,same,hn,hf,hu,hi,mask⟩:=tail_routing q hit
  have stay:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q live
    (fun used=>head (List.mem_toFinset.mp (Enter255.programCover used))) away (admin_cover d)
  have read:=cut.unchanged q hn hf hu hi
  have canon:s.basis q=raw.basis q:=by simpa only [pullState,same,eraseSites,if_neg mask] using read
  rcases tail_inputs q hit with rfl|carry
  · exact stay.trans (canon.trans endBit)
  · exact stay.trans (canon.trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ carry))
end NativePack255
#print axioms NativePack255.tail_clean
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem full_carry (i n x p:Nat) (lim:i+n≤512) (good:Bounds x p) (raw:State) (domain:Domain i x p raw)
    (m:List Bool) (q:Nat) (low:1556≤q) (high:q≤1812) :
    (run (span i n) m raw).basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  have finish:=full_span i n x p lim good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have fields:=(W.compactSkywalkStage_fields_iff base _ (i+n) lim base_pool_nodup _).mp finish
  have outside:=outside_above (q:=q) (i:=i) (by omega)
  have link:=fixed_span i i n (Nat.le_refl _) lim raw ref m match'
  apply (link.2 q outside).trans
  apply (regValue_zero _ _).mp fields.2.2.2.2.2.1
  exact List.mem_map.mpr ⟨q-16,List.mem_range'_1.mpr (by omega),by change (q-16)+16=q;omega⟩
theorem carry_origin {i upper x p:Nat} (limit:i+15≤512) (upper_ok:upper≤1812) (good:Bounds x p) (raw history:State)
    (domain:Domain i x p raw)
    (fixed:∀q:Nat,1556≤q → q≤upper → OB5.sig (i+14) q=q)
    (q:Nat) (low:1556≤q) (high:q≤upper) : (origin i raw history).basis q=false:=by
  have clear:q∉sites i:=by
    intro hit
    obtain ⟨r,hr,eq⟩:=List.mem_flatMap.mp hit
    have bound:=List.mem_range'_1.mp hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,base,Wire] at eq
    unfold oldStart oldCount at bound
    split at bound <;> rcases eq with h|h <;> omega
  rw [outside i raw history q clear,fixed _ low high]
  exact full_carry i 15 x p limit good raw domain [] q low (Nat.le_trans high upper_ok)
theorem same_c225 (q:Nat) (lo:1556≤q) (hi:q≤1812):OB5.sig (225+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
theorem same_c240 (q:Nat) (lo:1556≤q) (hi:q≤1812):OB5.sig (240+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
theorem same_c255 (q:Nat) (lo:1556≤q) (hi:q≤1799):OB5.sig (255+14) q=q:=by
  unfold OB5.sig;rw [if_neg (by simp only [Wire];omega)]
#print axioms carry_origin
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
theorem incoming_free_A (i x p:Nat) (lim:i≤512) (raw:State) (domain:Domain i x p raw)
    (q:Nat) (lower:i+16<q) (upper:q<1044)
    (free:q∈(W.compactSkywalkSignPoolA base i).released ∨ (i+274≤q ∧ q<786)) :
    raw.basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  apply (match'.2 _ (outside_between lower upper)).trans
  rcases free with sign|later
  · exact stage.2.1 q sign
  · let j:=q-274
    have hj:i≤j ∧ j<512:=by dsimp [j];omega
    have eq:q=base (j+258):=by change q=j+258+16;dsimp [j];omega
    rw [eq]
    exact ((W.compactSkywalkStage_fields_iff base _ i lim base_pool_nodup _).mp stage).2.2.2.2.1 j hj.1 hj.2 |>.1
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave225Word

def zeros := (List.range' 1556 157)++(List.range' 1719 94)
def retired (q:Wire):Prop:=
  q=1722 ∨ (q≠1722 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave225CoreCheckpoint.targets ∧ q∉smallM)))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave225FullArithmetic.program=Leave225CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) (quiet:∀q∈Leave225CoreCheckpoint.rawSites,s.basis q=false) :
    ∀q∈zeros,(run leave225 m s).basis q=false := by
  let c:=run Leave225CoreCheckpoint.program m s
  have h:=Leave225CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave225CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave225CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave225CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave225CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave225CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave225CoreCheckpoint.targets) (notM:q∉smallM):(run Leave225FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave225StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave225BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ origin.1 origin.2)
end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave240Word

def zeros := (List.range' 1556 150)++(List.range' 1712 101)
def retired (q:Wire):Prop:=
  q=1714 ∨ (q≠1714 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave240CoreCheckpoint.targets ∧ q∉smallM)))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave240FullArithmetic.program=Leave240CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) (quiet:∀q∈Leave240CoreCheckpoint.rawSites,s.basis q=false) :
    ∀q∈zeros,(run leave240 m s).basis q=false := by
  let c:=run Leave240CoreCheckpoint.program m s
  have h:=Leave240CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave240CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave240CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave240CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave240CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave240CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave240CoreCheckpoint.targets) (notM:q∉smallM):(run Leave240FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave240StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave240BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ origin.1 origin.2)
end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave255Word

def zeros := (List.range' 1556 142)++(List.range' 1704 96)++List.range' 1029 14
def retired (q:Wire):Prop:=
  q=1707 ∨ (q≠1707 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave255CoreCheckpoint.targets ∧ q∉smallM) ∨ (∃i:Fin 14,q=live (113+i.val))))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by decide +kernel
theorem restoreShape : Leave255FullArithmetic.program=Leave255CoreCheckpoint.program++restore := by decide +kernel
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) (quiet:∀q∈Leave255CoreCheckpoint.rawSites,s.basis q=false) (narrow:Leave255TrueMiddle.F z<2^113) :
    ∀q∈zeros,(run leave255 m s).basis q=false := by
  let c:=run Leave255CoreCheckpoint.program m s
  have h:=Leave255CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave255CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave255CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by decide +kernel : ∀q∈smallC,q∈Leave255CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by decide +kernel : ∀q∈smallM,q∈Leave255CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave255CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave255CoreCheckpoint.targets) (notM:q∉smallM):(run Leave255FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave255StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave255BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  intro q hq
  rw [whole.2.2.2.2]
  rcases routed q hq with eq|⟨diff,out,hist,src⟩
  · rw [eq];simp [writeBit]
  simp only [writeBit,Function.update_of_ne diff]
  rw [store _ out hist]
  rcases src with eq|⟨x,y,z,origin⟩
  · rw [eq];exact flags.2.1
  · rcases origin with ⟨mem,notM⟩|⟨i,eq⟩
    · exact (flags.2.2.2.2.2.2 _ x y z).trans (coreDone _ mem notM)
    · rw [eq,flags.2.2.2.2.2.1 _ (by have h:=i.isLt;omega)]
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le narrow (Nat.pow_le_pow_right (by decide) (by omega))
end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin
open Arithmetic MappedCompressed WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000

def releasedSite (q:Nat) := q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313)
instance (q:Nat):Decidable (releasedSite q) := by unfold releasedSite;infer_instance

theorem released (x p:Nat) (good:Bounds x p) (raw history:State) (dom:Domain 255 x p raw) (q:Nat)
    (site:q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313)) :
    (origin 255 raw history).basis q=false := by
  have off:∀i:Fin 1314,releasedSite i.val →
      i.val∉sites 255 := by decide +kernel
  have bound:q<1314:=by omega
  rw [outside _ _ _ _ (off ⟨q,bound⟩ site)]
  by_cases mirror:1301≤q ∧ q≤1313
  · have map:OB5.sig 269 q=3113-q:=by simp [OB5.sig,mirror.1,show q≤1044+269 by omega]
    rw [show 255+14=269 by decide,map]
    exact full_carry 255 15 x p (by decide) good raw dom [] _ (by omega) (by omega)
  have small:q=529 ∨ (1029≤q ∧ q≤1042):=by tauto
  have ident:OB5.sig (255+14) q=q:=by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
  rw [ident]
  obtain ⟨reference,same,stage⟩:=dom
  have finish:=full_span 255 15 x p (by decide) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime reference [] stage
  have offHist:¬Earlier 255 q:=outside_between (by omega) (by omega)
  have link:=fixed_span 255 255 15 (Nat.le_refl _) (by decide) raw reference [] same
  apply (link.2 q offHist).trans
  rcases small with rfl|⟨lo,hi⟩
  · exact finish.2.1 _ (by decide +kernel)
  · have members : ∀i∈List.range' 1029 14,i∈(W.compactSkywalkSignPoolB base 270).released := by decide +kernel
    exact finish.2.2 q (members _ (List.mem_range'_1.mpr ⟨lo,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run body
namespace NativePack225
def upperA:=List.range' 419 94
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉support ∧ q∉ports225 ∧ q∉([]:List Wire) ∧
    OB5.sig 224 q=q ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ 225+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter225.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter225.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 225).released ∨ (225+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 225 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long (pullState (OB5.sig 224) raw) s)
    (q:Nat) (low:419≤q) (high:q≤512) :
    (run (body idx (program d)) b (run Partial.enter225 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter225 idx (program d) support s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter225.programCover h))) adminOff (packs d)
  apply normal.trans
  have clean:(s).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 225 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  exact clean
end NativePack225
namespace NativePack240
def upperA:=List.range' 426 102
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary240.rawPortsList) ∧ q∉ports240 ∧ q∉Enter240.pending ∧
    OB5.sig 239 q=q ∧ q≠1715 ∧ q≠1713 ∧ q≠1714 ∧ 240+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter240.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter240.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 240).released ∨ (240+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 240 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (q:Nat) (low:426≤q) (high:q≤527) :
    (run (body idx (withArchive d)) b (run Partial.enter240 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter240 idx (withArchive d) (support++ArchiveBoundary240.rawPortsList) s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter240.programCover h))) adminOff (admin_cover d)
  apply normal.trans
  have clean:((eraseSites Enter240.pending s)).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 240 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  simpa [eraseSites,mask] using clean
end NativePack240
namespace NativePack255
def upperA:=List.range' 434 96
theorem upper_layout:∀q∈upperA,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧ q∉ports255 ∧ q∉Enter255.pending ∧
    OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ 255+16<q ∧ q<1044:=by decide +kernel
theorem upper_sources:∀q∈upperA,q∈Enter255.upperPairs.map Prod.fst ∨
    (q∉RailPair.sites Enter255.upperPairs ∧ (q∈(W.compactSkywalkSignPoolA base 255).released ∨ (255+274≤q ∧ q<786))):=by decide +kernel
theorem upper_clear (d:Bool) (raw s:State) (x p:Nat) (domain:Domain 255 x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (q:Nat) (low:434≤q) (high:q≤529) :
    (run (body idx (withArchive d)) b (run Partial.enter255 a s)).basis q=false:=by
  have seen:q∈upperA:=List.mem_range'_1.mpr ⟨low,Nat.lt_succ_of_le high⟩
  obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,lower,upper⟩:=upper_layout q seen
  have normal:=ext_head Partial.enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q off
    (fun h=>enterOff (List.mem_toFinset.mp (Enter255.programCover h))) adminOff (admin_cover d)
  apply normal.trans
  have clean:((eraseSites Enter255.pending s)).basis q=false:=by
    rcases upper_sources q seen with old|⟨away,fresh⟩
    · obtain ⟨pair,hp,rfl⟩:=List.mem_map.mp old
      exact (cut.upper _ hp).1
    · have cleared:=incoming_free_A 255 x p (by decide) raw domain q lower upper fresh
      exact (cut.unchanged q hn hf hu away).trans (by simpa only [pullState,source] using cleared)
  simpa [eraseSites,mask] using clean
end NativePack255
#print axioms NativePack225.upper_clear
#print axioms NativePack240.upper_clear
#print axioms NativePack255.upper_clear
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 144) (s:State) (m:List Bool) :
    let v:=run leave225 m s
    v.basis (256+i.val)=s.basis (256+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave225.all (fun g=>decide ((destination g<256 ∨ 400≤destination g) ∧ (destination g<786 ∨ 930≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(256≤q ∧ q<400) ∨ (786≤q ∧ q<930)):q∉leave225.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 144 15 z → chain (decide (2^144≤z.u)) xs)
    (first:Shadow.far 144 15 z → decide (2^144≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave225Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u)))
    (highZero:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave225WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 239) raw
    let out:=run leave225 m s
    (∀i:Fin 155,out.basis (256+i.val)=o.basis (256+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 102,out.basis (411+i.val)=false ∧
      out.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let o:=pullState (OB5.sig 239) raw
  let out:=run leave225 m s
  have word:=Leave225EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave225HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 255=G := by
    have geo:Leave225WideWords.L.previous=OB5.sig 239 255:=by decide +kernel
    change raw.basis (OB5.sig 239 255)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 144 z small sg
  constructor
  · intro i
    have fit:i.val<257:=by have h:=i.isLt;omega
    have ref:=Leave225WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<144
    · have hw:=Leave225WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 144 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 144 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 11:=⟨i.val-144,by have h:=i.isLt;omega⟩
      have eq:144+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (400:Nat)+j.val=256+i.val by omega,show (930:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 257:=⟨155+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave225WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 256+(155+i.val)=411+i.val by omega,show 786+(155+i.val)=941+i.val by omega] at ref
    have free:(run leave225 m s).basis (411+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (411:Nat)+i.val≠1722;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 136) (s:State) (m:List Bool) :
    let v:=run leave240 m s
    v.basis (271+i.val)=s.basis (271+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave240.all (fun g=>decide ((destination g<271 ∨ 407≤destination g) ∧ (destination g<786 ∨ 922≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(271≤q ∧ q<407) ∨ (786≤q ∧ q<922)):q∉leave240.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 136 15 z → chain (decide (2^136≤z.u)) xs)
    (first:Shadow.far 136 15 z → decide (2^136≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave240Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u)))
    (highZero:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave240WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 254) raw
    let out:=run leave240 m s
    (∀i:Fin 148,out.basis (271+i.val)=o.basis (271+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 109,out.basis (419+i.val)=false ∧
      out.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let o:=pullState (OB5.sig 254) raw
  let out:=run leave240 m s
  have word:=Leave240EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave240HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 270=G := by
    have geo:Leave240WideWords.L.previous=OB5.sig 254 270:=by decide +kernel
    change raw.basis (OB5.sig 254 270)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 136 z small sg
  constructor
  · intro i
    have fit:i.val<257:=by have h:=i.isLt;omega
    have ref:=Leave240WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<136
    · have hw:=Leave240WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 136 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 136 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 12:=⟨i.val-136,by have h:=i.isLt;omega⟩
      have eq:136+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (407:Nat)+j.val=271+i.val by omega,show (922:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 257:=⟨148+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave240WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 271+(148+i.val)=419+i.val by omega,show 786+(148+i.val)=934+i.val by omega] at ref
    have free:(run leave240 m s).basis (419+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (419:Nat)+i.val≠1714;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 129) (s:State) (m:List Bool) :
    let v:=run leave255 m s
    v.basis (286+i.val)=s.basis (286+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave255.all (fun g=>decide ((destination g<286 ∨ 415≤destination g) ∧ (destination g<786 ∨ 915≤destination g)))=true := by decide +kernel
  have safe (q:Nat) (inside:(286≤q ∧ q<415) ∨ (786≤q ∧ q<915)):q∉leave255.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 129 15 z → chain (decide (2^129≤z.u)) xs)
    (first:Shadow.far 129 15 z → decide (2^129≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave255Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u)))
    (highZero:∀q:Nat,434≤q → q≤528 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave255WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 269) raw
    let out:=run leave255 m s
    (∀i:Fin 140,out.basis (286+i.val)=o.basis (286+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 103,out.basis (426+i.val)=false ∧
      out.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let o:=pullState (OB5.sig 269) raw
  let out:=run leave255 m s
  have word:=Leave255EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave255HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 285=G := by
    have geo:Leave255WideWords.L.previous=OB5.sig 269 285:=by decide +kernel
    change raw.basis (OB5.sig 269 285)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 129 z small sg
  constructor
  · intro i
    have fit:i.val<243:=by have h:=i.isLt;omega
    have ref:=Leave255WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<129
    · have hw:=Leave255WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 129 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 129 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 11:=⟨i.val-129,by have h:=i.isLt;omega⟩
      have eq:129+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (415:Nat)+j.val=286+i.val by omega,show (915:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 243:=⟨140+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave255WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 286+(140+i.val)=426+i.val by omega,show 786+(140+i.val)=926+i.val by omega] at ref
    have free:(run leave255 m s).basis (426+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (426:Nat)+i.val≠1707;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112)
    (far:s.basis 1721=decide (Shadow.far 144 15 z))
    (side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 10) 0 15 (mappedBasis 10 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave225 m s
    let cells:=readCells (shape 10) 0 15 (mappedBasis 10 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1716=decide (Shadow.far 144 15 z) ∧
      out.basis 1717=(decide (Shadow.far 144 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1718=(decide (Shadow.far 144 15 z) && HighBankSum.cross (Leave225TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave225RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave225Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave225EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave225PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 144 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (240≤q ∧ q<256) ∨ (1269≤q ∧ q<1284)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1715=neg) (mode : s.basis 1713=far) (side : s.basis 1714=long)
    (low : ∀i:Fin 155, s.basis (256+i.val)=o.basis (256+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 102, s.basis (411+i.val)=false ∧
      s.basis (941+i.val)=(if o.basis 255 then o.basis (941+i.val) else o.basis (411+i.val)))
    (ext : ∀q,Exterior 225 512 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave225BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1812 → o.basis q=false) :
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long o (eraseSites Enter240.pending s) := by
  have loShape : Enter240.lowerPairs=(List.finRange 3).map (fun j=>(256+(152+j.val),786+(152+j.val))) := by decide +kernel
  have hiShape : Enter240.upperPairs=(List.finRange 102).map (fun j=>(411+j.val,941+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites Enter240.pending s).basis q=s.basis q := by
    have no:q∉Enter240.pending:=by simp [Enter240.pending,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,Enter240.pending] using sign
  · simpa [eraseSites,Enter240.pending] using mode
  · simpa [eraseSites,Enter240.pending] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (256+(152+j.val)) (by change 256+(152+j.val)<1556;omega),away (786+(152+j.val)) (by change 786+(152+j.val)<1556;omega)]
    exact low ⟨152+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (411+j.val) (by change 411+j.val<1556;omega),away (941+j.val) (by change 941+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈Enter240.pending
    · have range : ∀q∈Enter240.pending,1556≤q ∧ q≤1812 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 225 512 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 102) : 411+i.val∈sites Enter240.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 102,411+i.val∈sites Enter240.upperPairs) i
    have hiB (i:Fin 102) : 941+i.val∈sites Enter240.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 102,941+i.val∈sites Enter240.upperPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Enter240.upperPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:256≤q ∧ q<411
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 256 155 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<941
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 155 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1812 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave225BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [Enter240.pending,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120)
    (far:s.basis 1713=decide (Shadow.far 136 15 z))
    (side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 11) 0 15 (mappedBasis 11 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave240 m s
    let cells:=readCells (shape 11) 0 15 (mappedBasis 11 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1709=decide (Shadow.far 136 15 z) ∧
      out.basis 1710=(decide (Shadow.far 136 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1711=(decide (Shadow.far 136 15 z) && HighBankSum.cross (Leave240TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave240RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave240Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave240EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave240PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 136 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (255≤q ∧ q<271) ∨ (1284≤q ∧ q<1299)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1708=neg) (mode : s.basis 1706=far) (side : s.basis 1707=long)
    (low : ∀i:Fin 148, s.basis (271+i.val)=o.basis (271+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 109, s.basis (419+i.val)=false ∧
      s.basis (934+i.val)=(if o.basis 270 then o.basis (934+i.val) else o.basis (419+i.val)))
    (ext : ∀q,Exterior 240 527 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave240BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1812 → o.basis q=false) :
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long o (eraseSites Enter255.pending s) := by
  have loShape : Enter255.lowerPairs=(List.finRange 3).map (fun j=>(271+(145+j.val),786+(145+j.val))) := by decide +kernel
  have hiShape : Enter255.upperPairs=(List.finRange 109).map (fun j=>(419+j.val,934+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites Enter255.pending s).basis q=s.basis q := by
    have no:q∉Enter255.pending:=by simp [Enter255.pending,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,Enter255.pending] using sign
  · simpa [eraseSites,Enter255.pending] using mode
  · simpa [eraseSites,Enter255.pending] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (271+(145+j.val)) (by change 271+(145+j.val)<1556;omega),away (786+(145+j.val)) (by change 786+(145+j.val)<1556;omega)]
    exact low ⟨145+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (419+j.val) (by change 419+j.val<1556;omega),away (934+j.val) (by change 934+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈Enter255.pending
    · have range : ∀q∈Enter255.pending,1556≤q ∧ q≤1812 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 240 527 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 109) : 419+i.val∈sites Enter255.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 109,419+i.val∈sites Enter255.upperPairs) i
    have hiB (i:Fin 109) : 934+i.val∈sites Enter255.upperPairs := by
      exact (by decide +kernel : ∀i:Fin 109,934+i.val∈sites Enter255.upperPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Enter255.upperPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:271≤q ∧ q<419
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 271 148 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<934
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 148 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1812 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave240BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [Enter255.pending,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127)
    (far:s.basis 1706=decide (Shadow.far 129 15 z))
    (side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 12) 0 15 (mappedBasis 12 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave255 m s
    let cells:=readCells (shape 12) 0 15 (mappedBasis 12 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave255RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave255Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave255EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave255PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 129 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (270≤q ∧ q<286) ∨ (1299≤q ∧ q<1314) ∨ q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1800≤q ∧ q≤1812)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1700=neg) (mode : s.basis 1698=far) (side : s.basis 1699=long)
    (low : ∀i:Fin 140, s.basis (286+i.val)=o.basis (286+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 103, s.basis (426+i.val)=false ∧
      s.basis (926+i.val)=(if o.basis 285 then o.basis (926+i.val) else o.basis (426+i.val)))
    (ext : ∀q,Exterior 255 529 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave255BoundaryClean.zeros,s.basis q=false)
    (carry : ∀q:Wire,1556≤q → q≤1799 → o.basis q=false) :
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 neg far long o (eraseSites ParkEndpoint.src s) := by
  have loShape : Portal270Flag.loPairs=(List.finRange 3).map (fun j=>(286+(137+j.val),786+(137+j.val))) := by decide +kernel
  have hiShape : Portal270Flag.hiPairs=(List.finRange 103).map (fun j=>(426+j.val,926+j.val)) := by decide +kernel
  have away (q:Wire) (small:q<1556) : (eraseSites ParkEndpoint.src s).basis q=s.basis q := by
    have no:q∉ParkEndpoint.src:=by simp [ParkEndpoint.src,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,ParkEndpoint.src] using sign
  · simpa [eraseSites,ParkEndpoint.src] using mode
  · simpa [eraseSites,ParkEndpoint.src] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (286+(137+j.val)) (by change 286+(137+j.val)<1556;omega),away (786+(137+j.val)) (by change 786+(137+j.val)<1556;omega)]
    exact low ⟨137+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (426+j.val) (by change 426+j.val<1556;omega),away (926+j.val) (by change 926+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈ParkEndpoint.src
    · have range : ∀q∈ParkEndpoint.src,1556≤q ∧ q≤1799 := by decide +kernel
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 255 529 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    have hiA (i:Fin 103) : 426+i.val∈sites Portal270Flag.hiPairs := by
      exact (by decide +kernel : ∀i:Fin 103,426+i.val∈sites Portal270Flag.hiPairs) i
    have hiB (i:Fin 103) : 926+i.val∈sites Portal270Flag.hiPairs := by
      exact (by decide +kernel : ∀i:Fin 103,926+i.val∈sites Portal270Flag.hiPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Portal270Flag.hiPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:286≤q ∧ q<426
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 286 140 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<926
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 140 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1799 := by
      unfold Exterior at external;unfold leftovers at residual
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave255BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [ParkEndpoint.src,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual
open Arithmetic MappedCompressed IntegerPacket WideReference EnterProof NativePack255 Partial LeaveReadoutFrame
set_option maxRecDepth 32000
set_option maxHeartbeats 2700000

def mirrorSites:=List.range' 1301 13
def untouched:=529::mirrorSites

theorem agree (d:Bool) (raw s:State) (x p:Nat) (good:Bounds x p) (dom:Domain 255 x p raw)
    (a b m:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (clear:∀q∈Leave255BoundaryClean.zeros,
      (run leave255 m (run (body idx (withArchive d)) b (run enter255 a s))).basis q=false) :
    let v:=run (body idx (withArchive d)) b (run enter255 a s)
    ∀q:Wire, q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313) →
      (run leave255 m v).basis q=(origin 255 raw v).basis q := by
  let v:=run (body idx (withArchive d)) b (run enter255 a s)
  have stable : ∀q∈untouched,q∉leave255.map LeaveReadoutFrame.destination := by decide +kernel
  have mirror (q:Wire) (lo:1301≤q) (hi:q≤1313) : v.basis q=false := by
    have mem:q∈mirrorSites:=List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩
    have marks : ∀q∈mirrorSites,¬MayTouch idx (windowNet idx q) ∧ q∉(support++ArchiveBoundary255.rawPortsList) ∧
        q∉ports255 ∧ q∉Enter255.pending ∧ OB5.sig 254 q=q ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧
        q∉RailPair.sites Enter255.upperPairs := by decide +kernel
    obtain ⟨off,adminOff,enterOff,mask,source,hn,hf,hu,no⟩:=marks q mem
    have normal:=ext_head enter255 idx (withArchive d) (support++ArchiveBoundary255.rawPortsList) s a b q off
      (fun h=>enterOff (List.mem_toFinset.mp (Enter255.programCover h))) adminOff (admin_cover d)
    apply normal.trans
    have original:raw.basis q=false:=by
      obtain ⟨ref,match',stage⟩:=dom
      apply (match'.2 q (outside_above (by change 1044+255≤q;simp only [Wire] at *;omega))).trans
      have fields:=(W.compactSkywalkStage_fields_iff base _ 255 (by decide) base_pool_nodup _).mp stage
      have qid:q=base (1028+(q-1044)):=by change q=1028+(q-1044)+16;simp only [Wire] at *;omega
      have jlo:255≤q-1044:=by simp only [Wire] at *;omega
      have jhi:q-1044<512:=by simp only [Wire] at *;omega
      exact qid ▸ (fields.2.2.2.2.1 _ jlo jhi).2
    have cleared:((eraseSites Enter255.pending s)).basis q=false:=
      (cut.unchanged q hn hf hu no).trans (by simpa only [pullState,source] using original)
    simpa [eraseSites,mask] using cleared
  dsimp only
  intro q site
  rw [Leave255ReleasedOrigin.released _ _ good _ _ dom _ site]
  rcases site with rfl|band|⟨lo,hi⟩
  · rw [preserved _ _ _ _ (stable 529 (by decide))]
    exact upper_clear _ _ _ _ _ dom _ _ _ _ _ cut 529 (by decide) (by decide)
  · exact clear q (by simp only [Leave255BoundaryClean.zeros,List.mem_append,List.mem_range'_1];simp only [Wire] at *;omega)
  · have mem:q∈mirrorSites:=List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩
    rw [preserved _ _ _ _ (stable q (List.mem_cons_of_mem _ mem))]
    exact mirror q lo hi
end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^144
  odd:z.v%2=1
  room:Shadow.high 144 15 z+1<2^97
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136
  bound:Leave225TrueMiddle.F z<2^112

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[225] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 224
  have short:=true_small x p 240 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[240] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 225 _).symm
  refine ⟨true_small x p 225 hx hp (by decide),(SkywalkNat.iter_valid 225 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).1,?_,(LeaveBankEnvelope.outputs z (by omega) 15).1⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 10 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis
  fresh:s.basis 1723=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,97≤t→t<112→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0
  zero:∀q∈Leave225FrontReady.watched,s.basis q=false
  far:s.basis 1721=decide (Shadow.far 144 15 z)
  side:s.basis 1722=(decide (Shadow.far 144 15 z) && decide (2^144≤z.u))
  record:readCells (shape 10) 0 15 (mappedBasis 10 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
def spare:List Wire:=[1724, 1725]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 97 15).map wire) ++ Leave225FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1717) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 10 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 144 15 z).u (Shadow.reduced 144 15 z).v)) s.basis)
    (record:readCells (shape 10) 0 15 (mappedBasis 10 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 144 15 z then Shadow.high 144 15 z else 0) ∧
      s.basis 1723=false ∧ s.basis 1721=decide (Shadow.far 144 15 z) ∧ s.basis 1722=decide (Shadow.far 144 15 z ∧ 2^144≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry225 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 97 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 144 15 z <;> simp [f]
end ECDSAAdd.Entrant.StairPacket.Leave225Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 225 x p raw)
    (input:InputAt 225 (encode g sg (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (record:physicalCells 10 s=SkywalkTrace.trace 15 (encode g sg (unsigned 225 x p).u (unsigned 225 x p).v))
    (kept:physicalCells 10 (run leave225 m s)=physicalCells 10 s)
     :
    ∀q,Leave225AssembleCut.leftovers q → (run leave225 m s).basis q=(origin 225 raw s).basis q := by
  let out:=run leave225 m s
  let o:=origin 225 raw s
  have geo : ∀i:Fin 15,windowNet 10 (ports (shape 10) i.val).a0=241+i.val ∧
      windowNet 10 (ports (shape 10) i.val).history=Leave225Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (241+i.val)=o.basis (241+i.val) ∧
      out.basis (Leave225Hit.swaps i.val)=o.basis (Leave225Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places225 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 10) 0 15 (mappedBasis 10 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 10) 0 15 (mappedBasis 10 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 10 (ports (shape 10) i.val).a0),out.basis (windowNet 10 (ports (shape 10) i.val).history)) =
      (o.basis (windowNet 10 (ports (shape 10) i.val).a0),o.basis (windowNet 10 (ports (shape 10) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 240=o.basis 240 := by
    rw [show o.basis 240=s.basis 240 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 240 leave225=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>241+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave225Hit.swaps i.val)
  intro q residual
  by_cases prev:q=240
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave225AssembleCut.leftovers a.val → a.val≠240 → a.val∉gs → a.val∉ss →
      False := by
    unfold Leave225AssembleCut.leftovers; dsimp only [gs,ss];decide +kernel
  have bound:q<1813:=by unfold Leave225AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact False.elim (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^136
  odd:z.v%2=1
  room:Shadow.high 136 15 z+1<2^105
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129
  bound:Leave240TrueMiddle.F z<2^120

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[240] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[240] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 239
  have short:=true_small x p 255 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[255] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 240 _).symm
  refine ⟨true_small x p 240 hx hp (by decide),(SkywalkNat.iter_valid 240 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).2.1,?_,(LeaveBankEnvelope.outputs z (by omega) 15).2.1⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 11 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis
  fresh:s.basis 1715=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,105≤t→t<120→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0
  zero:∀q∈Leave240FrontReady.watched,s.basis q=false
  far:s.basis 1713=decide (Shadow.far 136 15 z)
  side:s.basis 1714=(decide (Shadow.far 136 15 z) && decide (2^136≤z.u))
  record:readCells (shape 11) 0 15 (mappedBasis 11 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
def spare:List Wire:=[1716, 1717]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 105 15).map wire) ++ Leave240FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1709) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 11 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 136 15 z).u (Shadow.reduced 136 15 z).v)) s.basis)
    (record:readCells (shape 11) 0 15 (mappedBasis 11 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 136 15 z then Shadow.high 136 15 z else 0) ∧
      s.basis 1715=false ∧ s.basis 1713=decide (Shadow.far 136 15 z) ∧ s.basis 1714=decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry240 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 105 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 136 15 z <;> simp [f]
end ECDSAAdd.Entrant.StairPacket.Leave240Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 240 x p raw)
    (input:InputAt 240 (encode g sg (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (record:physicalCells 11 s=SkywalkTrace.trace 15 (encode g sg (unsigned 240 x p).u (unsigned 240 x p).v))
    (kept:physicalCells 11 (run leave240 m s)=physicalCells 11 s)
     :
    ∀q,Leave240AssembleCut.leftovers q → (run leave240 m s).basis q=(origin 240 raw s).basis q := by
  let out:=run leave240 m s
  let o:=origin 240 raw s
  have geo : ∀i:Fin 15,windowNet 11 (ports (shape 11) i.val).a0=256+i.val ∧
      windowNet 11 (ports (shape 11) i.val).history=Leave240Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (256+i.val)=o.basis (256+i.val) ∧
      out.basis (Leave240Hit.swaps i.val)=o.basis (Leave240Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places240 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 11) 0 15 (mappedBasis 11 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 11) 0 15 (mappedBasis 11 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 11 (ports (shape 11) i.val).a0),out.basis (windowNet 11 (ports (shape 11) i.val).history)) =
      (o.basis (windowNet 11 (ports (shape 11) i.val).a0),o.basis (windowNet 11 (ports (shape 11) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 255=o.basis 255 := by
    rw [show o.basis 255=s.basis 255 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 255 leave240=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>256+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave240Hit.swaps i.val)
  intro q residual
  by_cases prev:q=255
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave240AssembleCut.leftovers a.val → a.val≠255 → a.val∉gs → a.val∉ss →
      False := by
    unfold Leave240AssembleCut.leftovers; dsimp only [gs,ss];decide +kernel
  have bound:q<1813:=by unfold Leave240AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact False.elim (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^129
  odd:z.v%2=1
  room:Shadow.high 129 15 z+1<2^112
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121
  bound:Leave255TrueMiddle.F z<2^127

theorem actualNumbers (x p:Nat) (hp0:0<p) (odd:p%2=1) (hx:x<2^256) (hp:p<2^256):
    Numeric (SkywalkNat.step^[255] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[255] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^256+2^255:=LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le 254
  have short:=true_small x p 270 hx hp (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[270] (SkywalkNat.init x p):=by
    exact (Function.iterate_add_apply SkywalkNat.step 15 255 _).symm
  refine ⟨true_small x p 255 hx hp (by decide),(SkywalkNat.iter_valid 255 (SkywalkNat.init x p) hp0 odd).2.1,
    (LeaveBankEnvelope.bounds z env).2.2,?_,(LeaveBankEnvelope.outputs z (by omega) 15).2.2⟩
  rw [it];exact short

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 12 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis
  fresh:s.basis 1708=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,112≤t→t<127→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0
  zero:∀q∈Leave255FrontReady.watched,s.basis q=false
  far:s.basis 1706=decide (Shadow.far 129 15 z)
  side:s.basis 1707=(decide (Shadow.far 129 15 z) && decide (2^129≤z.u))
  record:readCells (shape 12) 0 15 (mappedBasis 12 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  extra:∀q,1713≤q→q≤1718→s.basis q=false
def spare:List Wire:=[1709, 1710, 1713, 1714, 1715, 1716, 1717, 1718]
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 112 15).map wire) ++ Leave255FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1702) ∨ q∈spare:=by decide +kernel
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 12 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 129 15 z).u (Shadow.reduced 129 15 z).v)) s.basis)
    (record:readCells (shape 12) 0 15 (mappedBasis 12 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 129 15 z then Shadow.high 129 15 z else 0) ∧
      s.basis 1708=false ∧ s.basis 1706=decide (Shadow.far 129 15 z) ∧ s.basis 1707=decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=carry255 _ s rails
  have all (q:Wire) (hit:q∈touch):s.basis q=false:=by
    rcases geometry q hit with h|h
    · exact cl q h.1 h.2
    · exact ex q h
  refine ⟨numbers,?_,saved.2.1,?_,?_,?_,?_,saved.1,?_,saved.2.2.1,?_,record,?_⟩
  · exact (SharedSigned.same _ z numbers.small numbers.odd g0 s0).1 ▸ rails
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · intro t h;apply all;have mem:=List.mem_map_of_mem (f:=Prod.snd) h;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr mem)))
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inl (Or.inl (Or.inr h))
  · intro t lo hi
    have hit:t∈List.range' 112 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 129 15 z <;> simp [f]
  · intro q lo hi
    apply ex
    have inc:∀q∈List.range' 1713 6,q∈spare:=by decide
    exact inc q (List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩)
end ECDSAAdd.Entrant.StairPacket.Leave255Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 255 x p raw)
    (input:InputAt 255 (encode g sg (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (record:physicalCells 12 s=SkywalkTrace.trace 15 (encode g sg (unsigned 255 x p).u (unsigned 255 x p).v))
    (kept:physicalCells 12 (run leave255 m s)=physicalCells 12 s)
    (extra:∀q:Wire,q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1313) → (run leave255 m s).basis q=(origin 255 raw s).basis q) :
    ∀q,Leave255AssembleCut.leftovers q → (run leave255 m s).basis q=(origin 255 raw s).basis q := by
  let out:=run leave255 m s
  let o:=origin 255 raw s
  have geo : ∀i:Fin 15,windowNet 12 (ports (shape 12) i.val).a0=271+i.val ∧
      windowNet 12 (ports (shape 12) i.val).history=Leave255Hit.swaps i.val := by decide +kernel
  have agree (i:Fin 15) : out.basis (271+i.val)=o.basis (271+i.val) ∧
      out.basis (Leave255Hit.swaps i.val)=o.basis (Leave255Hit.swaps i.val) := by
    have old:=recorded_equal _ _ _ _ (by decide) places255 good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 12) 0 15 (mappedBasis 12 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 12) 0 15 (mappedBasis 12 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 12 (ports (shape 12) i.val).a0),out.basis (windowNet 12 (ports (shape 12) i.val).history)) =
      (o.basis (windowNet 12 (ports (shape 12) i.val).a0),o.basis (windowNet 12 (ports (shape 12) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 270=o.basis 270 := by
    rw [show o.basis 270=s.basis 270 from inside _ _ _ _ (by decide +kernel)]
    have stable : LeaveSelector.parityAt 270 leave255=some false := by decide +kernel
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>271+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave255Hit.swaps i.val)
  intro q residual
  by_cases prev:q=270
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  have census : ∀a:Fin 1813,Leave255AssembleCut.leftovers a.val → a.val≠270 → a.val∉gs → a.val∉ss →
      Leave255ReleasedOrigin.releasedSite a.val := by
    unfold Leave255AssembleCut.leftovers; dsimp only [gs,ss];set_option synthInstance.maxSize 4096 in decide +kernel
  have bound:q<1813:=by unfold Leave255AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact extra q (census ⟨q,bound⟩ residual prev gg sw)
end ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave225Inv n (run leave225 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave225RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave225 o s).phase=s.phase:=by
    exact (Leave225Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave225Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry225 _ s h.ready)
end ECDSAAdd.Entrant.StairPacket.Leave225Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 225 x p raw)
    (input:InputAt 225 (encode g0 s0 (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (h:Leave225Admission.Inputs s (unsigned 225 x p) g0 s0)
    (phase:s.phase=(origin 225 raw s).phase)
    (ext:∀q,Exterior 225 512 q → s.basis q=(origin 225 raw s).basis q)
    (upper:∀q:Nat,419≤q → q≤512 → s.basis q=false)
    (quiet:∀q∈Leave225CoreCheckpoint.rawSites,s.basis q=false)
     :
    let z:=unsigned 225 x p
    let flags:=Leave225Admission.flags z g0 s0
    let a:=unsigned 240 x p
    let out:=run leave225 m s
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 136 15 a)) (decide (Shadow.far 136 15 a ∧ 2^136≤a.u))
      (pullState (OB5.sig 239) (endRaw 225 raw s)) (eraseSites Enter240.pending out) := by
  let z:=unsigned 225 x p
  let flags:=Leave225Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 240 x p := (Function.iterate_add_apply SkywalkNat.step 15 225 _).symm
  have signed:= (advance_signed 225 144 x p (by decide) (by decide) fixed225 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave225WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 225 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave225RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave225RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave225EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave225Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave225PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave225FrameHistory.result x p good raw s m g0 s0 dom input h.record kept
  have rails:=Leave225BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side upper (endRaw _ raw s) nextInput
  have clear:=Leave225BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet
  dsimp only
  rw [←endpointState,endpoint 225 (by decide)]
  rw [endpoint 225 (by decide)] at rails
  apply Leave225AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack225.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c225
end ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave240Inv n (run leave240 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave240RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave240 o s).phase=s.phase:=by
    exact (Leave240Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave240Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry240 _ s h.ready)
end ECDSAAdd.Entrant.StairPacket.Leave240Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 240 x p raw)
    (input:InputAt 240 (encode g0 s0 (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (h:Leave240Admission.Inputs s (unsigned 240 x p) g0 s0)
    (phase:s.phase=(origin 240 raw s).phase)
    (ext:∀q,Exterior 240 527 q → s.basis q=(origin 240 raw s).basis q)
    (upper:∀q:Nat,426≤q → q≤527 → s.basis q=false)
    (quiet:∀q∈Leave240CoreCheckpoint.rawSites,s.basis q=false)
     :
    let z:=unsigned 240 x p
    let flags:=Leave240Admission.flags z g0 s0
    let a:=unsigned 255 x p
    let out:=run leave240 m s
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 129 15 a)) (decide (Shadow.far 129 15 a ∧ 2^129≤a.u))
      (pullState (OB5.sig 254) (endRaw 240 raw s)) (eraseSites Enter255.pending out) := by
  let z:=unsigned 240 x p
  let flags:=Leave240Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 255 x p := (Function.iterate_add_apply SkywalkNat.step 15 240 _).symm
  have signed:= (advance_signed 240 136 x p (by decide) (by decide) fixed240 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave240WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 240 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave240RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave240RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave240EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave240Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave240PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave240FrameHistory.result x p good raw s m g0 s0 dom input h.record kept
  have rails:=Leave240BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side upper (endRaw _ raw s) nextInput
  have clear:=Leave240BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet
  dsimp only
  rw [←endpointState,endpoint 240 (by decide)]
  rw [endpoint 240 (by decide)] at rails
  apply Leave240AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack240.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c240
end ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool} (h:Inputs s z g0 s0) (m n:List Bool):
    run leave255Inv n (run leave255 m s)=s:=by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave255RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave255 o s).phase=s.phase:=by
    exact (Leave255Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave255Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound ph (carry255 _ s h.ready) h.extra
end ECDSAAdd.Entrant.StairPacket.Leave255Admission


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 255 x p raw)
    (input:InputAt 255 (encode g0 s0 (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (h:Leave255Admission.Inputs s (unsigned 255 x p) g0 s0)
    (phase:s.phase=(origin 255 raw s).phase)
    (ext:∀q,Exterior 255 529 q → s.basis q=(origin 255 raw s).basis q)
    (upper:∀q:Nat,434≤q → q≤529 → s.basis q=false)
    (quiet:∀q∈Leave255CoreCheckpoint.rawSites,s.basis q=false)
    (extra:∀q:Wire,Leave255ReleasedOrigin.releasedSite q → (run leave255 m s).basis q=(origin 255 raw s).basis q) :
    let z:=unsigned 255 x p
    let flags:=Leave255Admission.flags z g0 s0
    let a:=unsigned 270 x p
    let out:=run leave255 m s
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 121 15 a)) (decide (Shadow.far 121 15 a ∧ 2^121≤a.u))
      (pullState (OB5.sig 269) (endRaw 255 raw s)) (eraseSites ParkEndpoint.src out) := by
  let z:=unsigned 255 x p
  let flags:=Leave255Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 270 x p := (Function.iterate_add_apply SkywalkNat.step 15 255 _).symm
  have signed:= (advance_signed 255 129 x p (by decide) (by decide) fixed255 good raw s dom g0 s0 input h.small).2
  have nextInput : SkywalkIntegerInput Leave255WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (endRaw 255 raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave255RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave255EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave255Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave255PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave255FrameHistory.result x p good raw s m g0 s0 dom input h.record kept extra
  have rails:=Leave255BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side (fun q lo hi=>upper q lo (Nat.le_trans hi (by decide))) (endRaw _ raw s) nextInput
  have clear:=Leave255BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet (LeaveTerminalBound.fit x p good.nonzero good.positive good.odd good.cap good.small good.coprime)
  dsimp only
  rw [←endpointState,endpoint 255 (by decide)]
  rw [endpoint 255 (by decide)] at rails
  apply Leave255AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(NativePack255.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · exact carry_origin (by decide) (by decide) good raw s dom same_c255
end ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
theorem admitted_with_input (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (firstWindow d) m origin
    ∃g0 s0:Bool,SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (encode g0 s0 z.u z.v).a (encode g0 s0 z.u z.v).b g0 raw.basis ∧ Leave225Admission.Inputs out z g0 s0:=by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
  let origin:=pullState (OB5.sig 224) raw
  let cut:=run Partial.portal225 m origin
  let n:=m.drop (measurementCount Partial.portal225)
  let pre:=run Partial.enter225 n cut
  let tape:=n.drop (measurementCount Partial.enter225)
  let T:=Shadow.reduced 144 15 z
  have small:min z.u z.v<2^144:=true_small seed p 225 (by omega) hp (by decide)
  obtain ⟨G,S,input⟩:=PortalValues.real_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw stage
  have pcut:=Portal225Flag.physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m stage G S input
  have same:Shadow.far 144 15 z=(3*2^160≤z.u+z.v):=by
    apply propext
    unfold Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have normalized:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
      (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) origin cut:=by
    simpa only [same] using pcut
  have numbers:=Leave225Admission.actualNumbers seed p hp0 hpo (lt_trans hx hp) hp
  have values:=saved_at_leave d raw cut z G S n (n.drop (measurementCount Partial.enter225)) small normalized input
  have more:=extra_clean d raw cut n (n.drop (measurementCount Partial.enter225)) _ _ _ _ _ _ normalized input
  have ready:=Enter225.ready_from_cut raw cut z G S n small normalized input
    (fun r=>by simpa only [Nat.add_assoc] using stock_history d seed p 225 raw stage (225+r) (by omega) (by have hr:=r.isLt;omega))
  have zo:z.v%2=1:=(SkywalkNat.iter_valid 225 (SkywalkNat.init seed p) hp0 hpo).2.1
  have to':T.v%2=1:=shadow_odd 144 z small zo
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have initial:=original_legal d seed p hp0 hpo raw stage
  have legal:=legal_congr (history_from_stock raw cut pre pcut n tape rfl _ parity ready.2) initial
  have whole:=window_run d pre tape _ parity ready.2 legal
  refine ⟨G,S,input,Leave225Admission.assemble _ _ _ _ numbers ?_ ?_ ?_ ?_⟩
  · simpa only [firstWindow,run_append,run_take,origin,n,pre,tape,cut] using whole.2.1
  · simpa only [firstWindow,run_append,run_take,origin,n,pre,tape,cut] using whole.2.2.1.trans (true_records 144 z small zo G S)
  · simpa only [firstWindow,window,run_append,run_take,origin,cut,n] using values
  · intro q h
    have inc:∀q∈Leave225Admission.spare,q∈spares:=by decide
    simpa only [firstWindow,window,run_append,run_take,origin,cut,n] using more q (inc q h)
theorem admitted (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (firstWindow d) m origin
    ∃g0 s0:Bool,Leave225Admission.Inputs out z g0 s0:=by
  obtain ⟨g,sg,_,facts⟩:=admitted_with_input d seed p hp0 hx0 hpo hp hq hx hc raw m stage
  exact ⟨g,sg,facts⟩
end ECDSAAdd.Entrant.StairPacket.NativePack225


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
open ArchiveBoundary240
theorem admitted (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:Leave240Admission.Numeric z)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out z G S:=by
  let tape:=m.drop (measurementCount Partial.enter240)
  have saved:=saved_with_pending d raw s z G S m tape numbers.small cut input
  have all:=next_window d raw s m z G S numbers.odd numbers.small cut input hist past pg ps cross po pm prior
  obtain ⟨_,_,_,tags⟩:=real_receipt d raw s m z G S numbers.odd numbers.small cut input hist past pg ps cross po pm prior
  apply Leave240Admission.assemble _ _ _ _ numbers all.2.1 all.2.2.1
  · simpa only [nextWindow,window,run_append,run_take,tape] using saved
  · intro q h
    have inc:∀q∈Leave240Admission.spare,∃t:Fin 3,q=1716+t.val:=by decide
    obtain ⟨t,rfl⟩:=inc q h
    exact tags t
end ECDSAAdd.Entrant.StairPacket.NativePack240


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run body measurementCount onRails
open ArchiveBoundary255
theorem admitted (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (numbers:Leave255Admission.Numeric z)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out z G S:=by
  let tape:=m.drop (measurementCount Partial.enter255)
  have saved:=saved_with_pending d raw s z G S m tape numbers.small cut input
  have all:=next_window d raw s m z G S numbers.odd numbers.small cut input hist endScratch past pg ps cross po pm prior
  obtain ⟨_,_,_,tags⟩:=real_receipt d raw s m z G S numbers.odd numbers.small cut input hist endScratch past pg ps cross po pm prior
  apply Leave255Admission.assemble _ _ _ _ numbers all.2.1 all.2.2.1
  · simpa only [nextWindow,window,run_append,run_take,tape] using saved
  · intro q h
    have inc:∀q∈Leave255Admission.spare,(∃t:Fin 3,q=1709+t.val) ∨ q∈spares:=by decide
    rcases inc q h with ⟨t,rfl⟩|hm
    · exact tags t
    · have ex:=extra_clean d raw s m tape _ _ _ _ _ _ cut input q hm
      simpa only [nextWindow,window,run_append,run_take,tape] using ex
end ECDSAAdd.Entrant.StairPacket.NativePack255


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave225Admission.Inputs s z g sg) :
    let out:=run leave225 m s
    PastFacts 10 ArchiveBoundary240.rawPorts 144 z g sg (HighBankSum.cross (Leave225TrueMiddle.d z)) out := by
  let flags:=Leave225Admission.flags z g sg
  have all:=Leave225ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact ⟨all.1,all.2.1,all.2.2.1,all.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave240Admission.Inputs s z g sg) :
    let out:=run leave240 m s
    PastFacts 11 ArchiveBoundary255.rawPorts 136 z g sg (HighBankSum.cross (Leave240TrueMiddle.d z)) out := by
  let flags:=Leave240Admission.flags z g sg
  have all:=Leave240ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact ⟨all.1,all.2.1,all.2.2.1,all.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave255Admission.Inputs s z g sg) :
    let out:=run leave255 m s
    physicalCells 12 out=SkywalkTrace.trace 15 (encode g sg z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && StairArchiveTrace.afterFlags (decide (z.v<z.u)) ((physicalCells 12 out).take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z)) := by
  let flags:=Leave255Admission.flags z g sg
  have all:=Leave255ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact all
end ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
theorem from_domain (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out (unsigned 240 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 240 x p
  let prev:=unsigned 225 x p
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,code,_⟩:=real_receipt d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,code⟩,a.2.2.2⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem from_domain (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out (unsigned 255 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 255 x p
  let prev:=unsigned 240 x p
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have clear:=WideReference.carry (by decide) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,code,_⟩:=real_receipt d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist clear prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,code⟩,a.2.2.2⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
theorem from_domain_matched (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave240Admission.Inputs out (unsigned 240 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned 225 x p) pg ps row ∧ Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 240 x p
  let prev:=unsigned 225 x p
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,truth,code,_⟩:=matched_receipt d raw s m z G S nums.odd nums.small cut input hist prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem from_domain_matched (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let out:=run (nextWindow d) m s
    Leave255Admission.Inputs out (unsigned 255 x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned 240 x p) pg ps row ∧ Kept codePorts d row out) ∧ ∀n,run (nextUnwind d) n out=s:=by
  let z:=unsigned 255 x p
  let prev:=unsigned 240 x p
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have clear:=WideReference.carry (by decide) domain
  have a:=next_window d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  obtain ⟨row,limit,truth,code,_⟩:=matched_receipt d raw s m z G S nums.odd nums.small cut input hist clear prev pg ps cross old.odd old.small prior
  exact ⟨admitted d raw s m z G S nums cut input hist clear prev pg ps cross old.odd old.small prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket


end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open Arithmetic IntegerPacket SkywalkRails WideReference StairArchiveRaw StairArchiveTrace CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 16000

def Chronology (i x p row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (WideReference.canonical i x p)).drop 5) (q.val/2)) q

theorem chronology (i x p row:Nat) (less:i<512) (good:Bounds x p) (raw:State) (domain:Domain i x p raw) (g sg:Bool)
    (input:InputAt i (encode g sg (unsigned i x p).u (unsigned i x p).v) raw)
    (truth:RowTruth (unsigned i x p) g sg row) : Chronology i x p row := by
  have same:=unique_input input (fixed_input i x p less good raw domain)
  unfold Chronology
  rw [←same]
  exact truth

structure Final (d:Bool) (x p:Nat) (out:State) : Prop where
  first : ∃row<63145,Chronology 225 x p row ∧ Kept ArchiveBoundary240.codePorts d row out
  middle : ∃row<63145,Chronology 240 x p row ∧ Kept ArchiveBoundary255.codePorts d row out
  last : ∃row<63145,Chronology 255 x p row ∧ Frame ArchiveBoundary270.codePorts (code d) row out

end ECDSAAdd.Entrant.StairPacket.ArchiveStockRows


end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix
open Arithmetic MappedCompressed
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
def logical (sw:Bool) (r:Nat):Wire:=if sw then base (1028+r) else base r
def site (sw:Bool) (r:Nat):Wire:=OB5.sig 270 (logical sw r)
theorem stable (i:Nat) (lo:270 ≤ i) (hi:i ≤ 511) (r:Nat) (old:r < 270) (sw:Bool):
    OB5.sig i (logical sw r)=site sw r:=by
  cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,site,
    StairField2V3JuncRefWalk.sig_base i hi,StairField2V3JuncRefWalk.sig_base 270 (by decide)]
  all_goals split_ifs <;> first | rfl | omega
private theorem no_pack (i:Nat) (lo:271 ≤ i) (hi:i < 512) (r:Nat) (old:r < 270) (d sw:Bool):
    logical sw r∉wires (Rolling1588.Integer.packFirst base d i) ∧
    logical sw r∉wires (Rolling1588.unpackAtTick d i):=by
  by_cases early:i < 275
  · have mem:i∈[271,272,273,274]:=by simp;omega
    have none:∀k∈[271,272,273,274],Rolling1588.Integer.packFirst base d k=[] ∧ Rolling1588.unpackAtTick d k=[]:=by
      cases d <;> decide +kernel
    rw [(none i mem).1,(none i mem).2];simp [wires]
  · have disjoint (j:Fin 10):logical sw r≠History5.historyMap base (i-5) j:=by
      have lim:=j.isLt
      cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,History5.historyMap,History5.historyId,base,Wire]
      all_goals split_ifs <;> omega
    constructor
    · intro h
      rw [Rolling1588.Integer.packFirst,if_neg (show i≠5 by omega),Rolling1588.Integer.pack_support_eq] at h
      unfold History5.packAfter at h
      split at h
      · obtain ⟨j,e⟩:=History5.history_gate_mem base (i-5) _ (Or.inl rfl) _ h
        exact disjoint j e
      · simp [wires] at h
    · intro h
      rw [←Rolling1588.Integer.unpackFirst_base,Rolling1588.Integer.unpackFirst,if_neg (show i≠5 by omega),
        Rolling1588.Integer.decodeBefore_support_eq] at h
      unfold History5.decodeBefore at h
      split at h
      · obtain ⟨j,e⟩:=History5.history_gate_mem base (i-5) _ (Or.inr rfl) _ h
        exact disjoint j e
      · simp [wires] at h
private theorem one (d sw:Bool) (r i:Nat) (old:r < 270) (lo:271 ≤ i) (hi:i < 512):
    site sw r∉wires (renameProgram (OB5.sig i) (TickRanges.tick base i ++ Rolling1588.Integer.packFirst base d i)) ∧
    site sw r∉wires (renameProgram (OB5.sig i) (Rolling1588.unpackAtTick d i ++ W.ReverseCarry.compactReceiverTick base i)):=by
  have past:WideReference.Earlier i (logical sw r):=⟨r,by omega,by cases sw <;> simp [logical]⟩
  have off:=WideReference.away hi past
  have pack:=no_pack i lo hi r old d sw
  have pre (q:Wire) (eq:OB5.sig i q=site sw r):q=logical sw r:=by
    rw [←stable i (by omega) (by omega) r old sw] at eq
    have inj:Function.Injective (OB5.sig i):=(OB5.sig_injective i (by omega))
    exact inj eq
  constructor <;> intro h <;> rw [renameProgram_support] at h <;>
    obtain ⟨q,mem,eq⟩:=Finset.mem_image.mp h <;> rw [pre q eq,wires_append,Finset.mem_union] at mem
  · rcases mem with tick|packet
    · exact off (List.mem_toFinset.mp (W.repairedTick_support base i hi base_pool_nodup (TickRanges.tick_support base i hi base_pool_nodup tick)))
    · exact pack.1 packet
  · rcases mem with packet|tick
    · exact pack.2 packet
    · exact off (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base i hi base_pool_nodup tick))
theorem suffix (d sw:Bool) (r i n:Nat) (old:r < 270) (lo:271 ≤ i) (hi:i+n≤512):
    site sw r∉wires (Rolling1588TickGap.forward d i n) ∧ site sw r∉wires (Rolling1588.reverse d i n):=by
  induction n generalizing i with
  | zero=>simp [Rolling1588TickGap.forward,Rolling1588.reverse,wires]
  | succ n ih=>
    have a:=one d sw r i old lo (by omega)
    have b:=ih (i+1) (by omega) (by omega)
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨a.1,b.1⟩,⟨b.2,a.2⟩⟩
def offset (j:Fin 16):Nat:=5*(j.val/8)+[0,0,1,1,2,3,3,4].getD (j.val%8) 0
def swap (j:Fin 16):Bool:=j.val%8∈[1,3,6]
theorem sites240:∀j:Fin 16,ArchiveBoundary240.codePorts ⟨j,by omega⟩=site (swap j) (230+offset j):=by decide +kernel
theorem old240:∀j:Fin 16,230+offset j<270:=by decide
theorem sites255:∀j:Fin 16,ArchiveBoundary255.codePorts ⟨j,by omega⟩=site (swap j) (245+offset j):=by decide +kernel
theorem old255:∀j:Fin 16,245+offset j<270:=by decide
theorem sites270:∀j:Fin 16,ArchiveBoundary270.codePorts ⟨j,by omega⟩=site (swap j) (260+offset j):=by decide +kernel
theorem old270:∀j:Fin 16,260+offset j<270:=by decide
def bank (n:Nat) (ports:ArchivePortAction.Ports):Finset Wire:=
  ((List.finRange n).map (fun j=>ports (Fin.ofNat 157 j.val))).toFinset
def archives:Finset Wire:=bank 16 ArchiveBoundary240.codePorts ∪ bank 16 ArchiveBoundary255.codePorts ∪ bank 16 ArchiveBoundary270.codePorts
theorem safe (d:Bool) (i n:Nat) (lo:271 ≤ i) (hi:i+n≤512) (q:Wire) (mem:q∈archives):
    q∉wires (Rolling1588TickGap.forward d i n) ∧ q∉wires (Rolling1588.reverse d i n):=by
  simp only [archives,bank,Finset.mem_union,List.mem_toFinset,List.mem_map,List.mem_finRange,true_and] at mem
  rcases mem with (⟨j,rfl⟩|⟨j,rfl⟩)|⟨j,rfl⟩
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites240]
    exact suffix d _ _ i n (old240 j) lo hi
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites255]
    exact suffix d _ _ i n (old255 j) lo hi
  · rw [show Fin.ofNat 157 j.val=(⟨j,by omega⟩:Fin 157) from Fin.ext (Nat.mod_eq_of_lt (by omega)),sites270]
    exact suffix d _ _ i n (old270 j) lo hi
def Same (a b:State):Prop:=a.phase=b.phase ∧ ∀q∉archives,a.basis q=b.basis q
theorem independent (P:Program) (off:∀q∈archives,q∉wires P)
    (m:List Bool) (s t:State) (same:Same s t):
    Same (run P m s) (run P m t) ∧ ∀q∈archives,(run P m s).basis q=s.basis q:=by
  have eqs:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m s t same.1
    (fun q h=>same.2 q (fun mem=>off q mem h))
  refine ⟨⟨eqs.1,?_⟩,fun q mem=>run_preserves_outside _ m s _ (off q mem)⟩
  intro q ext
  by_cases use:q∈wires P
  · exact eqs.2 q use
  · rw [run_preserves_outside _ m s _ use,run_preserves_outside _ m t _ use]
    exact same.2 q ext
end ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack225 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 225 x p raw)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722
      neg far long (pullState (OB5.sig 224) raw) s)
    (input:InputAt 225 (encode g0 s0 (unsigned 225 x p).u (unsigned 225 x p).v) raw)
    (h:Leave225Admission.Inputs (run (body idx (program d)) b (run enter225 a s)) (unsigned 225 x p) g0 s0)
    (phase:(run (body idx (program d)) b (run enter225 a s)).phase=s.phase) :
    let v:=run (body idx (program d)) b (run enter225 a s)
    let z:=unsigned 225 x p
    let flags:=Leave225Admission.flags z g0 s0
    let z':=unsigned 240 x p
    PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 136 15 z')) (decide (Shadow.far 136 15 z' ∧ 2^136≤z'.u))
      (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending (run leave225 m v)) := by
  let v:=run (body idx (program d)) b (run enter225 a s)
  let z:=unsigned 225 x p
  let flags:=Leave225Admission.flags z g0 s0
  have bank:=carry225 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave225CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave225CoreCheckpoint.rawSites,(1556≤q ∧ q≤1717) ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|endSite
    · exact bank q lo hi
    · exact tail q endSite
  have ph:v.phase=(origin 225 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  exact Leave225CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet
end ECDSAAdd.Entrant.StairPacket.Leave225BodyCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack240 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 240 x p raw)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714
      neg far long (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:InputAt 240 (encode g0 s0 (unsigned 240 x p).u (unsigned 240 x p).v) raw)
    (h:Leave240Admission.Inputs (run (body idx (withArchive d)) b (run enter240 a s)) (unsigned 240 x p) g0 s0)
    (phase:(run (body idx (withArchive d)) b (run enter240 a s)).phase=s.phase)
    (popped:(run (body idx (withArchive d)) b (run enter240 a s)).basis 1718=false) :
    let v:=run (body idx (withArchive d)) b (run enter240 a s)
    let z:=unsigned 240 x p
    let flags:=Leave240Admission.flags z g0 s0
    let z':=unsigned 255 x p
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 129 15 z')) (decide (Shadow.far 129 15 z' ∧ 2^129≤z'.u))
      (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending (run leave240 m v)) := by
  let v:=run (body idx (withArchive d)) b (run enter240 a s)
  let z:=unsigned 240 x p
  let flags:=Leave240Admission.flags z g0 s0
  have bank:=carry240 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave240CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave240CoreCheckpoint.rawSites,(1556≤q ∧ q≤1709) ∨ q=1718 ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|rfl|endSite
    · exact bank q lo hi
    · exact popped
    · exact tail q endSite
  have ph:v.phase=(origin 240 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  exact Leave240CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet
end ECDSAAdd.Entrant.StairPacket.Leave240BodyCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack255 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step

theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (a b m:List Bool)
    (neg far long g0 s0:Bool) (domain:Domain 255 x p raw)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707
      neg far long (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:InputAt 255 (encode g0 s0 (unsigned 255 x p).u (unsigned 255 x p).v) raw)
    (h:Leave255Admission.Inputs (run (body idx (withArchive d)) b (run enter255 a s)) (unsigned 255 x p) g0 s0)
    (phase:(run (body idx (withArchive d)) b (run enter255 a s)).phase=s.phase)
    (popped:(run (body idx (withArchive d)) b (run enter255 a s)).basis 1711=false) :
    let v:=run (body idx (withArchive d)) b (run enter255 a s)
    let z:=unsigned 255 x p
    let flags:=Leave255Admission.flags z g0 s0
    let z':=unsigned 270 x p
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 z'.u)
      (decide (Shadow.far 121 15 z')) (decide (Shadow.far 121 15 z' ∧ 2^121≤z'.u))
      (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src (run leave255 m v)) := by
  let v:=run (body idx (withArchive d)) b (run enter255 a s)
  let z:=unsigned 255 x p
  let flags:=Leave255Admission.flags z g0 s0
  have bank:=carry255 _ v h.ready
  have tail:=tail_clean d raw s a b neg far long _ _ _ cut input (carry (by decide) domain)
  have quiet (q:Wire) (mem:q∈Leave255CoreCheckpoint.rawSites) : v.basis q=false := by
    have layout:∀q∈Leave255CoreCheckpoint.rawSites,(1556≤q ∧ q≤1702) ∨ q=1711 ∨ q∈tailTemps := by decide +kernel
    rcases layout q mem with ⟨lo,hi⟩|rfl|endSite
    · exact bank q lo hi
    · exact popped
    · exact tail q endSite
  have ph:v.phase=(origin 255 raw v).phase := phase.trans (cut.phase.trans (origin_phase _ _ _ (by decide) good raw v domain).symm)
  have up:=upper_clear d raw s x p domain a b neg far long cut
  have ext:=agree_origin d raw s a b neg far long cut
  have par:=Leave255RecordedParity.result v z g0 s0 h.small h.odd h.record
  have md:actualMode 129 z=farMode (v.basis 1706) (v.basis 1707) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave255RecordedEvents.result v z g0 s0 h.small h.odd h.record
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have clear:=Leave255BoundaryClean.result v m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet (LeaveTerminalBound.fit x p good.nonzero good.positive good.odd good.cap good.small good.coprime)
  have extra:=Leave255ReleasedActual.agree d raw s x p good domain a b m neg far long cut clear
  exact Leave255CertifiedCut.result x p good raw v m g0 s0 domain input h ph ext up quiet extra
end ECDSAAdd.Entrant.StairPacket.Leave255BodyCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePersistence
open Arithmetic MappedCompressed IntegerPacket EnterProof ArchivePortAction ArchiveStockSuffix WideReference CodecBitSliceVerify Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body routed
def older:=bank 16 ArchiveBoundary240.codePorts
def two:=older ∪ bank 16 ArchiveBoundary255.codePorts
def first (q:Wire):Bool:=(246≤q && q≤255)||(1274≤q && q≤1283)
def next (q:Wire):Bool:=first q || (261≤q && q≤270)||(1289≤q && q≤1298)
theorem earlier:∀q∈older,first q=true:=by decide +kernel
theorem early:∀q∈two,next q=true:=by decide +kernel
private theorem keep (P:Program) (f:Wire→Bool) (test:P.all (fun g=> !f (target g))=true) (q:Wire) (mem:f q=true) (t:List Bool) (s:State):
    (run P t s).basis q=s.basis q:=by
  apply preserve_readonly
  intro g hit eq
  have h:=List.all_eq_true.mp test g hit
  rw [eq,mem] at h
  contradiction
private theorem cleave240Part0:leave240Part0.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part1:leave240Part1.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part2:leave240Part2.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part3:leave240Part3.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part4:leave240Part4.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part5:leave240Part5.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part6:leave240Part6.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part7:leave240Part7.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part8:leave240Part8.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part9:leave240Part9.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part10:leave240Part10.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part11:leave240Part11.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part12:leave240Part12.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part13:leave240Part13.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part14:leave240Part14.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part15:leave240Part15.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part16:leave240Part16.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part17:leave240Part17.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part18:leave240Part18.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part19:leave240Part19.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part20:leave240Part20.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part21:leave240Part21.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part22:leave240Part22.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part23:leave240Part23.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part24:leave240Part24.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part25:leave240Part25.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part26:leave240Part26.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part27:leave240Part27.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part28:leave240Part28.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part29:leave240Part29.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part30:leave240Part30.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part31:leave240Part31.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part32:leave240Part32.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part33:leave240Part33.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part34:leave240Part34.all (fun g=> !first (target g))=true:=by decide +kernel
private theorem cleave240Part35:leave240Part35.all (fun g=> !first (target g))=true:=by decide +kernel
theorem leave240_keeps (q:Wire) (mem:q∈older) (t:List Bool) (s:State):(run leave240 t s).basis q=s.basis q:=by
  apply keep _ first _ _ (earlier _ mem)
  simp only [leave240,List.all_append,cleave240Part0,cleave240Part1,cleave240Part2,cleave240Part3,cleave240Part4,cleave240Part5,cleave240Part6,cleave240Part7,cleave240Part8,cleave240Part9,cleave240Part10,cleave240Part11,cleave240Part12,cleave240Part13,cleave240Part14,cleave240Part15,cleave240Part16,cleave240Part17,cleave240Part18,cleave240Part19,cleave240Part20,cleave240Part21,cleave240Part22,cleave240Part23,cleave240Part24,cleave240Part25,cleave240Part26,cleave240Part27,cleave240Part28,cleave240Part29,cleave240Part30,cleave240Part31,cleave240Part32,cleave240Part33,cleave240Part34,cleave240Part35,Bool.and_self]
private theorem cleave255Part0:leave255Part0.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part1:leave255Part1.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part2:leave255Part2.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part3:leave255Part3.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part4:leave255Part4.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part5:leave255Part5.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part6:leave255Part6.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part7:leave255Part7.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part8:leave255Part8.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part9:leave255Part9.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part10:leave255Part10.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part11:leave255Part11.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part12:leave255Part12.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part13:leave255Part13.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part14:leave255Part14.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part15:leave255Part15.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part16:leave255Part16.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part17:leave255Part17.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part18:leave255Part18.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part19:leave255Part19.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part20:leave255Part20.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part21:leave255Part21.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part22:leave255Part22.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part23:leave255Part23.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part24:leave255Part24.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part25:leave255Part25.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part26:leave255Part26.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part27:leave255Part27.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part28:leave255Part28.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part29:leave255Part29.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part30:leave255Part30.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part31:leave255Part31.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part32:leave255Part32.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part33:leave255Part33.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part34:leave255Part34.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part35:leave255Part35.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cleave255Part36:leave255Part36.all (fun g=> !next (target g))=true:=by decide +kernel
theorem leave255_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run leave255 t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [leave255,List.all_append,cleave255Part0,cleave255Part1,cleave255Part2,cleave255Part3,cleave255Part4,cleave255Part5,cleave255Part6,cleave255Part7,cleave255Part8,cleave255Part9,cleave255Part10,cleave255Part11,cleave255Part12,cleave255Part13,cleave255Part14,cleave255Part15,cleave255Part16,cleave255Part17,cleave255Part18,cleave255Part19,cleave255Part20,cleave255Part21,cleave255Part22,cleave255Part23,cleave255Part24,cleave255Part25,cleave255Part26,cleave255Part27,cleave255Part28,cleave255Part29,cleave255Part30,cleave255Part31,cleave255Part32,cleave255Part33,cleave255Part34,cleave255Part35,cleave255Part36,Bool.and_self]
private theorem cpark270Part0:park270Part0.all (fun g=> !next (target g))=true:=by decide +kernel
theorem park270_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run park270 t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [park270,cpark270Part0]
private theorem cportal270InvPart0:portal270InvPart0.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart1:portal270InvPart1.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart2:portal270InvPart2.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart3:portal270InvPart3.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart4:portal270InvPart4.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart5:portal270InvPart5.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart6:portal270InvPart6.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart7:portal270InvPart7.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart8:portal270InvPart8.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart9:portal270InvPart9.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart10:portal270InvPart10.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart11:portal270InvPart11.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart12:portal270InvPart12.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart13:portal270InvPart13.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart14:portal270InvPart14.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart15:portal270InvPart15.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart16:portal270InvPart16.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart17:portal270InvPart17.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart18:portal270InvPart18.all (fun g=> !next (target g))=true:=by decide +kernel
private theorem cportal270InvPart19:portal270InvPart19.all (fun g=> !next (target g))=true:=by decide +kernel
theorem portal270Inv_keeps (q:Wire) (mem:q∈two) (t:List Bool) (s:State):(run portal270Inv t s).basis q=s.basis q:=by
  apply keep _ next _ _ (early _ mem)
  simp only [portal270Inv,List.all_append,cportal270InvPart0,cportal270InvPart1,cportal270InvPart2,cportal270InvPart3,cportal270InvPart4,cportal270InvPart5,cportal270InvPart6,cportal270InvPart7,cportal270InvPart8,cportal270InvPart9,cportal270InvPart10,cportal270InvPart11,cportal270InvPart12,cportal270InvPart13,cportal270InvPart14,cportal270InvPart15,cportal270InvPart16,cportal270InvPart17,cportal270InvPart18,cportal270InvPart19,Bool.and_self]
theorem next255_keeps (d:Bool) (q:Wire) (mem:q∈older) (t:List Bool) (s:State):
    (run (NativePack255.nextWindow d) t s).basis q=s.basis q:=by
  have layout:∀q∈older,¬MayTouch NativePack255.idx (windowNet NativePack255.idx q) ∧
      q∉ports255 ∧ q∉(NativePack255.support++ArchiveBoundary255.rawPortsList):=by decide +kernel
  obtain ⟨unseen,notEnter,notAdmin⟩:=layout q mem
  simp only [NativePack255.nextWindow,NativePack255.window,run_append,run_take]
  exact ext_head _ _ _ _ _ _ _ _ unseen
    (fun hit=>notEnter (List.mem_toFinset.mp (Enter255.programCover hit))) notAdmin (NativePack255.admin_cover d)
theorem last270_keeps (d:Bool) (q:Wire) (mem:q∈two) (t:List Bool) (s:State):
    (run (NativePack270.lastWindow d) t s).basis q=s.basis q:=by
  have layout:∀q∈two,q∉ArchiveBoundary270.rawPortsList ∧ ∀v:Fin 10,q≠NativePack270.history v:=by decide +kernel
  obtain ⟨notLoad,notPack⟩:=layout q mem
  have notTick:OB5.sig 270 q∉EndTick.L.wires:=by
    apply WideReference.away (i:=270) (by decide)
    have olderSites:∀q∈two,∃r∈List.range' 230 25,∃sw:Bool,q=site sw r:=by decide +kernel
    obtain ⟨r,hr,sw,rfl⟩:=olderSites q mem
    obtain ⟨_,hi⟩:=List.mem_range'_1.mp hr
    rw [site,OB5.sig_invol 270 (by decide)]
    exact ⟨r,by omega,by cases sw <;> simp [logical]⟩
  have nT:=EndTick.physical_free EndTick.P EndTick.supports.1 q notTick
  have nL:q∉wires (archiveLoad270 d):=fun hit=>notLoad (List.mem_toFinset.mp (ArchiveBoundary270.load_cover d hit))
  simp only [NativePack270.lastWindow,NativePack270.endSlice,run_append,run_take]
  rw [run_preserves_outside (archiveLoad270 d) _ _ _ nL,NativePack270.outside _ _ notPack,
    run_preserves_outside EndTick.physP _ _ _ nT,portal270Inv_keeps _ mem,park270_keeps _ mem]
end ECDSAAdd.Entrant.StairPacket.ArchivePersistence


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 35000
set_option maxHeartbeats 3500000
attribute [local irreducible] run body SkywalkNat.step

theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    let z:=unsigned 225 x p
    let a:=unsigned 240 x p
    let v:=run (firstWindow d) m (pullState (OB5.sig 224) raw)
    let out:=run leave225 n v
    ∃g s:Bool,let flags:=Leave225Admission.flags z g s
      InputAt 225 (encode g s z.u z.v) raw ∧ Leave225Admission.Inputs v z g s ∧
      PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative flags.2 a.u)
        (decide (Shadow.far 136 15 a)) (decide (Shadow.far 136 15 a ∧ 2^136≤a.u))
        (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending out) ∧
      PastFacts 10 ArchiveBoundary240.rawPorts 144 z g s (HighBankSum.cross (Leave225TrueMiddle.d z)) out := by
  let z:=unsigned 225 x p
  let o:=pullState (OB5.sig 224) raw
  let w:=run portal225 m o
  let v:=run (firstWindow d) m o
  let n1:=m.drop (measurementCount portal225)
  let n2:=n1.drop (measurementCount enter225)
  obtain ⟨g,s,inp,h⟩:=admitted_with_input d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have input:InputAt 225 (encode g s z.u z.v) raw:=by
    unfold InputAt;rw [gg];exact inp
  have packed:=Portal225Flag.physical_frame_for d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage g s inp
  have ph: v.phase=w.phase :=
    (first_window d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage).1.trans packed.phase.symm
  have split:v=run (body idx (program d)) n2 (run enter225 n1 w):=by
    unfold v firstWindow
    rw [run_append,run_take,run_append,run_take]
    rfl
  refine ⟨g,s,input,h,?_,Leave225ArchiveCut.result v n z g s h⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 239) (endRaw 225 raw v)) (eraseSites Enter240.pending (run leave225 n v))
  rw [split]
  exact Leave225BodyCut.result d x p good raw w n1 n2 n _ _ _ g s
    (initial 225 x p (by decide) d raw stage) packed input (split ▸ h) (split ▸ ph)

end ECDSAAdd.Entrant.StairPacket.NativePack225


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary240
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step
theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m n:List Bool)
    (domain:Domain 240 x p raw) (G S:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S (unsigned 240 x p).u)
      (decide (Shadow.far 136 15 (unsigned 240 x p))) (decide (Shadow.far 136 15 (unsigned 240 x p) ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).a (encode G S (unsigned 240 x p).u (unsigned 240 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 144 (unsigned 225 x p) pg ps cross s) :
    let z:=unsigned 240 x p
    let a:=unsigned 255 x p
    let flags:=Leave240Admission.flags z G S
    let v:=run (nextWindow d) m s
    let out:=run leave240 n v
    Leave240Admission.Inputs v z G S ∧
    PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 129 15 a)) (decide (Shadow.far 129 15 a ∧ 2^129≤a.u))
      (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending out) ∧
    PastFacts 11 ArchiveBoundary255.rawPorts 136 z G S (HighBankSum.cross (Leave240TrueMiddle.d z)) out := by
  let z:=unsigned 240 x p
  let v:=run (nextWindow d) m s
  let tape:=m.drop (measurementCount enter240)
  have native:=from_domain d x p good raw s m domain G S cut input pg ps cross prior
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  obtain ⟨_,_,_,popped⟩:=real_receipt d raw s m z G S native.1.odd native.1.small cut input hist (unsigned 225 x p) pg ps cross old.odd old.small prior
  have split:v=run (body idx (withArchive d)) tape (run enter240 m s):=by
    unfold v nextWindow
    rw [run_append,run_take]
    rfl
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt 240 (encode G S z.u z.v) raw:=by unfold InputAt;rw [gg];exact input
  refine ⟨native.1,?_,Leave240ArchiveCut.result v n z G S native.1⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 254) (endRaw 240 raw v)) (eraseSites Enter255.pending (run leave240 n v))
  rw [split]
  have bit:v.basis 1718=false:=popped (2:Fin 3)
  exact Leave240BodyCut.result d x p good raw s m tape n _ _ _ G S domain cut orig (split ▸ native.1)
    (split ▸ native.2.1) (split ▸ bit)
end ECDSAAdd.Entrant.StairPacket.NativePack240


end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary255
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body SkywalkNat.step
theorem stock_endpoint (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (m n:List Bool)
    (domain:Domain 255 x p raw) (G S:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S (unsigned 255 x p).u)
      (decide (Shadow.far 129 15 (unsigned 255 x p))) (decide (Shadow.far 129 15 (unsigned 255 x p) ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).a (encode G S (unsigned 255 x p).u (unsigned 255 x p).v).b G raw.basis)
    (pg ps cross:Bool) (prior:PastFacts sourceIdx rawPorts 136 (unsigned 240 x p) pg ps cross s) :
    let z:=unsigned 255 x p
    let a:=unsigned 270 x p
    let flags:=Leave255Admission.flags z G S
    let v:=run (nextWindow d) m s
    let out:=run leave255 n v
    Leave255Admission.Inputs v z G S ∧
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 121 15 a)) (decide (Shadow.far 121 15 a ∧ 2^121≤a.u))
      (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src out) ∧
    (physicalCells 12 out=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      out.basis 1701=decide (Shadow.far 129 15 z) ∧
      out.basis 1702=(decide (Shadow.far 129 15 z) && StairArchiveTrace.afterFlags (decide (z.v<z.u)) ((physicalCells 12 out).take 5)) ∧
      out.basis 1703=(decide (Shadow.far 129 15 z) && HighBankSum.cross (Leave255TrueMiddle.d z))) := by
  let z:=unsigned 255 x p
  let v:=run (nextWindow d) m s
  let tape:=m.drop (measurementCount enter255)
  have native:=from_domain d x p good raw s m domain G S cut input pg ps cross prior
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) domain
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  obtain ⟨_,_,_,popped⟩:=real_receipt d raw s m z G S native.1.odd native.1.small cut input hist (carry (by decide) domain) (unsigned 240 x p) pg ps cross old.odd old.small prior
  have split:v=run (body idx (withArchive d)) tape (run enter255 m s):=by
    unfold v nextWindow
    rw [run_append,run_take]
    rfl
  have gg (g s:Bool) (u v:Int) : (encode g s u v).g=g:=by cases g <;> rfl
  have orig:InputAt 255 (encode G S z.u z.v) raw:=by unfold InputAt;rw [gg];exact input
  refine ⟨native.1,?_,Leave255ArchiveCut.result v n z G S native.1⟩
  change PackedCut _ _ _ _ _ _ _ _ _ (pullState (OB5.sig 269) (endRaw 255 raw v)) (eraseSites ParkEndpoint.src (run leave255 n v))
  rw [split]
  have bit:v.basis 1711=false:=popped (2:Fin 3)
  exact Leave255BodyCut.result d x p good raw s m tape n _ _ _ G S domain cut orig (split ▸ native.1)
    (split ▸ native.2.1) (split ▸ bit)
end ECDSAAdd.Entrant.StairPacket.NativePack255


end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve
open Arithmetic IntegerPacket Partial ArchivePortAction WideReference LeaveReadoutFrame
set_option maxRecDepth 60000
set_option maxHeartbeats 5000000

def bank (ps:Ports):List Wire:=(List.finRange 16).map (fun j=>ps ⟨j.val,by omega⟩)
def bank1:=bank ArchiveBoundary240.codePorts
def bank2:=bank ArchiveBoundary255.codePorts
def both:=bank1++bank2

theorem keep {d:Bool} {row:Nat} {s t:State} {ps:Ports} (h:Kept ps d row s)
    (stable:∀q∈bank ps,t.basis q=s.basis q) : Kept ps d row t := by
  intro i
  rw [stable _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩),h i]

private theorem firstBank (q:Wire) (h:q∈bank1) : q∈ArchivePersistence.older :=
  (by decide +kernel : ∀q∈bank1,q∈ArchivePersistence.older) q h

private theorem bothBanks (q:Wire) (h:q∈both) : q∈ArchivePersistence.two :=
  (by decide +kernel : ∀q∈both,q∈ArchivePersistence.two) q h

theorem after240 (s:State) (m:List Bool) (q:Wire) (h:q∈bank1) : (run leave240 m s).basis q=s.basis q :=
  ArchivePersistence.leave240_keeps q (firstBank q h) m s

theorem entering255 (d:Bool) (s:State) (m:List Bool) (q:Wire) (h:q∈bank1) :
    (run (NativePack255.nextWindow d) m s).basis q=s.basis q :=
  ArchivePersistence.next255_keeps d q (firstBank q h) m s

theorem after255 (s:State) (m:List Bool) (q:Wire) (h:q∈both) : (run leave255 m s).basis q=s.basis q :=
  ArchivePersistence.leave255_keeps q (bothBanks q h) m s

theorem last (d:Bool) (s:State) (m:List Bool) (q:Wire) (h:q∈both) :
    (run (NativePack270.lastWindow d) m s).basis q=s.basis q :=
  ArchivePersistence.last270_keeps d q (bothBanks q h) m s
end ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve


end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 25000
attribute [local irreducible] run body SkywalkNat.step

def signedAt (i x p:Nat) (g s:Bool) := encode g s (unsigned i x p).u (unsigned i x p).v
def flagNeg (i x p:Nat) (sg:Bool) := PortalValues.negative sg (unsigned i x p).u
def farAt (b i x p:Nat) := Shadow.far b 15 (unsigned i x p)
instance (b i x p:Nat) : Decidable (farAt b i x p) := by unfold farAt;infer_instance

theorem readInput (i x p:Nat) (raw:State) (g sg:Bool) (h:InputAt i (signedAt i x p g sg) raw) :
    SkywalkIntegerInput (W.compactSkywalkTickLayout base i) (signedAt i x p g sg).a (signedAt i x p g sg).b g raw.basis := by
  have eq:(signedAt i x p g sg).g=g:=by cases g <;> rfl
  unfold InputAt at h
  rwa [eq] at h

theorem stepInput (i b x p:Nat) (lo:15 ≤ i) (hi:i+15<512) (fixed:Fixed i) (good:Bounds x p)
    (raw v:State) (g sg:Bool) (domain:Domain i x p raw) (input:InputAt i (signedAt i x p g sg) raw)
    (small:min (unsigned i x p).u (unsigned i x p).v<2^b) :
    let next:=SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt i x p g sg))
    Domain (i+15) x p (endRaw i raw v) ∧ InputAt (i+15) (signedAt (i+15) x p next.1 next.2) (endRaw i raw v) := by
  exact ⟨advance i x p lo (Nat.le_of_lt hi) fixed good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw v domain,
    (advance_signed i b x p lo hi fixed good raw v domain g sg input small).2⟩

def Saved (i x p:Nat) (ports:Ports) (d:Bool) (out:State) := ∃row<63145,Chronology i x p row ∧ Kept ports d row out

structure At240 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 240 x p raw
  input:InputAt 240 (signedAt 240 x p g sg) raw
  cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (flagNeg 240 x p sg)
      (decide (farAt 136 240 x p)) (decide (farAt 136 240 x p ∧ 2^136≤(unsigned 240 x p).u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s)
  facts:PastFacts 10 ArchiveBoundary240.rawPorts 144 (unsigned 225 x p) pg ps
      (HighBankSum.cross (Leave225TrueMiddle.d (unsigned 225 x p))) s
  pastCanonical:signedAt 225 x p pg ps=WideReference.canonical 225 x p

def Ready240 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At240 d x p raw s g sg pg ps

structure At255 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 255 x p raw
  input:InputAt 255 (signedAt 255 x p g sg) raw
  cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (flagNeg 255 x p sg)
      (decide (farAt 129 255 x p)) (decide (farAt 129 255 x p ∧ 2^129≤(unsigned 255 x p).u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s)
  facts:PastFacts 11 ArchiveBoundary255.rawPorts 136 (unsigned 240 x p) pg ps
      (HighBankSum.cross (Leave240TrueMiddle.d (unsigned 240 x p))) s
  pastCanonical:signedAt 240 x p pg ps=WideReference.canonical 240 x p
  saved225:Saved 225 x p ArchiveBoundary240.codePorts d s

def Ready255 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At255 d x p raw s g sg pg ps

structure At270 (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain:Domain 270 x p raw
  input:InputAt 270 (signedAt 270 x p g sg) raw
  cut:PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (flagNeg 270 x p sg)
      (decide (farAt 121 270 x p)) (decide (farAt 121 270 x p ∧ 2^121≤(unsigned 270 x p).u))
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src s)
  records:physicalCells 12 s=SkywalkTrace.trace 15 (signedAt 255 x p pg ps)
  mode:s.basis 1701=decide (farAt 129 255 x p)
  side:s.basis 1702=(decide (farAt 129 255 x p) && StairArchiveTrace.afterFlags (decide ((unsigned 255 x p).v<(unsigned 255 x p).u)) ((physicalCells 12 s).take 5))
  cross:s.basis 1703=(decide (farAt 129 255 x p) && HighBankSum.cross (Leave255TrueMiddle.d (unsigned 255 x p)))
  pastCanonical:signedAt 255 x p pg ps=WideReference.canonical 255 x p
  saved225:Saved 225 x p ArchiveBoundary240.codePorts d s
  saved240:Saved 240 x p ArchiveBoundary255.codePorts d s

def Ready270 (d:Bool) (x p:Nat) (s:State) := ∃raw g sg pg ps,At270 d x p raw s g sg pg ps
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket


end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed
attribute [local irreducible] run measurementCount

def Checked (F R:Program) (pre post:State→Prop) := ∀s m,pre s →
  let out:=run F m s
  out.phase=s.phase ∧ post out ∧ ∀n,run R n out=s

theorem composition {F R F' R':Program} {A B C:State→Prop}
    (left:Checked F R A B) (right:Checked F' R' B C) : Checked (F++F') (R'++R) A C := by
  intro s m h
  obtain ⟨ph,mid,undo⟩:=left s m h
  obtain ⟨ph',post,undo'⟩:=right _ (m.drop (measurementCount F)) mid
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph'.trans ph,post,?_⟩
  intro n
  rw [run_append,run_take,undo',undo]

theorem pair {F R F' R':Program} {A B:State→Prop}
    (law:∀s m, A s →
      let first:=run F m s
      let out:=run F' (m.drop (measurementCount F)) first
      out.phase=s.phase ∧ B out ∧ (∀k,run R' k out=first) ∧ (∀k,run R k first=s)) :
    Checked (F++F') (R'++R) A B := by
  intro s m h
  obtain ⟨ph,post,inv,inv'⟩:=law s m h
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph,post,?_⟩
  intro n
  rw [run_append,run_take,inv,inv']

theorem cutPhase {lo hi:List (Wire×Wire)} {g n f u:Wire} {neg far long:Bool}
    {sig:Wire→Wire} {raw s:State} {pending:List Wire}
    (cut:PackedCut lo hi g n f u neg far long (pullState sig raw) (eraseSites pending s)) :
    s.phase=raw.phase := cut.phase

def Before (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p 225 raw.basis ∧ s=pullState (OB5.sig 224) raw

end ECDSAAdd.Entrant.StairPacket.StockWindowTicket


end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3200000
attribute [local irreducible] run body measurementCount leave225 leave225Inv NativePack225.firstWindow NativePack225.firstUnwind

private theorem physical (d:Bool) (x p:Nat) (good:Bounds x p) (s:State) (m n:List Bool)
    (pre:Before d x p s) :
    let v:=run (NativePack225.firstWindow d) m s
    let out:=run leave225 n v
    out.phase=s.phase ∧ Ready240 d x p out ∧ (∀k,run leave225Inv k out=v) ∧ (∀k,run (NativePack225.firstUnwind d) k v=s) := by
  obtain ⟨raw,stage,rfl⟩:=pre
  let s:=pullState (OB5.sig 224) raw
  let v:=run (NativePack225.firstWindow d) m s
  let out:=run leave225 n v
  let raw':=endRaw 225 raw v
  obtain ⟨g,sg,input,h,cut,facts⟩:=NativePack225.stock_endpoint d x p good raw m n stage
  let flags:=Leave225Admission.flags (unsigned 225 x p) g sg
  have dom:=initial 225 x p (by decide) d raw stage
  have carried:=stepInput 225 144 x p (by decide) (by decide) fixed225 good raw v g sg dom input h.small
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase 225 x p (by decide) good raw v dom)
  have back:=NativePack225.first_window d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage
  exact ⟨ph,⟨raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,unique_input input (fixed_input 225 x p (by decide) good raw dom)⟩,
    h.roundtrip n,back.2.2⟩

theorem step225 (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (NativePack225.firstWindow d++leave225) (leave225Inv++NativePack225.firstUnwind d) (Before d x p) (Ready240 d x p) := by
  apply pair (F:=NativePack225.firstWindow d) (F':=leave225) (R:=NativePack225.firstUnwind d) (R':=leave225Inv)
  intro s m h
  exact physical d x p good s m _ h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket


end
