import ECDSAAdd.Submission.Entrant.ShadowPark390
import ECDSAAdd.Submission.Entrant.ShadowLeaveFacts

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 390
def P:=TickRanges.tick base 390
def Q:=W.ReverseCarry.compactReceiverTick base 390
def physP:=renameProgram (OB5.sig 390) P
def physQ:=renameProgram (OB5.sig 390) Q
theorem supports : wires P⊆L.wires.toFinset ∧ wires Q⊆L.wires.toFinset :=
  ⟨(TickRanges.tick_support base 390 (by decide) base_pool_nodup).trans
    (W.repairedTick_support base 390 (by decide) base_pool_nodup),
    W.ReverseCarry.compactReceiverTick_support base 390 (by decide) base_pool_nodup⟩
theorem physical_free (R:Program) (sub:wires R⊆L.wires.toFinset) (q:Wire)
    (off:OB5.sig 390 q∉L.wires) : q∉wires (renameProgram (OB5.sig 390) R) := by
  rw [JointForward1588.wires_rename_image]
  intro h
  obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
  rw [OB5.sig_invol 390 (by decide)] at off
  exact off (List.mem_toFinset.mp (sub mem))
theorem spared : ∀q∈ParkEndpoint3907.dst,OB5.sig 390 q∉L.wires := by decide +kernel
theorem stashP : ∀q∈ParkEndpoint3907.dst,q∉wires physP := fun q hit=>physical_free P supports.1 q (spared q hit)
theorem stashQ : ∀q∈ParkEndpoint3907.dst,q∉wires physQ := fun q hit=>physical_free Q supports.2 q (spared q hit)
end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic Secp256k1 MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem local_reference (i:Nat) (hi:i<512) (d:Bool) (x:Nat) (original:State)
    (stage:Rolling1588.Integer.Stage base d x p i original.basis) :
    ∃raw:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
      ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset, original.basis q=raw.basis q := by
  obtain ⟨raw,hraw,eq⟩:=stage
  refine ⟨raw,hraw,fun q hq=>?_⟩
  rw [eq]
  exact run_preserves_outside _ _ _ q (fun used=>Finset.disjoint_left.mp
    (Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i i (le_refl _) hi) used hq)

theorem undo_on_domain (w:Nat→Wire) (hn:(skywalkPoolWires w).Nodup) (x p i:Nat)
    (hi:i<512) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hgap:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p)
    (t raw:State) (a b:List Bool)
    (hraw:W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis)
    (read:∀q∈(W.compactSkywalkTickLayout w i).wires,t.basis q=raw.basis q) :
    run (W.ReverseCarry.compactReceiverTick w i) b (run (W.compactSkywalkTick w i) a t)=t:=by
  have loc := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw hraw
  have hh : t.basis (W.compactSkywalkTickLayout w i).history=false := by
    rw [read _ (by simp [SkywalkIntegerLayout.wires])]
    exact loc.2.2.2.2.1
  have tops : W.trimTick i →
      t.basis (w (i+W.compactSkywalkTickPreWidth i-1))=t.basis (w (i+W.compactSkywalkTickPreWidth i-2)) ∧
      t.basis (w (770+W.compactSkywalkTickPreWidth i-1))=t.basis (w (770+W.compactSkywalkTickPreWidth i-2)) := by
    intro htr
    have st := W.compactSkywalkStage_tops w hn x p i hp0 hx0 hpo hp hgap hx hc hi htr raw hraw
    have split := W.compactSkywalkTick_aMid_split w i hi
    have mem (q : Wire) (h : q∈(W.compactSkywalkTickLayout w i).aMid ∨ q=(W.compactSkywalkTickLayout w i).aSign ∨
        q∈(W.compactSkywalkTickLayout w i).bMid ∨ q=(W.compactSkywalkTickLayout w i).bSign) :
        q∈(W.compactSkywalkTickLayout w i).wires := by
      simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
        List.mem_cons,List.mem_append]
      itauto
    have ra := read _ (mem _ (Or.inr (Or.inl rfl)))
    have rb := read _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))
    have la := read (w (i+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inl (by rw [split.1]; simp)))
    have lb := read (w (770+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inr (Or.inr (Or.inl (by rw [split.2]; simp)))))
    simp only [W.compactSkywalkTickLayout] at ra rb
    exact ⟨by rw [ra,la]; exact st.1,by rw [rb,lb]; exact st.2⟩
  have clean : regValue (W.compactSkywalkTickLayout w i).carry t.basis=0 := by
    rw [regValue_congr _ t.basis raw.basis (by
      intro q hq
      exact read q (by simp only [SkywalkIntegerLayout.wires,List.mem_append,List.mem_cons]; itauto))]
    exact loc.2.2.2.2.2
  exact W.ReverseCarry.compactReceiverTick_roundtrip w i hi hn t a b hh clean tops

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def canonical:= W.compactSkywalkTick base 390
def Reads (a b:State) := ∀q∈L.wires.toFinset,a.basis q=b.basis q
theorem apply_old (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) (a b:List Bool) :
    run P a actual=run canonical b actual:=by
  obtain ⟨w,sw,agree⟩:=Rolling1588.Integer.old_stage_local base d base_pool_nodup x p 390 (by decide) original stage
  have old:=TickRanges.tick_eq5 x hx0 hx 390 (by decide) w a sw
  have same:=Stack5.local_replace P (W.repairedTick base 390) L.wires.toFinset supports.1
    (W.repairedTick_support base 390 (by decide) base_pool_nodup) original w a a agree old
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have reference:=Rolling1588.Integer.repaired_eq base d base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) original a b stage
  exact Stack5.local_replace P canonical L.wires.toFinset supports.1
    (W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) actual original a b read (same.trans reference)

theorem compact_undo (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) (a b:List Bool) :
    run Q b (run canonical a actual)=actual:=by
  obtain ⟨ref,stock,agree⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  exact undo_on_domain base base_pool_nodup x p 390 (by decide) hp0 hx0 hpo hp gap hx cop actual ref a b stock
    (fun q h=>(read _ (List.mem_toFinset.mpr h)).trans (agree _ (List.mem_toFinset.mpr h)))


end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem physical (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State)
    (read:Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (m:List Bool) :
    let start:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
    let out:=run physP m start
    out=ParkEndpoint3907.stash tags (pullState (OB5.sig 390) (run canonical [] raw)) ∧
      ∀t,run physQ t out=start := by
  have pre:pullState (OB5.sig 389) raw=pullState (OB5.sig 390) raw:=
    OB5.pull_step 390 (by decide) raw hist (fun _=>swapSlot)
  have result:run physP m (ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw))=
      ParkEndpoint3907.stash tags (pullState (OB5.sig 390) (run canonical [] raw)):=by
    rw [ParkEndpoint3907.commutes _ stashP,pre,physP,OB5.run_rename _ (by decide),apply_old d x hx0 hx raw original read stage m []]
  refine ⟨result,?_⟩
  intro t
  rw [result,ParkEndpoint3907.commutes _ stashQ,physQ,OB5.run_rename _ (by decide),compact_undo d x hx0 hx raw original read stage,←pre]

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary3907
theorem load_cover (d:Bool) : wires ((Shadow7.exitLoadP 390) d) ⊆ rawPortsList.toFinset := by
  rw [load_program,wires_append,Finset.union_subset_iff]
  constructor
  · rw [placed,renameProgram_support]
    intro q member
    obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp (sub (op true d) used)
    have small:w<155:=by cases d <;> exact bound
    have inside:∀j:Fin 155,loadMap j∈rawPortsList:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact List.mem_toFinset.mpr (inside ⟨w,small⟩)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ArchiveBoundary3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 390 q∉L.wires ∨ q=405
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
theorem observes (q:Wire) (h:readOnly q) (s:State) (m:List Bool) (prev:(run physP m s).basis 405=s.basis 405) : (run physP m s).basis q=s.basis q := by
  rcases h with h|rfl
  · exact run_preserves_outside _ _ _ _ (physical_free P supports.1 _ h)
  · exact prev
theorem oldPrefix : ∀i,readOnly (NativePack3907.history i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick3907.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem oldBank : ∀i:Fin 23,readOnly (ArchiveBoundary3907.rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick3907.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
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
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) :
    ∃ref:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 390 ref.basis ∧
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 391 (run canonical [] ref).basis ∧
      Reads raw ref ∧ Reads (run canonical [] raw) (run canonical [] ref) := by
  obtain ⟨ref,hs,agree⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have r:Reads raw ref:=fun q h=>(read q h).trans (agree q h)
  exact ⟨ref,hs,(W.compactSkywalkStageStep base base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).2,r,
    canonical_reads 390 (by decide) ref raw r []⟩

theorem pastG (i j:Nat) (hi:i≤512) (hj:j < i) (r:SkywalkRails.State) (b:BasisState)
    (hs:W.CompactSkywalkStage base r i b) :
    b (base j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 :=
  (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.1 j hj).1

theorem full_carry (i:Nat) (hi:i≤512) (r:SkywalkRails.State) (b:BasisState) (hs:W.CompactSkywalkStage base r i b) :
    ∀q∈wireBlock base 1540 257,b q=false :=
  (regValue_zero _ _).mp (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.2.2.1)

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
theorem carry_member (i:Nat) (q:Wire) (mem:q∈(W.compactSkywalkTickLayout base i).carry) :
    q∈(W.compactSkywalkTickLayout base i).wires.toFinset := List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires,mem])
theorem previous_member (i:Nat) : (W.compactSkywalkTickLayout base i).previous∈(W.compactSkywalkTickLayout base i).wires.toFinset :=
  List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires])
theorem scratch_lanes : ∀k:Fin 134,k.val+390<512 → 1556+k.val∈L.carry ∧ 1556+k.val∈wireBlock base 1540 257 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
/-- window390: the scratch hosts `790+k` (the ports beyond the stock carry) are no wires of the end tick. -/
theorem host_lanes : ∀k:Fin 134,512≤k.val+390 → (790+k.val:Wire)∉L.wires.toFinset := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem after_cells (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) :
    (run canonical [] raw).basis 405=raw.basis 405 ∧
    ∀k:Fin 134,(run canonical [] raw).basis (Shadow7.scratchX 390 k.val)=false := by
  obtain ⟨ref,old,next,pre,post⟩:=after_reference d x hx0 hx raw original read stage
  have prev:405∈L.wires.toFinset:=previous_member 390
  have a:=pastG 390 389 (by decide) (by decide) _ _ old
  have b:=pastG 391 389 (by decide) (by decide) _ _ next
  exact ⟨(post _ prev).trans (b.trans (a.symm.trans (pre _ prev).symm)),
    fun k=>by
      have _kl:=k.isLt
      by_cases hk:k.val+390<512
      · rw [show Shadow7.scratchX 390 k.val = 1556+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 390 ≤ 369), if_pos (by omega)]]
        exact (post _ (carry_member 390 _ (scratch_lanes k hk).1)).trans (full_carry 391 (by decide) _ _ next _ (scratch_lanes k hk).2)
      · rw [show Shadow7.scratchX 390 k.val = 790+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 390 ≤ 369), if_neg (by omega)]
          change 908+4+(1556+k.val+390-2068) = 790+k.val
          omega,
          run_preserves_outside canonical [] raw _ (fun used=>host_lanes k (by omega)
            ((W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) used))]
        exact hosts k (by omega)⟩

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick3907
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary3907 ParkEndpoint3907
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem no_phase (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis) : (run canonical [] raw).phase=raw.phase := by
  obtain ⟨ref,hs,ag⟩:=local_reference 390 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have step:=(W.compactSkywalkStageStep base base_pool_nodup x p 390 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).1
  have inc:=(run_local_increment canonical raw ref [] (fun q h=>by
    have mem:=(W.compactSkywalkTick_support base 390 (by decide) base_pool_nodup) h
    exact (read q mem).trans (ag q mem))).1
  change (run canonical [] ref).phase=ref.phase at step
  rw [step,Bool.xor_self] at inc
  cases h:(run canonical [] raw).phase <;> cases k:raw.phase <;> simp_all

theorem scratch_table : ∀i:Fin 157,23≤ i.val →
    rawPorts i∉dst ∧ OB5.sig 390 (rawPorts i)=Shadow7.scratchX 390 (i.val-23) ∧ ∀v:Fin 10,rawPorts i≠NativePack3907.history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem coordinate (s raw:State) : (stash s (pullState (OB5.sig 390) raw)).basis 405=raw.basis 405 ∧
    (stash s (pullState (OB5.sig 389) raw)).basis 405=raw.basis 405 := ⟨rfl,rfl⟩

theorem stash_slots (raw after tags:State) (phase:after.phase=raw.phase) (same:after.basis 405=raw.basis 405)
    (zero:∀k:Fin 134,after.basis (Shadow7.scratchX 390 k.val)=false) :
    let start:=stash tags (pullState (OB5.sig 389) raw)
    let out:=stash tags (pullState (OB5.sig 390) after)
    out.phase=start.phase ∧ out.basis 405=start.basis 405 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  refine ⟨phase,(coordinate _ _).1.trans (same.trans (coordinate _ _).2.symm),?_⟩
  intro i hi
  have ⟨off,eq,_⟩:=scratch_table i hi
  simp only [stash,if_neg off]
  exact (congrArg after.basis eq).trans (zero ⟨i.val-23,by have h:=i.isLt;omega⟩)

theorem exposed (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=stash tags (pullState (OB5.sig 389) raw)
    let out:=run physP m start
    out.phase=start.phase ∧ out.basis 405=start.basis 405 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  have out:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).1
  have bits:=after_cells d x hx0 hx raw original read stage hosts
  dsimp only
  rw [out]
  exact stash_slots raw (run canonical [] raw) tags (no_phase d x hx0 hx raw original read stage) bits.1 bits.2

end ECDSAAdd.Entrant.StairPacket.EndTick3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed IntegerPacket RailPair Portal390Flag7 ArchiveBoundary3907
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1633 ∧ q≠1631 ∧ q≠1632 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
theorem past_sites : ∀r:Fin 15,ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).a0) ∧
    ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).history) := by ((try unfold ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907.ordinary); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem earlier (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u
    (pullState (OB5.sig 389) raw) (eraseSites src s)) (q:Wire) (clean:ordinary q) :
    (stash s (pullState (OB5.sig 389) raw)).basis q=s.basis q := by
  obtain ⟨hs,hd,hn,hf,hu,hh⟩:=clean
  have eq:=cut.unchanged _ hn hf hu hh
  simpa [stash,eraseSites,hs,hd] using eq.symm

theorem past_cells (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u
    (pullState (OB5.sig 389) raw) (eraseSites src s)) :
    Shadow7.physicalCells sourceIdx (stash s (pullState (OB5.sig 389) raw))=Shadow7.physicalCells sourceIdx s := by
  rw [Shadow7.physicalCells_eq, Shadow7.physicalCells_eq]
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (earlier _ _ _ _ _ cut _ (past_sites r).1) (earlier _ _ _ _ _ cut _ (past_sites r).2)
theorem tag_address (s other:State) :
    (stash s other).basis (rawPorts 20)=s.basis 1634 ∧
    (stash s other).basis (rawPorts 21)=s.basis 1635 ∧
    (stash s other).basis (rawPorts 22)=s.basis 1636:=⟨rfl,rfl,rfl⟩
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary3907 ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

theorem pack_support (d:Bool) : wires (program d) ⊆ ((List.finRange 10).map history).toFinset := by cases d <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem outside (d:Bool) (q:Wire) (no:∀v:Fin 10,q≠history v) (m:List Bool) (s:State) :
    (run (program d) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro mem
  obtain ⟨v,_,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp (pack_support d mem))
  exact no v eq.symm
theorem bank_out : ∀q:Fin 23,∀v:Fin 10,rawPorts ⟨q,Nat.lt_trans q.isLt (by decide : 23<157)⟩≠history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem archive_ready (d:Bool) (start tick:State) (m:List Bool) (past:SkywalkNat.State) (g sign cross:Bool)
    (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past) (prior:PastFacts sourceIdx rawPorts 62 past g sign cross start)
    (keptFive:∀i,tick.basis (history i)=start.basis (history i))
    (bank:∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩))
    (scratch:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) :
    MeasuredCodec5.legalAt history tick.basis ∧ ∃row<63145,ArchivePortAction.Frame rawPorts raw row (run (program d) m tick) := by
  let cells:=Shadow7.physicalCells sourceIdx start
  let f:=decide (Shadow.far 62 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  let out:=run (program d) m tick
  have legal:StairArchiveRaw.legal (Shadow7.physicalCells sourceIdx start):=by rw [Shadow7.physicalCells_eq,prior.records];exact legal_signed 15 past g sign (by omega) odd
  have same (i:Fin 23) : out.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=
      start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩):=
    (outside d _ (bank_out i) m tick).trans (bank i)
  have tags:out.basis (rawPorts 20)=f ∧ out.basis (rawPorts 21)=u ∧ out.basis (rawPorts 22)=c:=
    ⟨(same 20).trans prior.far,by simpa only [u,f,cells,Shadow7.physicalCells_eq] using (same 21).trans prior.suffix,(same 22).trans prior.crossed⟩
  have hw:∀i:Fin 157,i.val<23 → out.basis (rawPorts i)=data i :=
    observed start out (fun q=>same ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  have fresh (i:Fin 157) (hi:23≤ i.val) : out.basis (rawPorts i)=false :=
    (outside d _ (EndTick3907.scratch_table i hi).2.2 m tick).trans (scratch i hi)
  obtain ⟨row,limit,matchRow⟩:=interrupted_row_shadow7 62 past small odd g sign cross cells
    (((Shadow7.physicalCells_eq _ _).trans prior.records).trans (true_records_shadow7 _ _ small odd _ _).symm)
  exact ⟨legal_prefix _ _ legal keptFive,row,limit,starting_frame rawPorts out row data matchRow hw fresh⟩

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
def endSlice (d:Bool) := EndTick3907.physP ++ (program d ++ (Shadow7.exitLoadP 390) d)
def endUndo (d:Bool) := (Shadow7.exitRestoreP 390) d ++ (reverse d ++ EndTick3907.physQ)
structure Transition (inverse:Program) (s tick:State) : Prop where
  phase : tick.phase=s.phase
  keptFive : ∀i,tick.basis (history i)=s.basis (history i)
  keptBank : ∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)
  scratch : ∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false
  undo : ∀n,run inverse n tick=s

abbrev TickStep:=Transition EndTick3907.physQ

theorem tick_intro (s tick:State) (ph:tick.phase=s.phase)
    (obs:∀q,EndTick3907.readOnly q → tick.basis q=s.basis q)
    (zero:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) (undo:∀m,run EndTick3907.physQ m tick=s) :
    TickStep s tick :=
  ⟨ph,fun i=>obs _ (EndTick3907.oldPrefix i),fun i=>obs _ (EndTick3907.oldBank i),zero,undo⟩

theorem observe_tick (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:EndTick3907.Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
    TickStep start (run EndTick3907.physP m start) := by
  let s:=ParkEndpoint3907.stash tags (pullState (OB5.sig 389) raw)
  have h:=EndTick3907.exposed d x hx0 hx raw original tags read stage hist swapSlot hosts m
  have u:=(EndTick3907.physical d x hx0 hx raw original tags read stage hist swapSlot m).2
  exact tick_intro s (run EndTick3907.physP m s) h.1 (fun q hq=>EndTick3907.observes q hq s m h.2.1) h.2.2 u

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

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def lastWindow (d:Bool) := (Shadow7.parkP 390) ++ ((Shadow7.portalInvP 390) ++ endSlice d)
def lastUnwind (d:Bool) := endUndo d ++ ((Shadow7.portalP 390) ++ (Shadow7.parkInvP 390))

theorem after_park (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u (pullState (OB5.sig 389) raw) (eraseSites src s))
    (past:SkywalkNat.State) (G S cross:Bool)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode G S past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (orientation:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    PastFacts sourceIdx rawPorts 62 past G S cross (stash s (pullState (OB5.sig 389) raw)) := by
  have cells:=past_cells raw s n f u cut
  have tag:=tag_address s (pullState (OB5.sig 389) raw)
  refine ⟨(Shadow7.physicalCells_eq _ _).symm.trans (cells.trans records),tag.1.trans mode,?_,tag.2.2.trans flipped⟩
  rw [←Shadow7.physicalCells_eq, cells];exact tag.2.1.trans orientation

end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
theorem empty_from_cut (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 n f u (pullState (OB5.sig 389) raw) (eraseSites src s))
    (source:∀q∈dst,(pullState (OB5.sig 389) raw).basis q=false) : ∀q∈dst,s.basis q=false:=by
  have regular:∀q∈dst,q∉src ∧ q≠1633 ∧ q≠1631 ∧ q≠1632 ∧ q∉RailPair.sites hiPairs:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩:=regular _ member
  have eq:=cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source _ member)
end ECDSAAdd.Entrant.StairPacket.NativePack3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem terminal3907 (d:Bool) (x:Nat) (s:State) (dom:Domain 390 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 390 ref.basis ∧ EndTick3907.Reads s ref ∧
    s.basis (base (1028+390))=false ∧ s.basis (base (2053-390))=false ∧
    (∀q∈ParkEndpoint3907.dst,(pullState (OB5.sig 389) s).basis q=false) ∧
    ∀k:Fin 134,512≤k.val+390 → s.basis (790+k.val)=false := by
  obtain ⟨ref,stage,link⟩:=leaves_reference 390 x p (by decide) d s dom
  have bounds:∀q∈ParkEndpoint3907.dst,390+16<OB5.sig 389 q ∧ OB5.sig 389 q<1044:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) dom,?_,?_,?_⟩
  · exact (link.2 _ (outside_above (by decide))).trans ((Rolling1588.Integer.stage_zero d x 390 (by decide) _ stage).2 (by decide))
  · intro q hit
    exact (link.2 _ (outside_between (bounds _ hit).1 (bounds _ hit).2)).trans (ParkEndpoint3907.clear_dest d x p ref stage q hit)
  · intro k hk
    have _kl := k.isLt
    have released : ∀ i : Fin 134, 512 ≤ i.val+390 →
        790+i.val ∈ (W.compactSkywalkSignPoolB base 390).released := by decide +kernel
    exact (link.2 _ (outside_between (by omega) (by omega))).trans
      (ParkEndpoint3907.dormant 390 d x p ref _ stage
        (ParkEndpoint3907.above_history 390 (by decide) d _ (by omega) (by omega)) (released k hk))
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack3907
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary3907
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary3907 ParkEndpoint3907 Portal390Flag7 Secp256k1 SkywalkRails StairArchiveTrace
theorem matched_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past)
    (prior:PastFacts sourceIdx rawPorts 62 past G S cross s) :
    let out:=run (p ++ (program d ++ (Shadow7.exitLoadP 390) d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run ((Shadow7.exitRestoreP 390) d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) ((Shadow7.exitLoadP 390) d) ((Shadow7.exitRestoreP 390) d)
    (reverse d) q s m (fun out=>∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run ((Shadow7.exitLoadP 390) d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem matched_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick3907.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 62 15 past)
    (prior:PastFacts sourceIdx rawPorts 62 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  matched_generic EndTick3907.physP EndTick3907.physQ d s m step past G S cross odd small prior
theorem matched_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick3907.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 390 original.basis)
    (hist:raw.basis (base (1028+390))=false) (swapSlot:raw.basis (base (2053-390))=false)
    (hosts:∀k:Fin 134,512≤k.val+390 → raw.basis (790+k.val)=false)
    (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick3907.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative S z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)) (pullState (OB5.sig 389) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 62 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (angle:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount (Shadow7.parkP 390))
  let one:=run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)
  let tape:=n.drop (measurementCount (Shadow7.portalInvP 390))
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot hosts tape
  have eqOne:one=stash s (pullState (OB5.sig 389) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 62 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick3907.physP tape one):=by rw [eqOne];exact tick
  have body:=matched_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem matched_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 390 x p raw) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick3907.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative S z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)) (pullState (OB5.sig 389) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 62 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1634=decide (Shadow.far 62 15 past))
    (angle:s.basis 1635=(decide (Shadow.far 62 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1636=(decide (Shadow.far 62 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty,hosts⟩:=WideReference.terminal3907 d x raw domain
  exact matched_last d x hx0 hx raw ref s m read stage history swapSlot hosts z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack3907

end
