import ECDSAAdd.Submission.Entrant.OneFlag
import ECDSAAdd.Submission.Entrant.NewFieldFrameOB5

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.FrontierReplay1591
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

structure Context (origin : BasisState) : Prop where
  hn : (skywalkSharedWires base).Nodup
  ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base
  hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base
  hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)
  hg0 : origin (base 2409)=false
  hs0 : origin (base 2410)=false
  env : Env base origin
  legal : NewHistory5.RawLegal base 102 origin
  parity : origin (base 2312)=false

def rawReplay (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then
      OneFlagCell.cell true base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2++rawReplay true ls
    else rawReplay false ls++
      OneFlagCell.cell false base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2

def body (divide : Bool) (j : Nat) : Program := rawReplay divide (Replay5.letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  NewHistory5.decode base (5*j)++body divide j++NewHistory5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstSwap : Program := OneFlagCell.selectSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2
def firstSwapM : Program := OneFlagCell.selectMSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def firstBody (divide : Bool) : Program :=
  if divide then firstSwap++rawReplay true Replay5.restLetters
  else rawReplay false Replay5.restLetters++firstSwapM

def baseFirstPacket (divide : Bool) : Program :=
  NewHistory5.decode base 0++firstBody divide++NewHistory5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  Q6EndpointCell.endpoint divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def logicalReplay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplay divide)


def fieldSites : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset

def readSites (start : Nat) : Finset Wire := fieldSites ∪ {base 2400,base 2410} ∪
  wires (NewHistory5.encode base start)

theorem raw_support (divide : Bool) (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (hi : fieldSites⊆W) (hb : base 2400∈W) (he : base 2410∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) : wires (rawReplay divide ls)⊆W := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := OneFlagCell.support divide base (base 2400) l.1.1 l.1.2 (base 2409)
      l.2.1 l.2.2 W hi hb (controls l (by simp)).1 (controls l (by simp)).2
    have rest := ih (fun k hk => controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.union_subset_iff] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆readSites (5*j) := by
  simpa only [readSites,OneFlagReplay.readSites,NewHistory5.encode_support_eq] using
    OneFlagReplay.body_support divide j hj

theorem readSites_sub (start : Nat) : readSites start⊆
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) start ∪ {base 2312} := by
  intro q hq
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem body_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (body_support divide j hj).trans (readSites_sub (5*j))

theorem firstBody_support (divide : Bool) : wires (firstBody divide)⊆readSites 0 := by
  simpa only [readSites,OneFlagReplay.readSites,NewHistory5.encode_support_eq] using
    OneFlagReplay.firstBody_support divide

theorem firstBody_read_support (divide : Bool) :
    wires (firstBody divide)⊆NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  (firstBody_support divide).trans (readSites_sub 0)

theorem rawEnd_support (divide : Bool) : wires (rawEnd divide)⊆fieldSites ∪ {base 2400,base 510} := by
  apply Q6EndpointCell.endpoint_support divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  · exact Finset.subset_union_left
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)

theorem rawEnd_read_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2312,base 2400,base 510} := by
  intro q hq
  rcases Finset.mem_union.mp (rawEnd_support divide hq) with h|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ (by simp [h])
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Finset.mem_union_right _ (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (NewHistory5.allEncode base 102)) (wires (rawEnd divide)) := by
  rw [NewHistory5.allEncode_support_eq]
  exact OneFlagReplay.rawEnd_disjoint divide hn hp

private theorem q7part2_letter_layout (origin : BasisState) (ctx : Context origin)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (l : MixedTranscriptLetter) (hl : l∈ls) :
    BalancedTranscriptLayout (Q6EndpointCell.ports base (base 2409))
      (base 2400) l.1.1 l.1.2 (base 2410) :=
  Q6EndpointCell.ports_transcript base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) (hf l hl) ctx.ho)
    (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

theorem raw_frame (divide : Bool) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawReplay divide ls)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).2)) := by
  have clean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  induction ls generalizing X Y with
  | nil =>
    intro s m h
    cases divide <;> simpa only [rawReplay,directionalPayload,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,mixedTranscriptControls,List.map_nil,skywalkPayloadReplay,
      skywalkPayloadReplayInverse,run] using And.intro (Eq.refl s.phase) h
  | cons l ls ih =>
    have layout := q7part2_letter_layout origin ctx (l::ls) hf l (by simp)
    have tailLayout := fun k hk => hf k (List.mem_cons_of_mem l hk)
    cases divide
    · let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) ls) (X,Y)
      have rest := ih tailLayout X Y
      have head := OneFlagCell.cell_frame_legacy false base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean Q.1 Q.2
      simpa only [rawReplay,Bool.false_eq_true,if_false,directionalPayload,Bool.not_false,if_true,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using rest.seq head
    · let Q := skywalkPayloadCell (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1)
        (mixedTranscriptBit origin (base 2400) l.1.2 l.2.2) (X,Y)
      have head := OneFlagCell.cell_frame_legacy true base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean X Y
      have rest := ih tailLayout Q.1 Q.2
      simpa only [rawReplay,if_true,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using head.seq rest

private theorem q7part2_rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem q7part2_first_layout (origin : BasisState) (ctx : Context origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have h := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at h
  exact h

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have raw := raw_frame divide (Replay5.letters j) (Replay5.letters_layouts ctx.hf j hj) origin ctx X Y
  have fresh := NewFieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp j hj origin X Y _ _ _ (body_read_support divide j hj) raw s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.groupsPayload divide origin j n (X,Y)).1
        (Replay5.groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun V t => NewHistory5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk origin ctx V.1 V.2 t records h⟩)
    j n bound (X,Y) s m input
  exact result.2


theorem base_sign_nd : (base 2409::(Q6EndpointCell.ports base (base 2409)).r++
    (Q6EndpointCell.ports base (base 2409)).y).Nodup := by
  have away : base 2409∉Q6EndpointCell.ids.map base := by
    intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have bound := Q6EndpointCell.ids_bound i hi
    have := base_injective he
    omega
  have hn := Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective away
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil,
    Q6EndpointCell.ports_sign] at h ⊢
  omega

theorem firstBody_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.firstPayload divide origin (X,Y)).1)
        (centerWord (Replay5.firstPayload divide origin (X,Y)).2)) := by
  let S := mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  have nl := Q6EndpointCell.ports_transcript base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) ctx.hn (q7part2_first_layout origin ctx) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hb := nl.outside (base 2400) (by simp)
  have hs := nl.outside (base 1028) (by simp)
  have hf := nl.outside (base 2409) (by simp [Q6EndpointCell.ports_sign])
  have swap := OneFlagCell.selectSwap_frame base (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0
  cases divide
  · let V := directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X,Y)
    have zero : (if S then V.1 else V.2)=0 := by
      have h := hz rfl
      have k : ∀ (b : Bool) (p : Fp×Fp), (if b then (p.2,p.1) else p).2=(if b then p.1 else p.2) := by
        intro b p; cases b <;> rfl
      simp only [Replay5.firstPayload,Bool.false_eq_true,if_false,k] at h
      exact h
    have swapM := OneFlagCell.selectMSwap_frame base (base 2400) (base 1028) (base 2409)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0 V.1 V.2 zero
    have rest := raw_frame false Replay5.restLetters (q7part2_rest_layout ctx.hf) origin ctx X Y
    have out := rest.seq swapM
    cases hS : S <;> simpa only [firstBody,firstSwapM,Replay5.firstPayload,Bool.false_eq_true,
      if_false,Bool.not_false,if_true,S,hS,V] using out
  · have out := (swap X Y).seq (raw_frame true Replay5.restLetters (q7part2_rest_layout ctx.hf)
      origin ctx (if S then Y else X) (if S then X else Y))
    cases hS : S <;> simpa only [firstBody,firstSwap,Replay5.firstPayload,if_true,Bool.not_true,
      Bool.false_eq_true,if_false,S,hS] using out

theorem firstPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.firstPayload divide origin (X,Y)).1
        (Replay5.firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := NewFieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin X Y _ _ _ (firstBody_read_support divide)
    (firstBody_frame divide origin ctx X Y hz) s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) (baseFirstPacket divide)
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  exact Q6EndpointReplay.rawEnd_frame divide origin oldctx X Y hend

theorem endPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := NewHistory5.encoded_disjoint_step base (base 2409)
    (skywalkShared_integer_nodup base ctx.hn) origin X Y _ _ _ (rawEnd_disjoint divide ctx.hn ctx.hp)
    (rawEnd_frame divide origin ctx X Y hend) s m input
  have eq := Replay5.placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (NewHistory5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => NewHistory5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ NewHistory5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false origin ctx Y Y (fun e => absurd e (by decide)) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  NewFieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  NewFieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame origin ctx x hx0 hx trace Y) s m input


















end ECDSAAdd.Entrant.FrontierReplay1591
