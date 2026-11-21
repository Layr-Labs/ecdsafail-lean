import ECDSAAdd.Submission.Entrant.Extension270Core

open ECDSAAdd.Entrant.StairPacket.Extension270
-- Insert after Window and BoundaryPrograms. No change to the stock reference.
namespace ECDSAAdd.Entrant.StairPacket.Enter285
def lowerPairs : List (Wire×Wire) := (List.range' 431 3).zip (List.range' 916 3)
def upperPairs : List (Wire×Wire) := (List.range' 434 95).zip (List.range' 919 95)
def pending : List Wire := [1694,1695,1696]
end ECDSAAdd.Entrant.StairPacket.Enter285

namespace ECDSAAdd.Entrant.StairPacket.Leave270Reference
open Arithmetic MappedCompressed WideReference IntegerPacket SkywalkRails
open ECDSAAdd.Entrant.StairPacket.Extension270
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run SkywalkNat.step

-- At this cut the OB5 map reflects part of the old history into 1800..1812.
def historySites : List Wire := (WideReference.sites 270).map (OB5.sig 284)
def reframe (wide history : State) : State :=
  ⟨wide.phase,fun q=>if q∈WideReference.sites 270 then history.basis (OB5.sig 284 q) else wide.basis q⟩
def endRaw (raw history : State) : State := reframe (run (span 270 15) [] raw) history
def origin (raw history : State) : State := pullState (OB5.sig 284) (endRaw raw history)

theorem historySites_shape : historySites =
    [271,1299,272,1300,273,1812,274,1811,275,1810,276,1809,277,1808,
     278,1807,279,1806,280,1805,281,1804,282,1803,283,1802,284,1801,285,1800] := by
  decide +kernel

theorem mem_historySites (q : Wire) : q∈historySites ↔ OB5.sig 284 q∈WideReference.sites 270 := by
  constructor
  · rintro h
    obtain ⟨r,hr,eq⟩ := List.mem_map.mp h
    have same := congrArg (OB5.sig 284) eq
    rw [OB5.sig_invol 284 (by decide)] at same
    exact same ▸ hr
  · intro h
    exact List.mem_map.mpr ⟨OB5.sig 284 q,h,OB5.sig_invol 284 (by decide) q⟩

theorem reframe_read (wide history : State) (q : Wire) :
    (pullState (OB5.sig 284) (reframe wide history)).basis q=
      if q∈historySites then history.basis q else wide.basis (OB5.sig 284 q) := by
  change (if OB5.sig 284 q∈WideReference.sites 270 then history.basis (OB5.sig 284 (OB5.sig 284 q)) else _)=_
  rw [OB5.sig_invol 284 (by decide)]
  by_cases h:q∈historySites
  · rw [if_pos ((mem_historySites q).mp h),if_pos h]
  · rw [if_neg (fun a=>h ((mem_historySites q).mpr a)),if_neg h]

theorem inside (raw history : State) (q : Wire) (h : q∈historySites) :
    (origin raw history).basis q=history.basis q :=
  (reframe_read (run (span 270 15) [] raw) history q).trans (if_pos h)

theorem outside (raw history : State) (q : Wire) (h : q∉historySites) :
    (origin raw history).basis q=(run (span 270 15) [] raw).basis (OB5.sig 284 q) :=
  (reframe_read (run (span 270 15) [] raw) history q).trans (if_neg h)

theorem outside_stock_mask (raw history : State) (q : Wire) (h : q∉historySites) :
    (origin raw history).basis q=(run (span 270 15) [] raw).basis (OB5.sig (270+14) q) :=
  (outside raw history q h).trans
    (congrArg (run (span 270 15) [] raw).basis (show OB5.sig 284 q=OB5.sig (270+14) q from rfl))

theorem endpoint (raw history : State) :
    pullState (OB5.sig 284) (endRaw raw history)=origin raw history := rfl

theorem reframe_coherent (wide reference history : State) (same : Coherent 285 wide reference) :
    Coherent 285 (reframe wide history) reference := by
  refine ⟨same.1,?_⟩
  intro q off
  have notOld : q∉WideReference.sites 270 := fun h=>off (past_slot 270 q (by decide) h)
  change (if q∈WideReference.sites 270 then history.basis (OB5.sig 284 q) else wide.basis q)=_
  rw [if_neg notOld]
  exact same.2 q off

theorem advance (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) : Domain 285 x p (endRaw raw history) := by
  obtain ⟨ref,same,valid⟩ := domain
  have c := coherent_span 270 15 (by decide) raw ref same []
  exact ⟨run (span 270 15) [] ref,reframe_coherent _ _ history c,
    full_span 270 15 x p (by decide) good.positive good.nonzero good.odd
      good.cap good.gap good.small good.coprime ref [] valid⟩

theorem advance_signed (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) (G S : Bool)
    (input : InputAt 270 (encode G S (unsigned 270 x p).u (unsigned 270 x p).v) raw)
    (small : min (unsigned 270 x p).u (unsigned 270 x p).v<2^121) :
    let flags := SharedSigned.flags G S (SkywalkTrace.trace 15 (encode G S (unsigned 270 x p).u (unsigned 270 x p).v))
    InputAt 285 (encode flags.1 flags.2 (unsigned 285 x p).u (unsigned 285 x p).v) (endRaw raw history) := by
  let z := unsigned 270 x p
  have odd : z.v%2=1 := (SkywalkNat.iter_valid 270 (SkywalkNat.init x p) good.positive good.odd).2.1
  have signed := (SharedSigned.same 121 z small odd G S).2
  have eq := unique_input input (fixed_input 270 x p (by decide) good raw domain)
  have stepRel : WideReference.canonical 285 x p=SkywalkTrace.next^[15] (WideReference.canonical 270 x p) := by
    exact Function.iterate_add_apply _ 15 270 _
  have numRel : unsigned 285 x p=SkywalkNat.step^[15] z := by
    exact Function.iterate_add_apply _ 15 270 _
  have active := fixed_input 285 x p (by decide) good (endRaw raw history) (advance x p good raw history domain)
  dsimp only
  rw [stepRel,←eq,signed] at active
  simpa only [numRel] using active

attribute [local irreducible] origin endRaw reframe WideReference.origin

theorem cell_read (s : State) (r : Fin 15) :
    cell (shape 13) r (mappedBasis 13 s.basis)=
      (s.basis (windowNet 13 (ports (shape 13) r).a0),s.basis (windowNet 13 (ports (shape 13) r).history)) := rfl

theorem cell_congr (a b : State) (r : Fin 15)
    (first : a.basis (windowNet 13 (ports (shape 13) r).a0)=b.basis (windowNet 13 (ports (shape 13) r).a0))
    (second : a.basis (windowNet 13 (ports (shape 13) r).history)=b.basis (windowNet 13 (ports (shape 13) r).history)) :
    cell (shape 13) r (mappedBasis 13 a.basis)=cell (shape 13) r (mappedBasis 13 b.basis) :=
  Prod.ext first second

theorem places : WideReference.Geometry 270 13 := by
  unfold WideReference.Geometry
  decide +kernel

theorem record_geometry : ∀r:Fin 15,
    windowNet 13 (ports (shape 13) r).a0∉historySites ∧
    windowNet 13 (ports (shape 13) r).history∉historySites := by decide +kernel

theorem reference_eq (raw history : State) (r : Fin 15) :
    cell (shape 13) r (mappedBasis 13 (origin raw history).basis)=
    cell (shape 13) r (mappedBasis 13 (WideReference.origin 270 raw history).basis) :=
  cell_congr (origin raw history) (WideReference.origin 270 raw history) r
    ((outside_stock_mask raw history _ (record_geometry r).1).trans (WideReference.outside 270 raw history _ (places r).1).symm)
    ((outside_stock_mask raw history _ (record_geometry r).2).trans (WideReference.outside 270 raw history _ (places r).2.1).symm)

theorem reference_cells (x p : Nat) (good : Bounds x p) (raw history : State)
    (r : Fin 15) (domain : Domain 270 x p raw) :
    cell (shape 13) r (mappedBasis 13 (origin raw history).basis)=SkywalkTrace.code (WideReference.canonical (270+r.val) x p) :=
  (reference_eq raw history r).trans (WideReference.reference_cells 270 13 x p (by decide) places good raw history r domain)

theorem recorded_equal (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) (G S : Bool)
    (input : InputAt 270 (encode G S (unsigned 270 x p).u (unsigned 270 x p).v) raw)
    (trace : physicalCells 13 history=SkywalkTrace.trace 15 (encode G S (unsigned 270 x p).u (unsigned 270 x p).v))
    (r : Fin 15) :
    cell (shape 13) r (mappedBasis 13 history.basis)=cell (shape 13) r (mappedBasis 13 (origin raw history).basis) :=
  (WideReference.recorded_equal 270 13 x p (by decide) places good raw history domain G S input trace r).trans
    (reference_eq raw history r).symm

theorem carry (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) (q : Wire) (low : 1556≤q) (high : q≤1784) :
    (origin raw history).basis q=false := by
  have no : q∉historySites := by
    rw [historySites_shape]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at *
    simp only [Wire] at *
    omega
  have fixed : OB5.sig 284 q=q :=
    (by decide +kernel : ∀r:Fin 1785,1556≤r.val → OB5.sig 284 r.val=r.val)
      ⟨q,Nat.lt_succ_of_le high⟩ low
  rw [outside raw history q no,fixed]
  exact full_carry 270 15 x p (by decide) good raw domain [] q low (Nat.le_trans high (by decide))

theorem writes : leave270.all (fun g=>decide (¬Exterior 270 528 (CodecBitSliceVerify.target g)))=true := by
  decide +kernel

theorem exterior (s : State) (m : List Bool) (q : Wire) (ext : Exterior 270 528 q) :
    (run leave270 m s).basis q=s.basis q := by
  apply ECDSAAdd.Entrant.StairPacket.preserve_readonly
  intro g hit eq
  have clean := of_decide_eq_true (List.all_eq_true.mp writes g hit)
  exact clean (eq.symm ▸ ext)

end ECDSAAdd.Entrant.StairPacket.Leave270Reference
namespace ECDSAAdd.Entrant.StairPacket.Leave270Reference
open Arithmetic MappedCompressed WideReference ArchivePortAction IntegerPacket
open ECDSAAdd.Entrant.StairPacket.Extension270
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run SkywalkNat.step
attribute [local irreducible] origin endRaw reframe

def extra : List Wire := List.range' 1705 8

theorem nativeCarry (z : SkywalkRails.State) (s : State) (ready : onRails 13 15 z s.basis) :
    ∀q:Wire,1556≤q → q≤1694 → s.basis q=false := by
  have portsEq : ((ports (shape 13) 15).carry.map (windowNet 13))=List.range' 1556 139 := by decide +kernel
  intro q low high
  apply native_carry _ _ _ ready
  rw [portsEq,List.mem_range'_1]
  exact ⟨low,Nat.lt_succ_of_le high⟩

theorem extra_geometry : ∀q∈extra,
    q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉RailPair.sites Portal270Flag.loPairs ∧
    q∉RailPair.sites Portal270Flag.hiPairs ∧ q∉ParkEndpoint.src ∧ OB5.sig 269 q=q := by
  decide +kernel

theorem extra_at_cut {d : Bool} {x p : Nat} (good : Bounds x p)
    {raw s : State} {g sg pg ps : Bool} (pre : StockWindowTicket.At270 d x p raw s g sg pg ps) :
    ∀q∈extra,s.basis q=false := by
  intro q hit
  obtain ⟨n,f,u,lo,hi,park,map⟩ := extra_geometry q hit
  have range := List.mem_range'_1.mp hit
  have clear : raw.basis q=false := by
    simpa only [span,run] using full_carry 270 0 x p (by decide) good raw pre.domain [] q (by omega) (by omega)
  have same := pre.cut.frame q n f u lo hi
  simpa only [eraseSites,if_neg park,pullState,map,clear] using same

theorem extra_ready {d : Bool} {x p : Nat} (good : Bounds x p) {s : State}
    (pre : StockWindowTicket.Ready270 d x p s) : ∀q∈extra,s.basis q=false := by
  obtain ⟨raw,g,sg,pg,ps,pre⟩ := pre
  exact extra_at_cut good pre

theorem extra_enter (q : Nat) (hit : q∈extra) (s : State) (m : List Bool) :
    (run enter270 m s).basis q=s.basis q := by
  apply LeaveReadoutFrame.preserved
  exact (by decide +kernel : ∀q∈extra,q∉enter270.map LeaveReadoutFrame.destination) q hit

theorem extra_native : ∀q∈extra,¬MayTouch 13 (windowNet 13 q) := by decide +kernel

def releasedInput (q : Nat) : Prop := q=529 ∨ (1029≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1328)
instance (q : Nat) : Decidable (releasedInput q) := by unfold releasedInput;infer_instance

def released (q : Nat) : Prop := q=529 ∨ (1014≤q ∧ q≤1042) ∨ (1301≤q ∧ q≤1328)
instance (q : Nat) : Decidable (released q) := by unfold released;infer_instance

theorem releasedInput_sub (q : Nat) (h : releasedInput q) : released q := by
  rcases h with rfl|⟨lo,hi⟩|band
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨Nat.le_trans (by decide) lo,hi⟩)
  · exact Or.inr (Or.inr band)

theorem released_origin (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) (q : Nat) (site : released q) :
    (origin raw history).basis q=false := by
  unfold released at site
  try simp only [Wire] at *
  have no : q∉historySites := by
    rw [historySites_shape]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  rw [outside raw history q no]
  by_cases mirror : 1301≤q ∧ q≤1328
  · obtain ⟨lo,hi⟩ := mirror
    have map : OB5.sig 284 q=3113-q := by
      unfold OB5.sig
      rw [if_pos (Or.inl ⟨lo,hi⟩)]
    rw [map]
    exact full_carry 270 15 x p (by decide) good raw domain [] (3113-q) (by omega) (by omega)
  have small : q=529 ∨ (1014≤q ∧ q≤1042) := by tauto
  have ident : OB5.sig 284 q=q := by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
  rw [ident]
  obtain ⟨reference,same,stage⟩ := domain
  have finish := full_span 270 15 x p (by decide) good.positive good.nonzero good.odd good.cap
    good.gap good.small good.coprime reference [] stage
  have lower : 270+16<q := by rcases small with rfl|⟨lo,hi⟩ <;> omega
  have upper : q<1044 := by rcases small with rfl|⟨lo,hi⟩ <;> omega
  have offHist : ¬Earlier 270 q := outside_between lower upper
  have link := fixed_span 270 270 15 (Nat.le_refl _) (by decide) raw reference [] same
  apply (link.2 q offHist).trans
  rcases small with rfl|⟨lo,hi⟩
  · exact finish.2.1 _ (by decide +kernel)
  · have members : ∀r∈List.range' 1014 29,r∈(W.compactSkywalkSignPoolB base 285).released := by decide +kernel
    exact finish.2.2 q (members q (List.mem_range'_1.mpr ⟨lo,Nat.lt_succ_of_le hi⟩))

theorem released_input (x p : Nat) (good : Bounds x p) (raw s : State)
    (domain : Domain 270 x p raw) (neg far long : Bool)
    (cut : PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 neg far long
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src s))
    (q : Nat) (site : releasedInput q) : s.basis q=false := by
  unfold releasedInput at site
  try simp only [Wire] at *
  have parked : q∉ParkEndpoint.src := by
    simp only [ParkEndpoint.src,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have geom : ∀r:Fin 1329,releasedInput r.val →
      r.val≠1700 ∧ r.val≠1698 ∧ r.val≠1699 ∧ r.val∉RailPair.sites Portal270Flag.loPairs ∧ r.val∉RailPair.sites Portal270Flag.hiPairs := by
    decide +kernel
  obtain ⟨n,f,u,lo,hi⟩ := geom ⟨q,by omega⟩ site
  have frame := cut.frame q n f u lo hi
  have source : raw.basis (OB5.sig 269 q)=false := by
    rcases site with rfl|b|b
    · have ident : OB5.sig 269 529=529 := by decide +kernel
      rw [ident]
      exact incoming_free_A 270 x p (by decide) raw domain 529 (by decide) (by decide) (Or.inl (by decide +kernel))
    · obtain ⟨blo,bhi⟩ := b
      have ident : OB5.sig 269 q=q := by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
      rw [ident]
      obtain ⟨ref,same,stage⟩ := domain
      have off : ¬Earlier 270 q := outside_between (by omega) (by omega)
      apply (same.2 q off).trans
      exact stage.2.2 q ((by decide +kernel : ∀r∈List.range' 1029 14,r∈(W.compactSkywalkSignPoolB base 270).released) q (List.mem_range'_1.mpr ⟨blo,Nat.lt_succ_of_le bhi⟩))
    · obtain ⟨blo,bhi⟩ := b
      by_cases old : q≤1313
      · have map : OB5.sig 269 q=3113-q := by unfold OB5.sig;rw [if_pos (Or.inl ⟨blo,old⟩)]
        rw [map]
        simpa only [span,run] using full_carry 270 0 x p (by decide) good raw domain [] (3113-q) (by omega) (by omega)
      · have ident : OB5.sig 269 q=q := by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
        rw [ident]
        have h := future_history (i:=270) (j:=q-1044) (by omega) (by omega) domain
        simpa only [base,Wire,show 1028+(q-1044)+16=q by omega] using h
  simpa only [eraseSites,if_neg parked,pullState,source] using frame

theorem exterior_origin (x p : Nat) (good : Bounds x p) (raw input history : State)
    (domain : Domain 270 x p raw) (neg far long : Bool)
    (cut : PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 neg far long
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src input))
    (kept : ∀q,Exterior 270 528 q → q∉historySites → history.basis q=input.basis q)
    (q : Nat) (ext : Exterior 270 528 q) : history.basis q=(origin raw history).basis q := by
  try simp only [Wire] at *
  by_cases old : q∈historySites
  · exact (inside raw history q old).symm
  by_cases zero : releasedInput q
  · exact ((kept q ext old).trans (released_input x p good raw input domain neg far long cut q zero)).trans
      (released_origin x p good raw history domain q (releasedInput_sub q zero)).symm
  have range : ¬(1556≤q ∧ q≤1812) := by unfold Exterior at ext;tauto
  have mirror : ¬(1301≤q ∧ q≤1328) := by unfold releasedInput at zero;tauto
  have map : OB5.sig 284 q=q := by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
  have prevMap : OB5.sig 269 q=q := by unfold OB5.sig;rw [if_neg];simp only [Wire] at *;omega
  have noFlag : q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉ParkEndpoint.src := by
    simp only [ParkEndpoint.src,List.mem_cons,List.not_mem_nil,or_false]
    simp only [Wire] at *
    omega
  have pairCover : ∀r∈RailPair.sites (Portal270Flag.loPairs++Portal270Flag.hiPairs),¬Exterior 270 528 r := by decide +kernel
  have noLo : q∉RailPair.sites Portal270Flag.loPairs := by
    intro h
    exact pairCover q (by simpa only [RailPair.sites,List.flatMap_append,List.mem_append] using Or.inl h) ext
  have noHi : q∉RailPair.sites Portal270Flag.hiPairs := by
    intro h
    exact pairCover q (by simpa only [RailPair.sites,List.flatMap_append,List.mem_append] using Or.inr h) ext
  have source : input.basis q=raw.basis q := by
    have frame := cut.frame q noFlag.1 noFlag.2.1 noFlag.2.2.1 noLo noHi
    simpa only [eraseSites,if_neg noFlag.2.2.2,pullState,prevMap] using frame
  have width : ∀a:Fin 15,W.compactSkywalkTickPreWidth (270+a.val)≤257 ∧
      270+a.val+16+W.compactSkywalkTickPreWidth (270+a.val)≤529 := by decide +kernel
  have exteriorWide : Exterior 270 529 q := by
    unfold Exterior at *
    unfold releasedInput at zero
    simp only [Wire] at *
    omega
  rw [outside raw history q old,map,span_unchanged 270 15 q (by decide) (raw_away (by decide) width exteriorWide)]
  exact (kept q ext old).trans source

theorem released_kept (q : Nat) (site : releasedInput q) (s : State) (m : List Bool) :
    (run leave270 m s).basis q=s.basis q := by
  apply LeaveReadoutFrame.preserved
  have bound : q<1329 := by unfold releasedInput at site;omega
  exact (by decide +kernel : ∀r:Fin 1329,releasedInput r.val → r.val∉leave270.map LeaveReadoutFrame.destination) ⟨q,bound⟩ site

theorem terminal285 (d : Bool) (x p : Nat) (good : Bounds x p) (s : State)
    (domain : Domain 285 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 285 ref.basis ∧
      (∀q∈(W.compactSkywalkTickLayout base 285).wires.toFinset,s.basis q=ref.basis q) ∧
      s.basis (base (1028+285))=false ∧ s.basis (base (2053-285))=false ∧
      ∀q∈[1014,1015,1016],(pullState (OB5.sig 284) s).basis q=false := by
  obtain ⟨ref,stage,link⟩ := leaves_reference 285 x p (by decide) d s domain
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) domain,?_,?_⟩
  · simpa only [span,run] using full_carry 285 0 x p (by decide) good s domain []
      (base (2053-285)) (by decide) (by decide)
  · intro q mem
    have geo : ∀q∈[1014,1015,1016],OB5.sig 284 q=q ∧ 285+16<q ∧ q<1044 ∧
        q∈(W.compactSkywalkSignPoolB base 285).released := by decide +kernel
    obtain ⟨eq,lo,hi,released⟩ := geo q mem
    change s.basis (OB5.sig 284 q)=false
    rw [eq]
    obtain ⟨canonical,match',valid⟩ := domain
    exact (match'.2 q (outside_between lo hi)).trans (valid.2.2 q released)

end ECDSAAdd.Entrant.StairPacket.Leave270Reference

/- front: certified source line 60668. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Hit
open Partial HighBankFirstHit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev swaps (i : Nat) := 1799-i
abbrev hits (i : Nat) := 1561+i

theorem sites : Layout 1560 swaps hits 0 15 := by
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  exact ⟨fun i _ hi => rows ⟨i,hi⟩, fun i _ hi j lt hj => apart ⟨i,hi⟩ ⟨j,hj⟩ lt⟩

theorem written : (((leave270.drop 245).take 30)) = putAll 1560 swaps hits 0 15 := by rfl

theorem retired : (((leaveInv270.drop 3094).take 30)) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave270Hit

end

/- front: certified source line 61960. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Partial LeaveSelector HighBankFirstHit Leave270Hit
set_option maxRecDepth 50000

def far : List Op := [.xor 1559 1702, .xor 1561 1702, .xor 1562 1702, .xor 1563 1702, .xor 1564 1702, .xor 1565 1702]
def zero : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffix : List Op := [.save 299 300 1577, .save 298 1577 1578, .save 297 1578 1579, .save 296 1579 1580, .save 295 1580 1581, .save 294 1581 1582, .save 293 1582 1583, .save 292 1583 1584, .save 291 1584 1585, .save 290 1585 1586, .save 289 1586 1587, .save 288 1587 1588]
def select : List Op := [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593, .save 1567 1578 1594, .save 1568 300 1595]
def cross : List Op := [.mix 1576 423 1701, .mix 1562 424 1701, .mix 1563 425 1701, .mix 1564 426 1701, .mix 1565 427 1701, .mix 1566 428 1701, .mix 1567 429 1701, .mix 1568 430 1701, .mix 1569 431 1701, .mix 1570 432 1701, .mix 1571 433 1701, .mix 1572 434 1701, .mix 1573 435 1701, .mix 1574 436 1701, .mix 1575 437 1701, .mix 1560 438 1701]
def sign : List Op := [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596, .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596, .xor 1560 1596]
def product : List Op := [.save 1701 1596 1597]

def prepare := far ++ zero ++ suffix ++ select ++ cross ++ sign ++ product
def retire := (product.reverse ++ sign ++ select.reverse ++ suffix.reverse ++ zero)
def prepareInv := zero.reverse ++ suffix ++ select ++ sign.reverse ++ product
def retireInv := prepare.reverse

theorem prepared : (((leave270.drop 275).take 59)) = prepare.map Op.enter := by rfl

theorem retired : (((leave270.drop 2342).take 37)) = retire.map Op.exit := by rfl

theorem preparedInv : (((leaveInv270.drop 990).take 37)) = prepareInv.map Op.enter := by rfl

theorem retiredInv : (((leaveInv270.drop 3035).take 59)) = retireInv.map Op.exit := by rfl

theorem hitsInv : (((leaveInv270.drop 960).take 30)) = putAll 1560 swaps hits 0 15 := by rfl

theorem retireHits : (((leave270.drop 2379).take 30)) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- front: certified source line 63095. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open LeaveSelector
def ports : Ports := ⟨286,423,1701,1702⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- front: certified source line 63548. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave270Hit Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

def program (inv : Bool) := if inv then leaveInv270 else leave270
def initPC (inv : Bool) := if inv then 957 else 242
def retirePC (inv : Bool) := if inv then 3035 else 2342
def beforeWord (inv : Bool) := ((program inv).drop (initPC inv+33)).take (if inv then 37 else 59)
def afterWord (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 59 else 37)

theorem flags (inv : Bool) : ((program inv).drop (initPC inv)).take 3 =
    (flagOps 1698 1699 inv).map Op.enter := by cases inv <;> rfl


theorem firstHit (inv : Bool) : ((program inv).drop (initPC inv+3)).take 30 =
    putAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact written
  · exact hitsInv

theorem lastHit (inv : Bool) : ((program inv).drop (retirePC inv+(if inv then 59 else 37))).take 30 =
    dropAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact retireHits
  · exact Leave270Hit.retired

theorem separate (i : Nat) (hi:i<15) (j : Nat) (hj:j<15) : swaps i≠LeaveSelector.tags j := by
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  exact cert ⟨i,hi⟩ ⟨j,hj⟩

theorem execute (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(LeaveSelector.start ports inv k q).read v) :
    let out := run (beforeWord inv) m s
    out.phase=s.phase ∧ out.basis 1702=nearby k ∧
    out.basis 1701=(crossing ports k).read v ∧ out.basis 1596=(signExpr ports k).read v ∧
    out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  cases inv
  · exact physical ports prepare false k s m v input (controlCert k)
  · exact physical ports prepareInv true k s m v input (controlInvCert k)

theorem clear (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v) :
    run (afterWord inv) m s=⟨s.phase,fun q => (restored ports inv k q).read v⟩ := by
  cases inv
  · apply cleanup ports prepare retire false k s m v input (cleanCert k)
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)


end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- front: certified source line 63751. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Arithmetic RecordedQuantum LeaveSelector Leave270Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
def rawPrefix (inv : Bool) := (program inv).take (initPC inv)
theorem historyShape : ∀ inv : Bool, ∀i : Fin 15,
    LeaveSelector.parityAt (ports.g+i) (rawPrefix inv)=some true ∧
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem history (inv : Bool) (i : Fin 15) (s : State) (m : List Bool) :
    let out:=run (rawPrefix inv) m s
    out.basis (ports.g+i)= !s.basis (ports.g+i) ∧ out.basis (swaps i)=s.basis (swaps i) := by
  obtain ⟨g,sw⟩:=historyShape inv i
  exact ⟨by simpa using polarity _ _ _ g s m,by simpa using polarity _ _ _ sw s m⟩
end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- middle: certified source line 56. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Join
open HighBankJoin Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def tags : List Wire := [1576, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]
def columns : List Column := [
  ⟨true,some 1576,423,1695⟩, ⟨true,some 1562,424,1696⟩, ⟨true,some 1563,425,1697⟩, ⟨true,some 1564,426,926⟩, ⟨true,some 1565,427,927⟩, ⟨true,some 1566,428,928⟩, ⟨true,some 1567,429,929⟩, ⟨true,some 1568,430,930⟩, ⟨true,some 1569,431,931⟩, ⟨true,some 1570,432,932⟩, ⟨true,some 1571,433,933⟩, ⟨false,some 1572,434,934⟩, ⟨false,some 1573,435,935⟩, ⟨false,some 1574,436,936⟩, ⟨false,some 1575,437,937⟩, ⟨false,some 1560,438,938⟩, ⟨false,none,439,939⟩, ⟨false,none,440,940⟩]

def digitPass := digits (tags.getD · 0) (fun j => 423+j) 1701 1613 0 16
def wordPass := word 1614 columns

theorem emitted : (((leave270.drop 2233).take 107)) = digitPass ++ wordPass := by rfl

theorem sites : WellPlaced 1614 columns := by
  unfold WellPlaced
  decide +kernel

theorem disjoint : columns.Pairwise Apart := by
  unfold Apart
  decide +kernel

theorem digitSites : DigitLayout (tags.getD · 0) (fun j => 423+j) 1701 1613 0 16 := by
  have valid : ∀ i : Fin 16, [tags.getD i 0, 1701, 1613, 423+i.val, 423+(i.val+1)].Nodup := by decide +kernel
  have separate : ∀ i : Fin 16, ∀ j : Fin 17, tags.getD i 0 ≠ 423+j.val := by decide +kernel
  exact ⟨fun i _ hi => valid ⟨i,hi⟩,fun i _ hi j _ hj => separate ⟨i,hi⟩ ⟨j,by omega⟩⟩

theorem assembled :
    leave270 = leave270.take 2233 ++ ((digitPass ++ wordPass) ++ leave270.drop 2340) := by
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave270Join

end

/- middle: certified source line 212. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Shift
open Partial HighBankLookup
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def bank0 : List Wire := [1695, 1696, 1697, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1598]

theorem pass0 : (((leave270.drop 870).take 318)) = HighBankShift.program 1613 (bank0.getD · 0) 1 106 := by rfl

theorem layout0 : HighBankShift.Layout 1613 (bank0.getD · 0) 107 := by
  apply lookupLayout
  all_goals decide +kernel

def bank1 : List Wire := [1695, 1696, 1697, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1598, 1599, 1600]

theorem pass1 : (((leave270.drop 1204).take 321)) = HighBankShift.program 1613 (bank1.getD · 0) 2 107 := by rfl

theorem layout1 : HighBankShift.Layout 1613 (bank1.getD · 0) 109 := by
  apply lookupLayout
  all_goals decide +kernel

def bank2 : List Wire := [1695, 1696, 1697, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1598, 1599, 1600, 1601, 1602, 1603, 1604]

theorem pass2 : (((leave270.drop 1541).take 327)) = HighBankShift.program 1613 (bank2.getD · 0) 4 109 := by rfl

theorem layout2 : HighBankShift.Layout 1613 (bank2.getD · 0) 113 := by
  apply lookupLayout
  all_goals decide +kernel

def bank3 : List Wire := [1695, 1696, 1697, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612]

theorem pass3 : (((leave270.drop 1884).take 339)) = HighBankShift.program 1613 (bank3.getD · 0) 8 113 := by rfl

theorem layout3 : HighBankShift.Layout 1613 (bank3.getD · 0) 121 := by
  apply lookupLayout
  all_goals decide +kernel

theorem assembled : leave270 =
    ((leave270.drop 0).take 870) ++
    HighBankShift.program 1613 (bank0.getD · 0) 1 106 ++
    ((leave270.drop 1188).take 16) ++
    HighBankShift.program 1613 (bank1.getD · 0) 2 107 ++
    ((leave270.drop 1525).take 16) ++
    HighBankShift.program 1613 (bank2.getD · 0) 4 109 ++
    ((leave270.drop 1868).take 16) ++
    HighBankShift.program 1613 (bank3.getD · 0) 8 113 ++
    ((leave270.drop 2223).take 10) ++
    (Leave270Join.digitPass ++ Leave270Join.wordPass) ++
    leave270.drop 2340 := by
  rfl
end ECDSAAdd.Entrant.StairPacket.Leave270Shift

end

/- middle: certified source line 528. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Control
open Partial HighBankControl Leave270Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def controls0 : List Wire := [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560]

theorem selection0 (key : Fin 16) :
    parity (fun q => decide (q = Leave270Join.tags.getD key 0)) controls0 = key.val.testBit 0 := by
  revert key
  decide +kernel

theorem away0 : 1613 ∉ controls0 ∧ ∀ q ∈ controls0, q ∉ bank0 := by decide +kernel

theorem on0 : (((leave270.drop 862).take 8)) = toggles 1613 controls0 := by rfl
theorem off0 : (((leave270.drop 1188).take 8)) = toggles 1613 controls0 := by rfl
theorem reverseOn0 : (((leaveInv270.drop 2173).take 8)) = toggles 1613 controls0.reverse := by rfl
theorem reverseOff0 : (((leaveInv270.drop 2499).take 8)) = toggles 1613 controls0.reverse := by rfl
theorem wrapped0 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls0)⟩
    let v := run (HighBankShift.program 1613 (bank0.getD · 0) 1 106) m u
    run (((leave270.drop 862).take 334)) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : (((leave270.drop 862).take 334)) =
      toggles 1613 controls0 ++ (HighBankShift.program 1613 (bank0.getD · 0) 1 106 ++ toggles 1613 controls0) := by rfl
  rw [exactSlice]
  apply wrapped layout0 (by decide) _ away0.1
  intro q hq i hi eq
  have h : i < bank0.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away0.2 q hq (eq ▸ List.getElem_mem h)


def controls1 : List Wire := [1563, 1564, 1567, 1568, 1571, 1572, 1575, 1560]

theorem selection1 (key : Fin 16) :
    parity (fun q => decide (q = Leave270Join.tags.getD key 0)) controls1 = key.val.testBit 1 := by
  revert key
  decide +kernel

theorem away1 : 1613 ∉ controls1 ∧ ∀ q ∈ controls1, q ∉ bank1 := by decide +kernel

theorem on1 : (((leave270.drop 1196).take 8)) = toggles 1613 controls1 := by rfl
theorem off1 : (((leave270.drop 1525).take 8)) = toggles 1613 controls1 := by rfl
theorem reverseOn1 : (((leaveInv270.drop 1836).take 8)) = toggles 1613 controls1.reverse := by rfl
theorem reverseOff1 : (((leaveInv270.drop 2165).take 8)) = toggles 1613 controls1.reverse := by rfl
theorem wrapped1 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls1)⟩
    let v := run (HighBankShift.program 1613 (bank1.getD · 0) 2 107) m u
    run (((leave270.drop 1196).take 337)) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : (((leave270.drop 1196).take 337)) =
      toggles 1613 controls1 ++ (HighBankShift.program 1613 (bank1.getD · 0) 2 107 ++ toggles 1613 controls1) := by rfl
  rw [exactSlice]
  apply wrapped layout1 (by decide) _ away1.1
  intro q hq i hi eq
  have h : i < bank1.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away1.2 q hq (eq ▸ List.getElem_mem h)


def controls2 : List Wire := [1565, 1566, 1567, 1568, 1573, 1574, 1575, 1560]

theorem selection2 (key : Fin 16) :
    parity (fun q => decide (q = Leave270Join.tags.getD key 0)) controls2 = key.val.testBit 2 := by
  revert key
  decide +kernel

theorem away2 : 1613 ∉ controls2 ∧ ∀ q ∈ controls2, q ∉ bank2 := by decide +kernel

theorem on2 : (((leave270.drop 1533).take 8)) = toggles 1613 controls2 := by rfl
theorem off2 : (((leave270.drop 1868).take 8)) = toggles 1613 controls2 := by rfl
theorem reverseOn2 : (((leaveInv270.drop 1493).take 8)) = toggles 1613 controls2.reverse := by rfl
theorem reverseOff2 : (((leaveInv270.drop 1828).take 8)) = toggles 1613 controls2.reverse := by rfl
theorem wrapped2 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls2)⟩
    let v := run (HighBankShift.program 1613 (bank2.getD · 0) 4 109) m u
    run (((leave270.drop 1533).take 343)) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : (((leave270.drop 1533).take 343)) =
      toggles 1613 controls2 ++ (HighBankShift.program 1613 (bank2.getD · 0) 4 109 ++ toggles 1613 controls2) := by rfl
  rw [exactSlice]
  apply wrapped layout2 (by decide) _ away2.1
  intro q hq i hi eq
  have h : i < bank2.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away2.2 q hq (eq ▸ List.getElem_mem h)


def controls3 : List Wire := [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]

theorem selection3 (key : Fin 16) :
    parity (fun q => decide (q = Leave270Join.tags.getD key 0)) controls3 = key.val.testBit 3 := by
  revert key
  decide +kernel

theorem away3 : 1613 ∉ controls3 ∧ ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel

theorem on3 : (((leave270.drop 1876).take 8)) = toggles 1613 controls3 := by rfl
theorem off3 : (((leave270.drop 2223).take 8)) = toggles 1613 controls3 := by rfl
theorem reverseOn3 : (((leaveInv270.drop 1138).take 8)) = toggles 1613 controls3.reverse := by rfl
theorem reverseOff3 : (((leaveInv270.drop 1485).take 8)) = toggles 1613 controls3.reverse := by rfl
theorem wrapped3 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls3)⟩
    let v := run (HighBankShift.program 1613 (bank3.getD · 0) 8 113) m u
    run (((leave270.drop 1876).take 355)) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : (((leave270.drop 1876).take 355)) =
      toggles 1613 controls3 ++ (HighBankShift.program 1613 (bank3.getD · 0) 8 113 ++ toggles 1613 controls3) := by rfl
  rw [exactSlice]
  apply wrapped layout3 (by decide) _ away3.1
  intro q hq i hi eq
  have h : i < bank3.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away3.2 q hq (eq ▸ List.getElem_mem h)


end ECDSAAdd.Entrant.StairPacket.Leave270Control

end

/- middle: certified source line 809. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Barrel
open Partial Leave270Control Leave270Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev wire (i : Nat) := bank3.getD i 0
def passes0 : Program := []
def passes1 := passes0 ++ stage 1613 wire controls0 1 106
def passes2 := passes1 ++ stage 1613 wire controls1 2 107
def passes3 := passes2 ++ stage 1613 wire controls2 4 109
def passes4 := passes3 ++ stage 1613 wire controls3 8 113

theorem emitted : (((leave270.drop 862).take 1369)) = passes4 := by rfl

theorem value (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^106) (h : holds wire 121 x s) (clean : s.basis 1613=false)
    (tags : ∀ q ∈ Leave270Join.tags, s.basis q = decide (q = Leave270Join.tags.getD key 0)) :
    Result wire 121 (x <<< key.val) s (run (((leave270.drop 862).take 1369)) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 121 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 121 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 106+0 ≤ 106)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls0, q ∈ Leave270Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 121 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 106+(key.val % 2) ≤ 107)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls1, q ∈ Leave270Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 121 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 106+(key.val % 4) ≤ 109)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls2, q ∈ Leave270Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 121 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 106+(key.val % 8) ≤ 113)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls3, q ∈ Leave270Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave270Barrel

end

/- front: certified source line 959. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion270
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
def longPairs : List (Wire × Wire) := [(908,1557),(909,1558),(910,1559),(911,1560),(912,1561),(913,1562),(914,1563),(915,1564),(916,1565),(917,1566),(918,1567),(919,1568),(920,1569),(921,1570),(922,1571),(923,1572),(924,1573),(925,1574)]
theorem long_layout : (1556::907::sites longPairs).Nodup := by decide +kernel
def long : Program := ((leave270).drop 93).take 76
theorem long_eq : long = latch true none 1556 907 longPairs := by decide +kernel
def longBack : Program := ((leaveInv270).drop 3200).take 76
theorem longBack_eq : longBack = backwardLatch true none 1556 907 longPairs := by decide +kernel
theorem long_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run long m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 907 longPairs).any s.basis))⟩ := by
  rw [long_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 907 longPairs long_layout (by simp) s m clean
theorem longBack_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run longBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 907 longPairs).any s.basis))⟩ := by
  rw [longBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 907 longPairs long_layout (by simp) s m clean
def pendingPairs : List (Wire × Wire) := [(433,1559),(934,1560),(935,1561),(936,1562),(937,1563),(938,1564),(939,1565),(940,1566),(941,1567),(942,1568),(943,1569),(944,1570),(945,1571),(946,1572),(947,1573),(948,1574),(949,1575),(950,1576),(951,1577),(952,1578),(953,1579),(954,1580),(955,1581),(956,1582),(957,1583),(958,1584),(959,1585),(960,1586),(961,1587),(962,1588),(963,1589),(964,1590),(965,1591),(966,1592),(967,1593),(968,1594),(969,1595),(970,1596),(971,1597),(972,1613),(973,1614),(974,1615),(975,1616),(976,1617),(977,1618),(978,1619),(979,1620),(980,1621),(981,1622),(982,1623),(983,1624),(984,1625),(985,1626),(986,1627),(987,1628),(988,1629),(989,1630),(990,1631),(991,1632),(992,1633),(993,1634),(994,1635),(995,1636),(996,1637),(997,1638),(998,1639),(999,1640),(1000,1641),(1001,1642),(1002,1643),(1003,1644),(1004,1645),(1005,1646),(1006,1647),(1007,1648),(1008,1649),(1009,1650),(1010,1651),(1011,1652),(1012,1653),(1013,1654),(1014,1655),(1015,1656),(1016,1657),(1017,1658),(1018,1659),(1019,1660),(1020,1661),(1021,1662),(1022,1663),(1023,1664),(1024,1665),(1025,1666),(1026,1667),(1027,1668),(1028,1669),(1598,1670),(1599,1671),(1600,1672),(1601,1673),(1602,1674),(1603,1675),(1604,1676),(1605,1677),(1606,1678),(1607,1679),(1608,1680),(1609,1681),(1610,1682),(1611,1683),(1612,1684)]

theorem pending_layout : (431::432::1557::1558::sites pendingPairs).Nodup := by decide +kernel
def pending : Program := ((leave270).drop 2479).take 450
theorem pending_eq : pending = threshold 431 432 1558 1557 pendingPairs := by decide +kernel
def pendingBack : Program := ((leaveInv270).drop 440).take 450
theorem pendingBack_eq : pendingBack = thresholdBack 431 432 1558 1557 pendingPairs := by decide +kernel
theorem pending_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 431 432 pendingPairs s.basis))⟩ := by
  rw [pending_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_run 431 432 1558 1557 pendingPairs pending_layout s m fresh clean
theorem pendingBack_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 431 432 pendingPairs s.basis))⟩ := by
  rw [pendingBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_back 431 432 1558 1557 pendingPairs pending_layout s m fresh clean
def clearFlagPairs : List (Wire × Wire) := [(907,1559),(908,1560),(909,1561),(910,1562),(911,1563),(912,1564),(913,1565),(914,1566),(915,1567),(916,1568),(917,1569),(918,1570)]
theorem clearFlag_layout : (1556::1558::sites clearFlagPairs).Nodup := by decide +kernel
def clearFlag : Program := ((leave270).drop 2930).take 52
theorem clearFlag_eq : clearFlag = latch true none 1556 1558 clearFlagPairs := by decide +kernel
def clearFlagBack : Program := ((leaveInv270).drop 387).take 52
theorem clearFlagBack_eq : clearFlagBack = backwardLatch true none 1556 1558 clearFlagPairs := by decide +kernel
theorem clearFlag_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlag m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlag_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
theorem clearFlagBack_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlagBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlagBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
def fullA : List Wire := [423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440]
def fullM : List Wire := [908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925]
def fullC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575]
theorem full_geometry : Companion.Geometry fullA fullM fullC 1556 1558 := by
  constructor <;> decide +kernel
def smallA : List Wire := [423,424,425,426,427,428,429,430,431,432,433]
def smallM : List Wire := [908,909,910,911,912,913,914,915,916,917,918]
def smallC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568]
theorem small_geometry : Companion.Geometry smallA smallM smallC 1556 1558 := by
  constructor <;> decide +kernel
def erase : Program := ((leave270).drop 172).take 70
theorem erase_eq : erase = Companion.erase fullA fullM fullC 1556 1558 := by decide +kernel
def eraseBack : Program := ((leaveInv270).drop 3127).take 70
theorem eraseBack_eq : eraseBack = PortalBorrow.restore fullA fullM fullC 1556 1558 := by decide +kernel
def restore : Program := ((leave270).drop 2412).take 64
theorem restore_eq : restore = Companion.restore smallA smallM smallC 1556 1558 := by decide +kernel
def restoreBack : Program := ((leaveInv270).drop 893).take 64
theorem restoreBack_eq : restoreBack = (notRegister smallM).reverse ++ PortalUnitInverse.emit smallM smallC 1558 ++ (notRegister smallM).reverse ++ (copyRegister (some 1556) smallA smallM).reverse := by decide +kernel
def mask : Program := ((leave270).drop 169).take 3
theorem mask_eq : mask = ([.X 1557,.CX 422 1557,.CCX 907 1557 1558]:Program) := by decide +kernel
def maskBack : Program := ((leaveInv270).drop 3197).take 3
theorem maskBack_eq : maskBack = ([.measureX 1558 [] [.CZ 907 1557],.CX 422 1557,.X 1557]:Program) := by decide +kernel
def releaseMask : Program := ((leave270).drop 2476).take 3
theorem releaseMask_eq : releaseMask = ([.measureX 1558 [] [.CZ 907 1557],.CX 422 1557,.X 1557]:Program) := by decide +kernel
def releaseMaskBack : Program := ((leaveInv270).drop 890).take 3
theorem releaseMaskBack_eq : releaseMaskBack = ([.X 1557,.CX 422 1557,.CCX 907 1557 1558]:Program) := by decide +kernel
def nextU : Program := ((leave270).drop 2929).take 1
theorem nextU_eq : nextU = ([.CCX 1556 1557 1558]:Program) := by decide +kernel
def nextUBack : Program := ((leaveInv270).drop 439).take 1
theorem nextUBack_eq : nextUBack = ([.measureX 1558 [] [.CZ 1556 1557]]:Program) := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion270

end

/- middle: certified source line 1387. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave270Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def ys : List Wire := [1695, 1696, 1697, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028]

def carries : List Wire := [1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712]

theorem emitted : (((leave270.drop 334).take 528)) = adjust ys carries 1701 1597 := by rfl
theorem combined : (((leave270.drop 334).take 1897)) =
    adjust ys carries 1701 1597 ++ (((leave270.drop 862).take 1369)) := by rfl

theorem result (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (one : ∀ q ∈ Leave270Join.tags, s.basis q = decide (q = Leave270Join.tags.getD key 0)) :
    let x := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    Result wire 121 (x <<< key.val) s (run (((leave270.drop 334).take 1897)) m s) := by
  let p := adjust ys carries 1701 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1701 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 106, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 121, 106 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^106 := regValue_lt ys t.basis
  have data : holds wire 121 x t := by
    intro i hi
    by_cases lo : i < 106
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 106 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave270Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave270Join.tags, t.basis q = decide (q = Leave270Join.tags.getD key 0) :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (one _ h)
  have action := value key x t (m.drop (measurementCount p)) small data cold keys
  have initial : x = adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨action.bits,action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 106 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave270High

end

/- middle: certified source line 1440. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Word
open Partial Leave270Join Leave270Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev row (i : Fin 18) := columns[i.val]'(i.isLt)
def hot (key : Fin 16) (q : Wire) := decide (q = tags.getD key 0)

theorem combine (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis 1701).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614=false) :
    let out := run (((leave270.drop 2233).take 107)) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref := hot key
  let u := run digitPass m s
  have sch : ∀ key : Fin 16, schedule (hot key) key false 0 columns = true := by decide +kernel
  have unique : ∀ i t : Fin 16, hot t (tags.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i<0+16) : s.basis (tags.getD i 0)=decide (i=key.val) := by
    have mem : tags.getD i 0 ∈ tags := by rw [List.getD_eq_getElem _ _ (show i<tags.length from hi)]; exact List.getElem_mem _
    exact (tagsOn _ mem).trans (unique ⟨i,hi⟩ key)
  have z := digits_remainder digitSites s m key.val (by omega) key.isLt sel X 18 (by decide)
    (fun i _ j _ eq => Nat.add_left_cancel eq) shadow digit
  have geom : ∀ i : Fin 18, (row i).shadow=423+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have hits : ∀ r ∈ columns, ∀ q ∈ r.hot, q∈tags := by decide +kernel
  have members : ∀ q ∈ tags, ∀ i : Fin 18, q≠423+i.val := by decide +kernel
  have tx : ∀ i j : Fin 18, wire i.val ≠ 423+j.val := by decide +kernel
  have cold : ∀ i : Fin 18, 1614 ≠ 423+i.val := by decide +kernel
  have ctrl : ∀ r∈columns, ∀ q∈r.hot, u.basis q=ref q := by
    intro r hr q hq
    have mem := hits r hr q hq
    exact (z.2.2 q (members q mem ⟨key.val,by omega⟩) (members q mem ⟨key.val+1,by omega⟩)).trans (tagsOn q mem)
  have inputs : columnsRead columns u.basis X H key.val 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change u.basis (row ix).shadow = _ ∧ u.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.zero_add]
    exact ⟨z.2.1 i hi,(z.2.2 _ (tx ix ⟨key.val,by omega⟩) (tx ix ⟨key.val+1,by omega⟩)).trans (tube i hi)⟩
  have rz : u.basis 1614=false :=
    (z.2.2 _ (cold ⟨key.val,by omega⟩) (cold ⟨key.val+1,by omega⟩)).trans scratch
  have word := reassemble 1614 columns ref u m X H key.val sites disjoint ctrl rz (sch key) inputs
  dsimp only
  rw [Leave270Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero]
  refine ⟨word.1.trans z.1,fun i => word.2.1 i.val i.isLt,?_⟩
  intro q away
  have safe (j : Fin 18) : q ≠ 423+j.val := by
    rw [← (geom j).1]
    exact (away _ (List.getElem_mem j.isLt)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe ⟨key.val,by omega⟩) (safe ⟨key.val+1,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave270Word

end

/- front: certified source line 1533. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion270
open ECDSAAdd.Arithmetic
theorem erase_run (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (input:(regValue fullM s.basis+(s.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) s.basis (regValue fullA s.basis)) :
    (run erase m s).phase=s.phase ∧ (∀q,q∉fullM → (run erase m s).basis q=s.basis q) ∧ regValue fullM (run erase m s).basis=0 := by
  rw [erase_eq]
  exact Companion.clear fullA fullM fullC 1556 1558 full_geometry s m clean input
theorem erase_roundtrip (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (n:List Bool) : run eraseBack n (run erase m s)=s := by
  rw [eraseBack_eq,erase_eq]
  apply LeaveCompanion.erase_undo fullA fullM fullC 1556 1558 full_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem restore_run (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (input:regValue smallM s.basis=0) :
    (run restore m s).phase=s.phase ∧ (∀q,q∉smallM → (run restore m s).basis q=s.basis q) ∧ regValue smallM (run restore m s).basis=(copyValue (some 1556) s.basis (regValue smallA s.basis)+2^smallM.length-(s.basis 1558).toNat)%2^smallM.length := by
  rw [restore_eq]
  exact Companion.write smallA smallM smallC 1556 1558 small_geometry s m clean input
theorem restore_roundtrip (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (n:List Bool) : run restoreBack n (run restore m s)=s := by
  rw [restoreBack_eq,restore_eq]
  apply LeaveCompanion.restore_undo smallA smallM smallC 1556 1558 small_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem pending_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (431::432::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pending_run s m fresh clean, LeaveCompanion.high_three]
theorem pendingBack_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (431::432::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pendingBack_run s m fresh clean, LeaveCompanion.high_three]
theorem nextU_run (s:State) (m:List Bool) (fresh:s.basis 1558=false) :
    run nextU m s=⟨s.phase,writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  rw [nextU_eq]
  simp [run,fresh]
theorem nextUBack_run (s:State) (m:List Bool) (product:s.basis 1558=(s.basis 1556 && s.basis 1557)) :
    run nextUBack m s=⟨s.phase,writeBit s.basis 1558 false⟩ := by
  rw [nextUBack_eq]
  exact PortalAnd.measure_and _ _ _ _ _ (by decide) (by decide) product
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion270

end

/- front: certified source line 1784. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion270
theorem clearFlag_digits : PortalAnd.digits 1558 clearFlagPairs = 1558::907::smallM := by decide +kernel
theorem clearFlag_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 907=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlag m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlag_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 907=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_reconstruct (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=false)
    (orientation:s.basis 1558=(decide (half≤mag) && s.basis 1557))
    (bottom:s.basis 907=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 (decide (half≤mag))⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion270

end

/- front: certified source line 2865. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave270Hit
set_option maxRecDepth 50000

def fullPrefix (inv : Bool) := ((program inv).drop (initPC inv)).take (if inv then 70 else 92)
theorem fullShape (inv : Bool) : fullPrefix inv =
    withHits 1698 1699 inv swaps ((if inv then prepareInv else prepare).map Op.enter) := by
  cases inv <;> rfl

theorem complete (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1698) (s.basis 1699) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    let out:=run (fullPrefix inv) m s
    out.phase=s.phase ∧ out.basis 1702=nearby k ∧ out.basis 1701=(crossing ports k).read v ∧
    out.basis 1596=(signExpr ports k).read v ∧ out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact assembled ports 1698 1699 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange
    (by cases inv
        · exact controlCert k
        · exact controlInvCert k)
end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- front: certified source line 3229. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave270Hit
set_option maxRecDepth 50000

def fullPostfix (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 92 else 70)
theorem postfixShape (inv : Bool) : fullPostfix inv = afterWord inv ++
    (dropAll 1560 swaps LeaveSelector.tags 0 15 ++ (flagOps 1698 1699 (!inv)).reverse.map Op.exit) := by
  cases inv <;> rfl

theorem retiredFull (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v)
    (l : left k=(v 1698 && v 1699)) (r : right k=(v 1698 && !v 1699))
    (exchange : right k=true → ∀i<15,i≤key k → v (swaps i)=decide (i=key k)) :
    run (fullPostfix inv) m s=⟨s.phase,clearKey (fun q=>(restored ports inv k q).read v)⟩ := by
  have ws : ∀iv : Bool, ∀k : Mode,witnesses 1698 1699 swaps k (restored ports iv k) := by decide +kernel
  rw [postfixShape]
  exact full_release 1698 1699 swaps sites separate (by decide) (by decide) (!inv) k s m v _ _
    (clear inv k s m v input) (ws inv k) l r exchange



end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- middle: certified source line 4686. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270BarrelBits
open Partial Leave270Barrel Leave270Control Leave270Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
theorem byDigits (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^106) (h : holds wire 121 x s) (clean : s.basis 1613=false)
    (bit0 : parity s.basis controls0 = key.val.testBit 0)
    (bit1 : parity s.basis controls1 = key.val.testBit 1)
    (bit2 : parity s.basis controls2 = key.val.testBit 2)
    (bit3 : parity s.basis controls3 = key.val.testBit 3) :
    Result wire 121 (x <<< key.val) s (run (((leave270.drop 862).take 1369)) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 121 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 121 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 106+0 ≤ 106)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 121 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 106+(key.val % 2) ≤ 107)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 121 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 106+(key.val % 4) ≤ 109)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 121 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 106+(key.val % 8) ≤ 113)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave270BarrelBits

end

/- middle: certified source line 4743. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Middle
open Arithmetic Partial Leave270Barrel Leave270High Leave270Word Leave270Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := (((leave270.drop 334).take 1897))
abbrev lastPart := (((leave270.drop 2233).take 107))
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := (((leave270.drop 334).take 2006))

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (key : Fin 16) (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (_one : ∀ q ∈ Leave270Join.tags, s.basis q = decide (q = Leave270Join.tags.getD key 0)),
    let x := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    Result wire 121 (x <<< key.val) s (run early m s))
    (wordLaw : ∀ (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (_tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (_shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (_digit : X/2^key.val = (s.basis 1701).toNat + 2*(s.basis 1613).toNat)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1701).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 121, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 121 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let H := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw key s m clean selectZero padding one
  have bits (i : Fin 121) : v.basis (wire i.val)=(2^key.val*H).testBit i.val := by
    rw [Nat.mul_comm (2^key.val) H,← Nat.shiftLeft_eq]
    exact a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 121, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 121, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 423+j.val≠1613 ∧ ∀ i : Fin 121, 423+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 121) : 1613 ≠ wire i.val := Leave270Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=hot key q := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (one q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (423+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=(2^key.val*H).testBit i := by
    let j : Fin 121 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have select : v.basis 1613=false := (a.frame _ Leave270Shift.layout3.separate).trans selectZero
  have neg : v.basis 1597=s.basis 1597 := a.frame _ (fun i h => (by decide +kernel : ∀ j : Fin 121, 1597≠wire j.val) ⟨i,h⟩)
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u,run,writeBit,Function.update,select,neg]
  have cross := old 1701 (by decide) (by decide +kernel)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis 1701).toNat + 2*(u.basis 1613).toNat := by rw [cross,d1]; exact digit
  have word := wordLaw key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 121, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1701).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 121, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 121 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave270High.result Leave270Word.combine key X s m clean selectZero padding one shadow digit scratch
end ECDSAAdd.Entrant.StairPacket.Leave270Middle

end

/- middle: certified source line 4847. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270NearWord
open Partial Leave270Join Leave270Barrel Leave270Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem combine (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=false)
    (scratch : s.basis 1614=false) :
    let out := run (((leave270.drop 2233).take 107)) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref : BasisState := fun _ => false
  have none : run digitPass m s = s := by
    apply digits_quiet digitSites
    intro i _ hi
    apply off
    rw [List.getD_eq_getElem _ _ (show i < tags.length from hi)]
    exact List.getElem_mem _
  have sch : schedule ref 18 false 0 columns = true := by decide +kernel
  have members : ∀ r∈columns, ∀ q∈r.hot, q∈tags := by decide +kernel
  have geom : ∀ i : Fin 18, (row i).shadow=423+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have inputs : columnsRead columns s.basis X 0 18 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change s.basis (row ix).shadow = _ ∧ s.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.mod_eq_of_lt bound,Nat.zero_add,Nat.mul_zero,Nat.zero_testBit,ix]
    exact And.intro (shadow i hi) (tube i hi)
  have v := reassemble 1614 columns ref s m X 0 18 sites disjoint (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [Leave270Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero,none]
  exact ⟨v.1,fun i => by simpa only [Nat.mul_zero,Nat.zero_add,Nat.mod_eq_of_lt bound] using v.2.1 i.val i.isLt,v.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave270NearWord

end

/- middle: certified source line 5297. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270NearHigh
open Arithmetic Partial Leave270Barrel Leave270High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (off : ∀ q ∈ Leave270Join.tags, s.basis q=false) :
    let x := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    Result wire 121 x s (run (((leave270.drop 334).take 1897)) m s) := by
  let p := adjust ys carries 1701 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1701 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 106, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 121, 106 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^106 := regValue_lt ys t.basis
  have data : holds wire 121 x t := by
    intro i hi
    by_cases lo : i < 106
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 106 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave270Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave270Join.tags, t.basis q=false :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (off _ h)
  have quiet (xs : List Wire) (sub : ∀ q ∈ xs, q ∈ Leave270Join.tags) : parity t.basis xs = false := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [parity,keys q (sub _ (by simp)),Bool.false_xor,ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  have action := Leave270BarrelBits.byDigits 0 x t (m.drop (measurementCount p)) small data cold
    (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel))
  have initial : x = adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨(by simpa only [Fin.val_zero,Nat.shiftLeft_zero] using action.bits),action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 106 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave270NearHigh

end

/- middle: certified source line 5746. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270NearMiddle
open Arithmetic Partial Leave270Barrel Leave270High Leave270Word Leave270Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := (((leave270.drop 334).take 1897))
abbrev lastPart := (((leave270.drop 2233).take 107))
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := (((leave270.drop 334).take 2006))

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (_off : ∀ q ∈ Leave270Join.tags, s.basis q=false),
    let x := adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597)
    Result wire 121 x s (run early m s))
    (wordLaw : ∀ (X : Nat) (_bound : X<2^18) (s : State) (m : List Bool)
    (_off : ∀ q ∈ tags, s.basis q=false)
    (_shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=false)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1701=false)
    (scratch : s.basis 1614=false) :
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 121, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 121 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw s m clean selectZero padding off
  have bankZero : adjusted (regValue ys s.basis) 106 (s.basis 1701) (s.basis 1597) = 0 := by
    rw [bank,crossZero]
    cases s.basis 1597 <;> decide
  have bits (i : Fin 121) : v.basis (wire i.val)=false := by
    simpa only [bankZero,Nat.zero_testBit] using a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 121, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 121, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 423+j.val≠1613 ∧ ∀ i : Fin 121, 423+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 121) : 1613 ≠ wire i.val := Leave270Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=false := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (off q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (423+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=false := by
    let j : Fin 121 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have word := wordLaw X bound u tape readTags readShadow readTube zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 121, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 106 ≤ i → i < 121 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (423+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1701=false)
    (scratch : s.basis 1614=false) :
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 121, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 121 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave270NearHigh.result Leave270NearWord.combine X bound s m clean selectZero padding off shadow bank crossZero scratch
end ECDSAAdd.Entrant.StairPacket.Leave270NearMiddle

end

/- middle: certified source line 6096. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270OutputPorts
open Arithmetic Leave270Word Leave270Barrel LeaveCompanion270
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def live (i : Nat) : Wire := if h : i<18 then (row ⟨i,h⟩).keep else wire i
def scanned := 431::432::pendingPairs.map Prod.fst

theorem outputRegisters (s : State) (Z : Nat) (bits : ∀i<121, s.basis (live i)=Z.testBit i) :
    regValue smallA s.basis=Z%2^11 ∧ regValue scanned s.basis=(Z/2^8)%2^113 := by
  constructor
  · apply EnterProof.value_of_bits smallA
    intro i hi
    have h : ∀i:Fin 11,smallA.getD i 0=live i := by decide +kernel
    rw [h ⟨i,hi⟩]
    exact bits i (by change i<11 at hi;omega)
  · apply EnterProof.value_of_bits scanned
    intro i hi
    have h : ∀i:Fin 113,scanned.getD i 0=live (8+i.val) := by decide +kernel
    rw [h ⟨i,hi⟩,Nat.testBit_div_two_pow,Nat.add_comm i 8]
    apply bits
    change i<113 at hi
    omega

theorem activeBits (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=(2^k.val*H+X%2^k.val).testBit i.val)
    (hi : ∀i:Fin 121,18 ≤ i.val → s.basis (wire i.val)=(2^k.val*H).testBit i.val) :
    ∀i<121,s.basis (live i)=(2^k.val*H+X%2^k.val).testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h)]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i=false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a,Bool.false_xor] using z.2

theorem inactiveBits (X : Nat) (small : X<2^18) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=X.testBit i.val)
    (hi : ∀i:Fin 121,18 ≤ i.val → s.basis (wire i.val)=false) :
    ∀i<121,s.basis (live i)=X.testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h),Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

end ECDSAAdd.Entrant.StairPacket.Leave270OutputPorts

end

/- tail: certified source line 7173. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Relocated
open Partial LeaveRelocation Leave270OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def moves : List (Wire×Wire) := [(934, 919), (935, 920), (936, 921), (937, 922), (938, 923), (939, 924), (940, 925), (941, 926), (942, 927), (943, 928), (944, 929), (945, 930), (946, 931), (947, 932), (948, 933), (949, 934), (950, 935), (951, 936), (952, 937), (953, 938), (954, 939), (955, 940), (956, 941), (957, 942), (958, 943), (959, 944), (960, 945), (961, 946), (962, 947), (963, 948), (964, 949), (965, 950), (966, 951), (967, 952), (968, 953), (969, 954), (970, 955), (971, 956), (972, 957), (973, 958), (974, 959), (975, 960), (976, 961), (977, 962), (978, 963), (979, 964), (980, 965), (981, 966), (982, 967), (983, 968), (984, 969), (985, 970), (986, 971), (987, 972), (988, 973), (989, 974), (990, 975), (991, 976), (992, 977), (993, 978), (994, 979), (995, 980), (996, 981), (997, 982), (998, 983), (999, 984), (1000, 985), (1001, 986), (1002, 987), (1003, 988), (1004, 989), (1005, 990), (1006, 991), (1007, 992), (1008, 993), (1009, 994), (1010, 995), (1011, 996), (1012, 997), (1013, 998), (1014, 999), (1015, 1000), (1016, 1001), (1017, 1002), (1018, 1003), (1019, 1004), (1020, 1005), (1021, 1006), (1022, 1007), (1023, 1008), (1024, 1009), (1025, 1010), (1026, 1011), (1027, 1012), (1028, 1013), (1557, 1691), (1558, 1692), (1700, 1693), (1698, 1694), (1702, 1695), (1701, 1696)]
def lastPart := leave270.drop 3066
def firstBack := leaveInv270.take 303
theorem emitted : lastPart=program moves := by decide +kernel
theorem inverseEmitted : firstBack=program moves.reverse := by decide +kernel
theorem properMoves : ∀p∈moves,p.1≠p.2 := by decide +kernel

theorem forward (s : State) (m : List Bool) :
    run lastPart m s=⟨s.phase,fun q=>s.basis (source moves q)⟩ := by
  rw [emitted];exact actual moves properMoves s m

theorem reverse (s : State) (m n : List Bool) : run firstBack n (run lastPart m s)=s := by
  rw [forward,inverseEmitted,actual _ (by simpa using properMoves)]
  cases s with
  | mk phase basis => exact congrArg (State.mk phase) (funext (fun q=>congrArg basis (undoSources moves q)))

theorem upperMap : ∀i:Fin 95,source moves (919+i.val)=live (11+i.val) ∧
    source moves (434+i.val)=434+i.val := by
  have lo : ∀ p ∈ moves, 885 ≤ p.1 ∧ 885 ≤ p.2 := by decide +kernel
  have hi : ∀ i : Fin 95, ECDSAAdd.Entrant.WSlimMain.sourceR moves (919+i.val) = live (11+i.val) := by decide +kernel
  intro i
  exact ⟨(ECDSAAdd.Entrant.WSlimMain.source_eq_sourceR _ _).trans (hi i),
    ECDSAAdd.Entrant.WSlimMain.source_fresh_of_lt lo (by omega)⟩

theorem rails (s : State) (m : List Bool) (Z : Nat)
    (pos:∀i:Fin 95,s.basis (live (11+i.val))=Z.testBit (11+i.val))
    (zero:∀i:Fin 95,s.basis (434+i.val)=false) (i:Fin 95) :
    let v:=run lastPart m s
    v.basis (434+i.val)=false ∧ v.basis (919+i.val)=Z.testBit (11+i.val) := by
  rw [forward];simp only [(upperMap i).1,(upperMap i).2,zero i,pos i,and_self]

theorem flags (s : State) (m : List Bool) :
    let v:=run lastPart m s
    v.basis 1691=s.basis 1557 ∧ v.basis 1692=s.basis 1558 ∧ v.basis 1693=s.basis 1700 ∧ v.basis 1694=s.basis 1698 ∧ v.basis 1695=s.basis 1702 ∧ v.basis 1696=s.basis 1701 ∧ v.basis 1812=s.basis 1812 := by
  rw [forward];exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave270Relocated
end

/- tail: certified source line 9577. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Close
open Arithmetic Partial RailPair Leave270Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def history : List Wire := [286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300]
def low : List (Wire×Wire) := [(422, 907), (423, 908), (424, 909), (425, 910), (426, 911), (427, 912), (428, 913), (429, 914), (430, 915), (431, 916), (432, 917), (433, 918)]
def events : List (Wire×Wire) := [(1799, 1556), (1798, 1559), (1797, 1560), (1796, 1561), (1795, 1562)]
def beforeTags := ((leave270.drop 2982).take 63)
def afterLow := leave270.drop 3045
def ending := leave270.drop 2982

theorem lowShape : beforeTags=notRegister history++store 300 1700 low [] := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem tailShape : afterLow=LeaveNoSwap.block 1702 1699 events++lastPart := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem split : ending=beforeTags++afterLow := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_drop, eq_self, ending, beforeTags, afterLow]

theorem lowResult (s:State) (m:List Bool) :
    let h:=fun q=>if q∈history then !s.basis q else s.basis q
    let t:=run beforeTags m s
    t.phase=s.phase ∧ (∀q,q∉sites low → t.basis q=h q) ∧
      ∀p∈low,t.basis p.1=(if h 300 then h p.2 ^^ h 1700 else h p.1) ∧
        t.basis p.2=(if h 300 then h p.1 else h p.2 ^^ h 1700) := by
  dsimp only
  rw [lowShape,run_append,run_take,notRegister_correct _ (by decide)]
  let h:State:=⟨s.phase,fun q=>if q∈history then !s.basis q else s.basis q⟩
  have geom : StoreGeometry 300 1700 low [] := by constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have act:=store_run 300 1700 low [] geom h (m.drop (measurementCount (notRegister history))) (by simp)
  exact ⟨act.1,fun q no=>act.2.1 q no (by simp [sites]),act.2.2.2⟩

theorem after (s:State) (m:List Bool) (cold:∀p∈events,s.basis p.2=false) :
    let toggled:=s.basis 1699 ^^ (s.basis 1702 && events.all (fun p=> !s.basis p.1))
    run afterLow m s=⟨s.phase,fun q=>(writeBit s.basis 1699 toggled) (LeaveRelocation.source moves q)⟩ := by
  rw [tailShape,run_append,run_take,LeaveNoSwap.action _ _ _ _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) cold,Leave270Relocated.forward]

end ECDSAAdd.Entrant.StairPacket.Leave270Close
end

/- front: certified source line 9617. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def pairs : List (Wire×Wire) := [(422, 907), (423, 908), (424, 909), (425, 910), (426, 911), (427, 912), (428, 913), (429, 914), (430, 915), (431, 916), (432, 917), (433, 918), (434, 919), (435, 920), (436, 921), (437, 922), (438, 923), (439, 924), (440, 925)]
def scanPart := (leave270.take 78)
abbrev L := IntegerPacket.ports (shape 13) 15
theorem emitted : scanPart=scan 440 925 300 1700 pairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem layout : ScanGeometry 440 925 300 1700 pairs := ⟨by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel),by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel),by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel),by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)⟩

theorem result (s : State) (tape : List Bool) (u v : Nat) (G sg : Bool)
    (ready : onRails 13 15 (SkywalkRails.encode G sg u v) s.basis) (fresh:s.basis 1700=false) :
    let t:=run scanPart tape s
    let e:=negative sg u
    t.phase=s.phase ∧ t.basis 1700=e ∧
      (∀i<19,t.basis (422+i)=((u+v)/2^121).testBit i ∧ t.basis (907+i)=((u-e.toNat)/2^121).testBit i) ∧
      ∀q,q≠1700 → q∉sites pairs → t.basis q=s.basis q := by
  rw [emitted]
  have out:=scanRouted 13 121 440 925 300 1700 pairs layout (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) s tape u v G sg ready fresh (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  have frame:=scan_run _ _ _ _ _ layout s tape fresh
  refine ⟨frame.1,out.1,?_,frame.2.2.1⟩
  intro i hi
  have geom : ∀j:Fin 19,(pairs.map Prod.fst).getD j 0=422+j.val ∧ (pairs.map Prod.snd).getD j 0=907+j.val := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  let ix:Fin 19:=⟨i,hi⟩
  rw [←(geom ix).1,←(geom ix).2,HighBankAdjust.bit_read (pairs.map Prod.fst) ix (run (scan 440 925 300 1700 pairs) tape s).basis hi,HighBankAdjust.bit_read (pairs.map Prod.snd) ix (run (scan 440 925 300 1700 pairs) tape s).basis hi,out.2.1,out.2.2]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave270InputScan

end

/- front: certified source line 9651. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion270 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

def openPart:Program := ((leave270.drop 169).take 3)
def interior:Program := ((leave270.drop 172).take 2304)
def closePart:Program := ((leave270.drop 2476).take 3)
theorem openShape : openPart=[.X 1557,.CX 422 1557,.CCX 907 1557 1558] := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem closeShape : closePart=[.measureX 1558 [] [.CZ 907 1557],.CX 422 1557,.X 1557] := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem layout : ∀q∈[422,907,1557,1558],q∉interior.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem released (s:State) (m₀ m₁ m₂:List Bool) (x:s.basis 1557=false) (y:s.basis 1558=false) :
    let u:=run openPart m₀ s
    let v:=run interior m₁ u
    run closePart m₂ v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let u:=run openPart m₀ s
  let v:=run interior m₁ u
  have fresh:u=⟨s.phase,writeBit (writeBit s.basis 1557 (!s.basis 422)) 1558 (s.basis 907 && !s.basis 422)⟩ := by
    change run openPart m₀ s=_
    rw [openShape]
    exact mask_open 422 907 1557 1558 s m₀ (by decide) x y
  have kept (q:Wire) (h:q∈[422,907,1557,1558]) : v.basis q=u.basis q :=
    preserved interior u m₁ q (layout q h)
  dsimp only
  rw [closeShape]
  apply mask_close _ _ _ _ _ _ (by decide)
  · change v.basis 1557= !v.basis 422
    rw [kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
  · change v.basis 1558=(v.basis 907 && v.basis 1557)
    rw [kept _ (by decide),kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
end ECDSAAdd.Entrant.StairPacket.Leave270MaskThrough

end

/- front: certified source line 9690. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave270Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem preparedState (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1698) (s.basis 1699) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    run (fullPrefix inv) m s = ⟨s.phase,fun q=>(sim (if inv then prepareInv else prepare) (LeaveSelector.start ports inv k) q).read v⟩ := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  exact allSites ports 1698 1699 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange

theorem tagCertificate : ∀k:Mode, ∀i:Fin 16,
    sim prepare (LeaveSelector.start ports false k) (Leave270Join.tags.getD i 0) = .bit (enabled k && decide (i.val=key k)) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem selected (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1698) (s.basis 1699) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports false k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) (i:Fin 16) :
    (run (fullPrefix false) m s).basis (Leave270Join.tags.getD i 0)=
      (enabled k && decide (i.val=key k)) := by
  rw [preparedState false s m v small k mode a b input exchange]
  exact congrArg (Expr.read v) (tagCertificate k i)

end ECDSAAdd.Entrant.StairPacket.Leave270Selector

end

/- middle: certified source line 9725. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Readout
open Arithmetic Partial LeaveCompanion270 Leave270OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev throughRestore := (((leave270.drop 2340).take 139))

theorem retained (s : State) (m : List Bool) (i : Fin 121) :
    (run throughRestore m s).basis (live i)=s.basis (live i) := by
  have layout : ∀j:Fin 121,live j∉throughRestore.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  exact preserved _ _ _ _ (layout i)

theorem nextFlag (s : State) (m m' : List Bool) (Z : Nat) (bound : Z<2^121)
    (bits : ∀i<121,s.basis (live i)=Z.testBit i)
    (fresh : (run throughRestore m s).basis 1558=false)
    (clean : ∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (3 ≤ Z/2^8))⟩ := by
  let v:=run throughRestore m s
  have valid (i : Nat) (h : i<121) : v.basis (live i)=Z.testBit i :=
    (retained s m ⟨i,h⟩).trans (bits i h)
  have read := (outputRegisters v Z valid).2
  have fits : Z/2^8<2^113 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
  rw [Nat.mod_eq_of_lt fits] at read
  dsimp only
  rw [←read]
  exact pending_three v m' fresh clean

end ECDSAAdd.Entrant.StairPacket.Leave270Readout

end

/- middle: certified source line 9863. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave270Join Leave270Word Leave270High Leave270Barrel Leave270OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev r (z : SkywalkNat.State) := reduced 121 15 z
def key (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^121≤z.u then 0 else wait 15 z.u,by have h:=wait_le 15 z.u;split <;> omega⟩
def X (z : SkywalkNat.State) := total (step^[15] (r z))/2^122
def F (z : SkywalkNat.State) := total (step^[15] z)/2^122
def d (z : SkywalkNat.State) := X z/2^(key z).val
def neg (z : SkywalkNat.State) := cross (d z) && (!(decide (2^121≤z.u)) && negative (oddBits (letters 15 (r z))))

/-- The actual word-update segment, from its physical input registers to every
    output bit of the true fifteen-tick sum and all retired column sites. -/
theorem actual (z : SkywalkNat.State) (s : ECDSAAdd.State) (m : List Bool)
    (small : min z.u z.v<2^121) (odd : z.v%2=1) (room : high 121 15 z+1<2^106)
    (clean : ∀q∈carries,s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (tag : ∀q∈tags,s.basis q=if far 121 15 z then hot (key z) q else false)
    (shadow : ∀i<18,s.basis (423+i)=(X z).testBit i)
    (bank : regValue ys s.basis=if far 121 15 z then high 121 15 z else 0)
    (cin : s.basis 1701=if far 121 15 z then cross (d z) else false)
    (sign : far 121 15 z → s.basis 1597=neg z) (scratch : s.basis 1614=false) :
    let u:=run Leave270Middle.middle m s
    u.phase=s.phase ∧ (∀i<121,u.basis (live i)=(F z).testBit i) ∧
      (∀i:Fin 18,u.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 121 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → u.basis q=s.basis q := by
  dsimp only
  by_cases f : far 121 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveShadowRails.far_result 121 106 z small f odd room
    change d z=(cross (d z)).toNat+2*(!neg z).toNat ∧ F z=2^(key z).val*HighBankAdjust.adjusted (high 121 15 z) 106 (cross (d z)) (neg z)+X z%2^(key z).val at law
    rw [←cin,←sign f,←bank] at law
    have out := Leave270Middle.result (key z) (X z) s m clean selectZero padding tag shadow law.1 scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [law.2]
    exact activeBits _ _ _ _ (fun i=>(out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have law := LeaveShadowRails.near_result 121 z f
    have eq : X z=F z := by unfold X F r;rw [law.1]
    have bound : X z<2^18 := eq ▸ law.2
    have out := Leave270NearMiddle.result (X z) bound s m clean selectZero padding tag shadow bank cin scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [←eq]
    exact inactiveBits _ bound _ (fun i=>(out.2.1 i).1) out.2.2.1

end ECDSAAdd.Entrant.StairPacket.Leave270TrueMiddle

end

/- front: certified source line 11115. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion270
set_option maxRecDepth 50000

theorem decode (s : State) (u v sign : Nat) (magFit : (u-sign)/2^121<2^19)
    (bits : ∀i<19,s.basis (422+i)=((u+v)/2^121).testBit i ∧ s.basis (907+i)=((u-sign)/2^121).testBit i) :
    ((digits 907 longPairs).any s.basis = decide (2^121≤u-sign)) ∧
      (s.basis 907 && !s.basis 422).toNat=upperBorrow (2^121) u v sign ∧
      regValue fullA s.basis=((u+v)/2^122)%2^18 ∧
      regValue fullM s.basis=((u-sign)/2^122)%2^18 := by
  have mag := EnterProof.value_of_bits (digits 907 longPairs) s.basis ((u-sign)/2^121) (by
    intro i hi
    have geom : ∀j:Fin 19,(digits 907 longPairs).getD j 0=907+j.val := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [geom ⟨i,hi⟩]
    exact (bits i hi).2)
  rw [show (digits 907 longPairs).length=19 from rfl,Nat.mod_eq_of_lt magFit] at mag
  refine ⟨?_,?_,?_,?_⟩
  · rw [any_positive,mag]
    simp only [Nat.div_pos_iff,show 0<2^121 by decide,true_and]
  · have bs := bits 0 (by decide)
    simpa only [Nat.add_zero,bs.1,bs.2] using borrowBit (2^121) u v sign (by decide)
  · apply EnterProof.value_of_bits fullA
    intro i hi
    have geom : ∀j:Fin 18,fullA.getD j 0=422+(j.val+1) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [geom ⟨i,hi⟩,show (u+v)/2^122=((u+v)/2^121)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).1
  · apply EnterProof.value_of_bits fullM
    intro i hi
    have geom : ∀j:Fin 18,fullM.getD j 0=907+(j.val+1) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [geom ⟨i,hi⟩,show (u-sign)/2^122=((u-sign)/2^121)/2^1 by rw [Nat.div_div_eq_div_mul];rfl,Nat.testBit_div_two_pow]
    have jj : i+1<19 := Nat.succ_lt_succ (show i<18 from hi)
    exact (bits (i+1) jj).2

end ECDSAAdd.Entrant.StairPacket.Leave270CompanionInput

end

/- tail: certified source line 11155. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion270 Leave270OutputPorts
open Leave270Readout
attribute [local irreducible] SkywalkNat.step

def endpoint (z:SkywalkNat.State) := step^[15] z

theorem value (z:SkywalkNat.State) :
    Leave270TrueMiddle.F z/2^8=Shadow.high 114 15 (endpoint z) := by
  change ((endpoint z).u+(endpoint z).v)/2^122/2^8=_ 
  rw [Nat.div_div_eq_div_mul]
  rfl

theorem physical (z:SkywalkNat.State) (s:ECDSAAdd.State) (m m':List Bool)
    (bound:Leave270TrueMiddle.F z<2^121)
    (bits:∀i<121,s.basis (live i)=(Leave270TrueMiddle.F z).testBit i)
    (fresh:(run throughRestore m s).basis 1558=false)
    (clean:∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (Shadow.far 114 15 (endpoint z)))⟩ := by
  dsimp only
  rw [nextFlag s m m' _ bound bits fresh clean,value]
  rfl

theorem boundNear (a:SkywalkNat.State) (sign:Nat) (near:¬Shadow.far 114 15 a) :
    a.u-sign<(2*2^121)*2^smallM.length := by
  apply near_bound a.u a.v sign (Shadow.limb 114 15) _ (by decide) (by decide)
  simpa only [decide_eq_false_iff_not] using near

theorem orientation (a:SkywalkNat.State) (sign:Nat) (bit:sign≤1)
    (small:min a.u a.v<2^114) (far:Shadow.far 114 15 a) :
    (2^121≤a.u-sign) ↔ (2^114≤a.u) := by
  have lower:= (Nat.le_div_iff_mul_le (by decide : 0<Shadow.limb 114 15)).mp far
  change 3*2^130≤a.u+a.v at lower
  omega

end ECDSAAdd.Entrant.StairPacket.Leave270NextFlagTruth
end

/- tail: certified source line 11197. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Posted
open Leave270Close Leave270Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s:State) (m:List Bool) (f u c:Bool) (w:Fin 16) (xs:List (Bool×Bool))
    (len:xs.length=15) (chainOK:f=true → chain u xs)
    (first:f=true → u=false → ∀i(h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val))
    (swaps:events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1698=f) (old:s.basis 1699=(f && u)) (suffix:s.basis 1702=nearby (ofFlags f u w))
    (cross:s.basis 1701=(f && c)) (cold:∀p∈events,s.basis p.2=false) :
    let out:=run afterLow m s
    out.phase=s.phase ∧ out.basis 1694=f ∧ out.basis 1695=(f && afterFlags u (xs.take 5)) ∧
      out.basis 1696=(f && c) ∧
      ∀q,out.basis q=writeBit s.basis 1699 false (LeaveRelocation.source moves q) := by
  have vp:=LeavePendingHistory.pending f u xs w len chainOK first
  have ev:events.all (fun p=> !s.basis p.1)= !(xs.take 5).any Prod.snd := by
    have mapped:events.any (fun p=>s.basis p.1)=(xs.take 5).any Prod.snd := by
      simpa only [List.any_map,Function.comp_def,id_eq] using congrArg (List.any · id) swaps
    rw [←mapped]
    simp only [List.all_eq_not_any_not,Bool.not_not]
  have cleared: (s.basis 1699 ^^ (s.basis 1702 && events.all (fun p=> !s.basis p.1)))=false := by
    rw [old,suffix,ev];exact vp.2
  rw [after _ _ cold]
  dsimp only
  rw [cleared]
  have geom:LeaveRelocation.source moves 1694=1698 ∧ LeaveRelocation.source moves 1695=1702 ∧ LeaveRelocation.source moves 1696=1701 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  rw [geom.1,geom.2.1,geom.2.2]
  exact ⟨rfl,far,suffix.trans vp.1,cross,fun _=>rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave270Posted
end

/- front: certified source line 11233. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270RetireActual
open Arithmetic LeaveSelector Leave270Selector Leave270Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def paritySites := List.range' 286 15
def prior (k:Mode) := sim prepare (LeaveSelector.start ports false k)

theorem controls : ∀k:Mode,∀j:Fin 38,
    post ports prepare false k (1559+j.val)=prior k (1559+j.val) ∧
    ∀q∈refs (prior k (1559+j.val)),q∈paritySites := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem signed : ∀k:Mode,∀q∈refs (signExpr ports k),q∈paritySites := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem result (k:Mode) (v:BasisState) (s:State) (m:List Bool)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read v)
    (history:∀q∈paritySites,v q=s.basis q)
    (product:s.basis 1597=(s.basis 1701 && (signExpr ports k).read v))
    (l:left k=(s.basis 1698 && s.basis 1699)) (r:right k=(s.basis 1698 && !s.basis 1699))
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
      have form : post ports prepare false k 1597=conj (.wire 1701) (signExpr ports k) := rfl
      rw [form,read_conj,←sign];exact product
    · have outside:q<1559 ∨ 1597<q:=by omega
      have plain:post ports prepare false k q=.wire q := by
        apply postOutside _ _ _ _ outside
        intro cx nr member
        have cover:∀t∈prepare.map Op.dst,(1559≤t ∧ t≤1597) ∨ t=ports.crossing ∨ t=ports.near := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
        rcases cover q member with h|h|h
        · change 1559 ≤ q ∧ q ≤ 1597 at h;omega
        · exact cx h
        · exact nr h
      rw [plain];rfl
  rw [retiredFull false k s m s.basis input l r exchange,retiredBasis _ _ _ (by decide) (by decide)]

end ECDSAAdd.Entrant.StairPacket.Leave270RetireActual

end

/- middle: certified source line 11282. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270SignClose
open Arithmetic Partial Leave270Middle Leave270High Leave270Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def closeSign : Program := [.CX 1597 1613,.X 1613]
def extended := middle++closeSign

private theorem startBits (s:State) (m:List Bool) (h:s.basis 1613=false) :
    (run signBit m s).basis 1597=s.basis 1597 ∧ (run signBit m s).basis 1613= !s.basis 1597 := by
  simp [run,writeBit,Function.update,h]

private theorem finish (u:State) (m:List Bool) (h:u.basis 1613= !u.basis 1597) :
    run closeSign m u=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply congrArg (State.mk u.phase)
  funext q
  by_cases eq:q=1613 <;> simp [Function.update,writeBit,h,eq]

theorem result (s:State) (m:List Bool) (initial:(run first m s).basis 1613=false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  let a:=run first m s
  let f:=m.drop (measurementCount first)
  let v:=run signBit f a
  have eq:run middle m s=run lastPart f v := by
    rw [Leave270Middle.split,run_append,run_take,run_append,run_take]
    rfl
  have after (q:Wire) (h:q∉lastPart.map destination) :
      (run middle m s).basis q=v.basis q := by rw [eq];exact preserved lastPart v f q h
  have start:=startBits a f initial
  have flag:=(after 1597 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))).trans start.1
  have work:=(after 1613 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))).trans start.2
  dsimp only
  rw [extended,run_append,run_take]
  apply finish
  rw [flag,work]

theorem closed (z:SkywalkNat.State) (s:State) (m:List Bool)
    (clean:∀q∈carries,s.basis q=false) (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (tags:∀q∈Leave270Join.tags,s.basis q=if Shadow.far 121 15 z then Leave270Word.hot (Leave270TrueMiddle.key z) q else false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply result
  have zero:=clean 1613 (by decide)
  by_cases far:Shadow.far 121 15 z
  · simp only [if_pos far] at tags
    have h:=Leave270High.result (Leave270TrueMiddle.key z) s m clean zero padding tags
    exact (h.frame _ Leave270Shift.layout3.separate).trans zero
  · simp only [if_neg far] at tags
    have h:=Leave270NearHigh.result s m clean zero padding tags
    exact (h.frame _ Leave270Shift.layout3.separate).trans zero

end ECDSAAdd.Entrant.StairPacket.Leave270SignClose

end

/- tail: certified source line 11340. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

abbrev L:=W.compactSkywalkTickLayout base 285
abbrev shortL:=IntegerPacket.ports (shape 13) 15

theorem shortMapping (i:Fin 121):
    windowNet 13 (shortL.a.getD i.val 0)=301+i.val ∧
    windowNet 13 (shortL.b.getD i.val 0)=786+i.val := by
  have h1 : (shortL.a.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (shortL.b.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  revert i
  simp only [ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem wideMapping (i:Fin 228):
    L.a.getD i.val 0=OB5.sig 284 (301+i.val) ∧
    L.b.getD i.val 0=OB5.sig 284 (786+i.val) := by
  have h1 : (L.a.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (L.b.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  revert i
  simp only [ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem wide (a:SkywalkNat.State) (G sg:Bool) (raw:State)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis)
    (i:Fin 228) :
    let o:=pullState (OB5.sig 284) raw
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    o.basis (301+i.val)=(if G then neg else pos) ∧ o.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:228≤L.a.length:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have maxB:228≤L.b.length:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h:=pair L G sg a.u a.v i.val raw.basis input.1 input.2.1 input.2.2.1
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  rw [(wideMapping i).1,(wideMapping i).2] at h
  exact h

theorem short (a:SkywalkNat.State) (G sg:Bool) (s:State)
    (ready:onRails 13 15 (SkywalkRails.encode G sg a.u a.v) s.basis) (i:Fin 121) :
    let e:=negative sg a.u
    let pos:=(a.u+a.v).testBit i.val
    let neg:=(a.u-e.toNat).testBit i.val ^^ e
    s.basis (301+i.val)=(if G then neg else pos) ∧ s.basis (786+i.val)=(if G then pos else neg) := by
  have maxA:121≤shortL.a.length:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have maxB:121≤shortL.b.length:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have prev:mappedBasis 13 s.basis shortL.previous=G:=by cases G <;> exact ready.2.2.1
  have h:=pair shortL G sg a.u a.v i.val (mappedBasis 13 s.basis) ready.1 ready.2.1 prev
    (Nat.lt_of_lt_of_le i.isLt maxA) (Nat.lt_of_lt_of_le i.isLt maxB)
  unfold mappedBasis at h
  dsimp only at h
  rw [(shortMapping i).1,(shortMapping i).2] at h
  exact h
end ECDSAAdd.Entrant.StairPacket.Leave270WideWords
end

/- middle: certified source line 12457. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Core
open Arithmetic Partial Leave270SignClose Leave270Selector LeaveSelector Leave270Barrel Leave270High Leave270Word Leave270Join
open HighBankBarrel Leave270RetireActual Leave270OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def work:=(((leave270.drop 334).take 2078))
theorem shape : work=extended++fullPostfix false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def watched := (List.range' 1559 39)++paritySites++[1701,1698,1699]++(List.range 15).map Leave270Hit.swaps

theorem untouched : ∀q∈watched,q≠1613 ∧ (∀i:Fin 121,q≠wire i.val) ∧
    ∀a∈columns,q≠a.shadow ∧ q≠a.tube := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

attribute [local irreducible] run

private theorem finish (z:SkywalkNat.State) (s a t:State)
    (fix:t=⟨a.phase,writeBit a.basis 1613 false⟩) (clean:s.basis 1613=false)
    (ar:a.phase=s.phase ∧ (∀i<121,a.basis (live i)=(Leave270TrueMiddle.F z).testBit i) ∧
      (∀i:Fin 18,a.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 121 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → a.basis q=s.basis q) :
    t.phase=s.phase ∧ (∀i<121,(cleared t.basis) (live i)=(Leave270TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,(cleared t.basis) (row j).free=false) ∧ (∀j:Fin 39,(cleared t.basis) (1559+j.val)=false) ∧
      (∀q,outside wire 121 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → (cleared t.basis) q=cleared s.basis q) := by
  have base (q:Wire) (diff:q≠1613) : t.basis q=a.basis q := by rw [fix];simp [writeBit,diff]
  have pass (q:Nat) (diff:q≠1613 ∧ ¬(1559≤q ∧ q≤1597)) : cleared t.basis q=a.basis q := by
    rw [cleared,if_neg diff.2];exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1,?_,?_,?_,?_⟩
  · intro i h
    have geom : ∀j:Fin 121,live j≠1613 ∧ ¬(1559≤live j ∧ live j≤1597) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (pass _ (geom ⟨i,h⟩)).trans (ar.2.1 i h)
  · intro j
    have geom : ∀j:Fin 18,(row j).free≠1613 ∧ ¬(1559≤(row j).free ∧ (row j).free≤1597) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (pass _ (geom j)).trans (ar.2.2.1 j)
  · intro j;have h:=j.isLt
    change (if 1559≤1559+j.val ∧ 1559+j.val≤1597 then _ else _)=_
    rw [if_pos (by omega)]
  · intro q out cols
    by_cases eq:q=1613
    · subst q
      change t.basis 1613=s.basis 1613
      rw [fix,clean]
      simp [writeBit]
    · unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2 _ eq out cols)


theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool) (k:Mode) (ref:BasisState)
    (small:min z.u z.v<2^121) (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (tag:∀q∈Leave270Join.tags,s.basis q=if Shadow.far 121 15 z then Leave270Word.hot (Leave270TrueMiddle.key z) q else false)
    (shadow:∀i<18,s.basis (423+i)=(Leave270TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (cin:s.basis 1701=if Shadow.far 121 15 z then HighBankSum.cross (Leave270TrueMiddle.d z) else false)
    (sign:Shadow.far 121 15 z → s.basis 1597=Leave270TrueMiddle.neg z)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read ref)
    (parity:∀q∈paritySites,ref q=s.basis q)
    (product:s.basis 1597=(s.basis 1701 && (signExpr ports k).read ref))
    (leftFlag:left k=(s.basis 1698 && s.basis 1699)) (rightFlag:right k=(s.basis 1698 && !s.basis 1699))
    (events:right k=true → ∀i<15,i≤LeaveSelector.key k → s.basis (Leave270Hit.swaps i)=decide (i=LeaveSelector.key k)) :
    let out:=run work tape s
    out.phase=s.phase ∧ (∀i<121,out.basis (live i)=(Leave270TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
      (∀q,outside wire 121 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → out.basis q=cleared s.basis q) := by
  let a:=run Leave270Middle.middle tape s
  let t:=run extended tape s
  have ar:=Leave270TrueMiddle.actual z s tape small odd room clean (clean _ (by decide)) padding tag shadow bank cin sign (clean _ (by decide))
  have fix:=closed z s tape clean padding tag
  change t=⟨a.phase,writeBit a.basis 1613 false⟩ at fix
  have saved (q:Wire) (mem:q∈watched) : t.basis q=s.basis q := by
    obtain ⟨diff,out,cols⟩:=untouched _ mem
    rw [fix];simp only [writeBit,Function.update_of_ne diff]
    exact ar.2.2.2 q diff (fun i hi=>out ⟨i,hi⟩) cols
  have ctl : ∀j:Fin 39,1559+j.val∈watched := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pa : ∀q∈paritySites,q∈watched := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw : ∀i:Fin 15,Leave270Hit.swaps i∈watched := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have retire:=Leave270RetireActual.result k ref t (tape.drop (measurementCount extended))
    (fun j=>(saved _ (ctl ⟨j.val,by have h:=j.isLt;omega⟩)).trans (bits j))
    (fun q h=>(parity q h).trans (saved _ (pa q h)).symm)
    (by rw [saved 1597 (by decide),saved 1701 (by decide)];exact product)
    (by rw [saved 1698 (by decide),saved 1699 (by decide)];exact leftFlag)
    (by rw [saved 1698 (by decide),saved 1699 (by decide)];exact rightFlag)
    (fun on i hi h=>(saved _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take,retire]
  exact finish z s a t fix (clean _ (by decide)) ar

end ECDSAAdd.Entrant.StairPacket.Leave270Core

end

/- front: certified source line 12552. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion270
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

def program := (((leave270.drop 93).take 149))
theorem emitted : program=long++(mask++erase) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

private theorem joined (L M E : Program) (Lspec : L=long) (Mspec : M=mask) (Espec : E=erase) (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^121) (magFit:(u-sign)/2^121<2^19)
    (bits:∀i<19,s.basis (422+i)=((u+v)/2^121).testBit i ∧ s.basis (907+i)=((u-sign)/2^121).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run (L++(M++E)) tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^121≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^121) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  let half:=2^121
  let l:=run L tape s
  let s1:=tape.drop (measurementCount L)
  let w:=run M s1 l
  let s2:=s1.drop (measurementCount M)
  have d:=Leave270CompanionInput.decode s u v sign magFit bits
  have flag:l=⟨s.phase,writeBit s.basis 1556 (decide (half≤u-sign))⟩ := by
    rw [show l=run L tape s from rfl,Lspec,long_run s tape temps,d.1,clean _ (by simp),Bool.false_xor]
  have base (q:Wire) (h:q≠1556) : l.basis q=s.basis q := by simp [flag,writeBit,h]
  have maskOn : w=⟨l.phase,writeBit (writeBit l.basis 1557 (!l.basis 422)) 1558 (l.basis 907 && !l.basis 422)⟩ := by
    rw [show w=run M s1 l from rfl,Mspec,mask_eq]
    apply mask_open _ _ _ _ _ _ (by decide) <;> rw [base _ (by decide)] <;> exact clean _ (by simp)
  have kept (q:Wire) (h:q∉[1556,1557,1558]) : w.basis q=s.basis q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    simp [maskOn,flag,writeBit,h.1,h.2.1,h.2.2]
  have isLong : w.basis 1556=decide (half≤u-sign) := by simp [maskOn,flag,writeBit]
  have borrow : (w.basis 1558).toNat=upperBorrow half u v sign := by
    simpa only [maskOn,writeBit,Function.update_self,base _ (by decide : 422≠1556),base _ (by decide : 907≠1556)] using d.2.1
  have same (rs : List Wire) (ok : ∀q∈rs,q∉[1556,1557,1558]) : regValue rs w.basis=regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ (ok q h))
  have cs : ∀q∈fullC,w.basis q=false := by
    intro q h; rw [kept q ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈fullC,q∉[1556,1557,1558]) q h)];exact clean _ (by simp [h])
  have condition : (regValue fullM w.basis+(w.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) w.basis (regValue fullA w.basis) := by
    rw [same fullM (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),same fullA (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),d.2.2.1,d.2.2.2,borrow]
    have twice : 2*half=2^122 := (Nat.mul_comm 2 half).trans (Nat.pow_succ 2 121).symm
    have calcValue:=upper_clear half u v sign (2^18) (by decide) se su small
    rw [twice] at calcValue
    simpa only [copyValue,isLong,decide_eq_true_eq] using calcValue
  have e:=LeaveCompanion270.erase_run w s2 cs condition
  rw [←Espec] at e
  dsimp only
  rw [run_append,run_take,run_append,run_take]
  have extern (q:Wire) (notM:q∉fullM) : (run E s2 w).basis q=w.basis q := e.2.1 q notM
  refine ⟨e.1.trans (by simp [maskOn,flag]),e.2.2,(extern _ (by decide)).trans isLong,?_,?_⟩
  · rw [extern _ (by decide)];exact borrow
  · intro q out
    simp only [List.mem_cons,not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1,out.2.1,out.2.2.1]))

theorem result (s : State) (tape : List Bool) (u v sign : Nat)
    (se:sign≤1) (su:sign≤u) (small:min u v<2^121) (magFit:(u-sign)/2^121<2^19)
    (bits:∀i<19,s.basis (422+i)=((u+v)/2^121).testBit i ∧ s.basis (907+i)=((u-sign)/2^121).testBit i)
    (clean:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temps:∀p∈longPairs,s.basis p.2=false) :
    let t:=run program tape s
    t.phase=s.phase ∧ regValue fullM t.basis=0 ∧ t.basis 1556=decide (2^121≤u-sign) ∧
      (t.basis 1558).toNat=upperBorrow (2^121) u v sign ∧
      ∀q,q∉1556::1557::1558::fullM → t.basis q=s.basis q := by
  rw [emitted]
  exact joined long mask erase rfl rfl rfl s tape u v sign se su small magFit bits clean temps

end ECDSAAdd.Entrant.StairPacket.Leave270EraseActual

end

/- middle: certified source line 12626. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Loaded
open Arithmetic LeaveSelector Leave270Selector Leave270RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem physicalTags : ∀k:Mode,∀q∈Leave270Join.tags,
    prior k q=.bit (enabled k && decide (q=Leave270Join.tags.getD (LeaveSelector.key k) 0)) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem tags (z:SkywalkNat.State) (v:BasisState) (q:Wire) (hq:q∈Leave270Join.tags) :
    (prior (actualMode 121 z) q).read v=
      if Shadow.far 121 15 z then Leave270Word.hot (Leave270TrueMiddle.key z) q else false := by
  rw [physicalTags _ _ hq]
  by_cases f:Shadow.far 121 15 z
  · rw [if_pos f]
    obtain ⟨idx,_,on⟩:=modeKey 121 z f
    simp only [Expr.read,on,Bool.true_and,idx]
    rfl
  · simp [f,Expr.read,actualMode,farMode,ofFlags,enabled]

private theorem extract (p:Ports) (k:Mode) (s:Sym) (h:reads p s=controls p k) :
    s p.crossing=crossing p k ∧ s 1597=conj (crossing p k) (signExpr p k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at h
  exact ⟨h.2.1,h.2.2.2⟩

theorem controlsAt (k:Mode) :
    prior k 1701=crossing ports k ∧ prior k 1597=conj (crossing ports k) (signExpr ports k) :=
  extract ports k (prior k) (controlCert k)

theorem signed (z:SkywalkNat.State) (ref:BasisState)
    (small:min z.u z.v<2^121) (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (bits:∀i<16,ref (ports.u+i)=(Leave270TrueMiddle.X z).testBit i)
    (par:parityBits ports ref=oddBits (letters 15 (Shadow.reduced 121 15 z))) :
    let k:=actualMode 121 z
    let s:=fun q=>(prior k q).read ref
    s 1701=(if Shadow.far 121 15 z then HighBankSum.cross (Leave270TrueMiddle.d z) else false) ∧
    s 1597=(s 1701 && (signExpr ports k).read ref) ∧ (Shadow.far 121 15 z → s 1597=Leave270TrueMiddle.neg z) := by
  have h:=trueControls 121 106 z small odd room ports ref bits par
  obtain ⟨cx,gate⟩:=controlsAt (actualMode 121 z)
  dsimp only
  rw [cx,gate,read_conj]
  refine ⟨h.1,rfl,?_⟩
  intro f
  rw [h.1,h.2 f,if_pos f]
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave270Loaded

end

/- middle: certified source line 12677. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion270
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m:List Bool)
    (small:min z.u z.v<2^121) (clean:∀q∈smallC,s.basis q=false) (cleared:regValue smallM s.basis=0)
    (input:let r:=step^[15] (reduced 121 15 z)
           let F:=step^[15] z
           let e:=(negative sg r.u).toNat
           s.basis 1556=decide (2^121≤r.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^121) r.u r.v e ∧
             regValue smallA s.basis=((F.u+F.v)/2^122)%2^11) :
    let F:=step^[15] z
    let e:=(negative sg F.u).toNat
    let out:=run restore m s
    out.phase=s.phase ∧ (∀q,q∉smallM → out.basis q=s.basis q) ∧
      regValue smallM out.basis=((F.u-e)/2^122)%2^11 := by
  have hardware:=restore_run s m clean cleared
  refine ⟨hardware.1,hardware.2.1,hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math:=LeaveRestoreTruth.restored 121 11 z small sg
  have sign:=(LeaveRestoreTruth.truth 121 z small sg).2.2.2
  rw [show smallM.length=11 from rfl,copyValue,input.1,input.2.1,input.2.2,sign]
  simpa only [decide_eq_true_eq] using math

end ECDSAAdd.Entrant.StairPacket.Leave270Restored

end

/- tail: certified source line 12708. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion270 Leave270OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program:Program := ((leave270.drop 2479).take 503)
theorem shape : program=pending++(nextU++clearFlag) := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, eq_self, program, pending, nextU, clearFlag]
attribute [local irreducible] run
theorem result (a:SkywalkNat.State) (s:State) (m:List Bool) (sign:Nat)
    (bit:sign≤1) (small:min a.u a.v<2^114) (x:s.basis 1557=false) (y:s.basis 1558=false)
    (scan:regValue scanned s.basis=Shadow.high 114 15 a)
    (clean:∀p∈pendingPairs,s.basis p.2=false) (scratch:∀p∈clearFlagPairs,s.basis p.2=false)
    (long:s.basis 1556=decide (2^121≤a.u-sign))
    (low:s.basis 907=decide (2^121≤(a.u-sign)%(2*2^121)))
    (upper:regValue smallM s.basis=((a.u-sign)/(2*2^121))%2^smallM.length) :
    let f:=decide (Shadow.far 114 15 a)
    let u:=f && decide (2^114≤a.u)
    run program m s=⟨s.phase,writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  let f:=decide (Shadow.far 114 15 a)
  let u:=f && decide (2^114≤a.u)
  let b₁:=writeBit s.basis 1557 f
  let b₂:=writeBit b₁ 1558 u
  have stage:run pending m s=⟨s.phase,b₁⟩ := by
    rw [pending_three s m y clean,x,Bool.false_xor]
    change (State.mk s.phase (writeBit s.basis 1557 (decide (3≤regValue scanned s.basis))))=_
    rw [scan]; rfl
  have side:(s.basis 1556 && f)=u := by
    by_cases far:Shadow.far 114 15 a
    · simp only [f,u,far,decide_true,Bool.and_true,Bool.true_and,long]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using Leave270NextFlagTruth.orientation a sign bit small far)
    · simp [f,u,far]
  have keep (q:Wire) (h:q≠1557 ∧ q≠1558) : b₂ q=s.basis q := by simp [b₂,b₁,writeBit,h.1,h.2]
  have turn (mm:List Bool):run nextU mm ⟨s.phase,b₁⟩=⟨s.phase,b₂⟩ := by
    rw [nextU_run _ _ (by simpa [b₁,writeBit] using y)]
    simp [b₂,b₁,writeBit,side]
  have last (mm:List Bool):run clearFlag mm ⟨s.phase,b₂⟩=⟨s.phase,writeBit b₂ 1556 false⟩ := by
    apply clearFlag_value _ _ (2^121) (a.u-sign) (by decide)
    · intro p hp
      exact (keep p.2 ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀p∈clearFlagPairs,p.2≠1557 ∧ p.2≠1558) p hp)).trans (scratch p hp)
    · intro h
      apply Leave270NextFlagTruth.boundNear a sign
      simpa [b₂,b₁,writeBit,f] using h
    · exact (keep _ (by decide)).trans long
    · change b₂ 1558=(b₂ 1556 && b₂ 1557)
      simp [b₂,b₁,writeBit,side]
    · exact (keep _ (by decide)).trans low
    · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>keep q ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈smallM,q≠1557 ∧ q≠1558) q h))).trans upper
  dsimp only
  rw [shape,run_append,run_take,stage,run_append,run_take,turn,last]

end ECDSAAdd.Entrant.StairPacket.Leave270TailFlags
end

/- front: certified source line 17335. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion270 Leave270InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def flipHistory := (((leave270.drop 78).take 15))
def entry := leave270.take 242
theorem emitted : entry=scanPart++(flipHistory++Leave270EraseActual.program) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
    let e:=negative sg a.u
    let out:=run entry m s
    out.phase=s.phase ∧ regValue fullM out.basis=0 ∧ out.basis 1700=e ∧
      out.basis 1556=decide (2^121≤a.u-e.toNat) ∧ (out.basis 1558).toNat=upperBorrow (2^121) a.u a.v e.toNat ∧
      ∀i<19,out.basis (422+i)=((a.u+a.v)/2^121).testBit i := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave270InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (422+i)=((a.u+a.v)/2^121).testBit i ∧ v.basis (907+i)=((a.u-e.toNat)/2^121).testBit i := by
    have ok : ∀j:Fin 19,422+j.val∉flipHistory.map destination ∧ 907+j.val∉flipHistory.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1700 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 121 z small
  have fit : (a.u-e.toNat)/2^121 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave270EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  dsimp only
  rw [emitted,run_append,run_take,run_append,run_take]
  refine ⟨done.1.trans (phase.trans scanActual.1),done.2.1,?_,done.2.2.1,done.2.2.2.1,?_⟩
  · exact (done.2.2.2.2 _ (by decide)).trans ((hist _ (by decide)).trans scanActual.2.1)
  · intro i hi
    have clear : ∀j:Fin 19,422+j.val∉1556::1557::1558::fullM := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (done.2.2.2.2 _ (clear ⟨i,hi⟩)).trans (outputBits i hi).1

end ECDSAAdd.Entrant.StairPacket.Leave270Front

end

/- mirror: certified source line 17401. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Mirror
open Arithmetic GateMirror Extension270
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
private def block0 : List Gate := [
  .cx 440 1700,
  .cx 925 1700,
  .cx 422 907,
  .ccx 300 907 422,
  .cx 422 907,
  .cx 423 908,
  .ccx 300 908 423,
  .cx 423 908,
  .cx 424 909]
private def block9 : List Gate := [
  .ccx 300 909 424,
  .cx 424 909,
  .cx 425 910,
  .ccx 300 910 425,
  .cx 425 910,
  .cx 426 911,
  .ccx 300 911 426,
  .cx 426 911,
  .cx 427 912,
  .ccx 300 912 427,
  .cx 427 912,
  .cx 428 913,
  .ccx 300 913 428,
  .cx 428 913,
  .cx 429 914,
  .ccx 300 914 429,
  .cx 429 914,
  .cx 430 915,
  .ccx 300 915 430,
  .cx 430 915,
  .cx 431 916,
  .ccx 300 916 431,
  .cx 431 916,
  .cx 432 917,
  .ccx 300 917 432,
  .cx 432 917,
  .cx 433 918,
  .ccx 300 918 433,
  .cx 433 918,
  .cx 434 919,
  .ccx 300 919 434,
  .cx 434 919,
  .cx 435 920,
  .ccx 300 920 435,
  .cx 435 920,
  .cx 436 921,
  .ccx 300 921 436,
  .cx 436 921,
  .cx 437 922,
  .ccx 300 922 437,
  .cx 437 922,
  .cx 438 923,
  .ccx 300 923 438,
  .cx 438 923,
  .cx 439 924,
  .ccx 300 924 439,
  .cx 439 924,
  .cx 440 925,
  .ccx 300 925 440,
  .cx 440 925,
  .cx 1700 907,
  .cx 1700 908,
  .cx 1700 909,
  .cx 1700 910,
  .cx 1700 911,
  .cx 1700 912,
  .cx 1700 913,
  .cx 1700 914,
  .cx 1700 915,
  .cx 1700 916,
  .cx 1700 917,
  .cx 1700 918,
  .cx 1700 919,
  .cx 1700 920,
  .cx 1700 921,
  .cx 1700 922,
  .cx 1700 923,
  .cx 1700 924,
  .cx 1700 925,
  .x 286,
  .x 287,
  .x 288,
  .x 289,
  .x 290,
  .x 291,
  .x 292,
  .x 293,
  .x 294,
  .x 295,
  .x 296,
  .x 297,
  .x 298,
  .x 299,
  .x 300,
  .x 907,
  .x 908,
  .x 909]
private def block96 : List Gate := [
  .x 910,
  .x 911,
  .x 912,
  .x 913,
  .x 914,
  .x 915,
  .x 916,
  .x 917,
  .x 918]
private def block105 : List Gate := [
  .x 919,
  .x 920,
  .x 921,
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .make 907 908 1557,
  .make 1557 909 1558,
  .make 1558 910 1559,
  .make 1559 911 1560,
  .make 1560 912 1561,
  .make 1561 913 1562,
  .make 1562 914 1563,
  .make 1563 915 1564,
  .make 1564 916 1565,
  .make 1565 917 1566,
  .make 1566 918 1567,
  .make 1567 919 1568,
  .make 1568 920 1569,
  .make 1569 921 1570,
  .make 1570 922 1571,
  .make 1571 923 1572,
  .make 1572 924 1573,
  .make 1573 925 1574,
  .cx 1574 1556,
  .x 1556,
  .pop 1573 925 1574,
  .pop 1572 924 1573,
  .pop 1571 923 1572,
  .pop 1570 922 1571,
  .pop 1569 921 1570,
  .pop 1568 920 1569,
  .pop 1567 919 1568,
  .pop 1566 918 1567,
  .pop 1565 917 1566,
  .pop 1564 916 1565,
  .pop 1563 915 1564,
  .pop 1562 914 1563,
  .pop 1561 913 1562,
  .pop 1560 912 1561,
  .pop 1559 911 1560,
  .pop 1558 910 1559,
  .pop 1557 909 1558,
  .pop 907 908 1557,
  .x 925,
  .x 924,
  .x 923,
  .x 922,
  .x 921,
  .x 920,
  .x 919,
  .x 918,
  .x 917,
  .x 916,
  .x 915,
  .x 914,
  .x 913,
  .x 912,
  .x 911,
  .x 910,
  .x 909,
  .x 908,
  .x 907,
  .x 1557,
  .cx 422 1557,
  .make 907 1557 1558,
  .make 908 1558 1559,
  .make 909 1559 1560,
  .make 910 1560 1561,
  .make 911 1561 1562,
  .make 912 1562 1563,
  .make 913 1563 1564,
  .make 914 1564 1565,
  .make 915 1565 1566,
  .make 916 1566 1567,
  .make 917 1567 1568,
  .make 918 1568 1569,
  .make 919 1569 1570,
  .make 920 1570 1571,
  .make 921 1571 1572,
  .make 922 1572 1573,
  .make 923 1573 1574,
  .make 924 1574 1575,
  .cx 1575 925,
  .pop 924 1574 1575,
  .cx 1574 924]
private def block192 : List Gate := [
  .pop 923 1573 1574,
  .cx 1573 923,
  .pop 922 1572 1573,
  .cx 1572 922,
  .pop 921 1571 1572,
  .cx 1571 921,
  .pop 920 1570 1571,
  .cx 1570 920,
  .pop 919 1569 1570]
private def block201 : List Gate := [
  .cx 1569 919,
  .pop 918 1568 1569,
  .cx 1568 918,
  .pop 917 1567 1568,
  .cx 1567 917,
  .pop 916 1566 1567,
  .cx 1566 916,
  .pop 915 1565 1566,
  .cx 1565 915,
  .pop 914 1564 1565,
  .cx 1564 914,
  .pop 913 1563 1564,
  .cx 1563 913,
  .pop 912 1562 1563,
  .cx 1562 912,
  .pop 911 1561 1562,
  .cx 1561 911,
  .pop 910 1560 1561,
  .cx 1560 910,
  .pop 909 1559 1560,
  .cx 1559 909,
  .pop 908 1558 1559,
  .cx 1558 908,
  .ccx 1556 423 908,
  .ccx 1556 424 909,
  .ccx 1556 425 910,
  .ccx 1556 426 911,
  .ccx 1556 427 912,
  .ccx 1556 428 913,
  .ccx 1556 429 914,
  .ccx 1556 430 915,
  .ccx 1556 431 916,
  .ccx 1556 432 917,
  .ccx 1556 433 918,
  .ccx 1556 434 919,
  .ccx 1556 435 920,
  .ccx 1556 436 921,
  .ccx 1556 437 922,
  .ccx 1556 438 923,
  .ccx 1556 439 924,
  .ccx 1556 440 925,
  .make 1698 1699 1559,
  .cx 1698 1560,
  .cx 1559 1560,
  .make 1560 1799 1561,
  .cx 1561 1560,
  .make 1560 1798 1562,
  .cx 1562 1560,
  .make 1560 1797 1563,
  .cx 1563 1560,
  .make 1560 1796 1564,
  .cx 1564 1560,
  .make 1560 1795 1565,
  .cx 1565 1560,
  .make 1560 1794 1566,
  .cx 1566 1560,
  .make 1560 1793 1567,
  .cx 1567 1560,
  .make 1560 1792 1568,
  .cx 1568 1560,
  .make 1560 1791 1569,
  .cx 1569 1560,
  .make 1560 1790 1570,
  .cx 1570 1560,
  .make 1560 1789 1571,
  .cx 1571 1560,
  .make 1560 1788 1572,
  .cx 1572 1560,
  .make 1560 1787 1573,
  .cx 1573 1560,
  .make 1560 1786 1574,
  .cx 1574 1560,
  .make 1560 1785 1575,
  .cx 1575 1560,
  .cx 1559 1702,
  .cx 1561 1702,
  .cx 1562 1702,
  .cx 1563 1702,
  .cx 1564 1702,
  .cx 1565 1702,
  .cx 1559 1576,
  .cx 1561 1576,
  .make 299 300 1577,
  .make 298 1577 1578,
  .make 297 1578 1579,
  .make 296 1579 1580,
  .make 295 1580 1581]
private def block288 : List Gate := [
  .make 294 1581 1582,
  .make 293 1582 1583,
  .make 292 1583 1584,
  .make 291 1584 1585,
  .make 290 1585 1586,
  .make 289 1586 1587,
  .make 288 1587 1588,
  .make 1562 1588 1589,
  .make 1563 1586 1590]
private def block297 : List Gate := [
  .make 1564 1584 1591,
  .make 1565 1582 1592,
  .make 1566 1580 1593,
  .make 1567 1578 1594,
  .make 1568 300 1595,
  .ccx 1576 423 1701,
  .ccx 1562 424 1701,
  .ccx 1563 425 1701,
  .ccx 1564 426 1701,
  .ccx 1565 427 1701,
  .ccx 1566 428 1701,
  .ccx 1567 429 1701,
  .ccx 1568 430 1701,
  .ccx 1569 431 1701,
  .ccx 1570 432 1701,
  .ccx 1571 433 1701,
  .ccx 1572 434 1701,
  .ccx 1573 435 1701,
  .ccx 1574 436 1701,
  .ccx 1575 437 1701,
  .ccx 1560 438 1701,
  .cx 1589 1596,
  .cx 1590 1596,
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .make 1701 1596 1597,
  .cx 1597 1695,
  .cx 1597 1696,
  .cx 1597 1697,
  .cx 1597 926,
  .cx 1597 927,
  .cx 1597 928,
  .cx 1597 929,
  .cx 1597 930,
  .cx 1597 931,
  .cx 1597 932,
  .cx 1597 933,
  .cx 1597 934,
  .cx 1597 935,
  .cx 1597 936,
  .cx 1597 937,
  .cx 1597 938,
  .cx 1597 939,
  .cx 1597 940,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943,
  .cx 1597 944,
  .cx 1597 945,
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972]
private def block384 : List Gate := [
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981]
private def block393 : List Gate := [
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .make 1695 1701 1598,
  .make 1696 1598 1599,
  .make 1697 1599 1600,
  .make 926 1600 1601,
  .make 927 1601 1602,
  .make 928 1602 1603,
  .make 929 1603 1604,
  .make 930 1604 1605,
  .make 931 1605 1606,
  .make 932 1606 1607,
  .make 933 1607 1608,
  .make 934 1608 1609,
  .make 935 1609 1610,
  .make 936 1610 1611,
  .make 937 1611 1612,
  .make 938 1612 1613,
  .make 939 1613 1614,
  .make 940 1614 1615,
  .make 941 1615 1616,
  .make 942 1616 1617,
  .make 943 1617 1618,
  .make 944 1618 1619,
  .make 945 1619 1620,
  .make 946 1620 1621,
  .make 947 1621 1622,
  .make 948 1622 1623,
  .make 949 1623 1624,
  .make 950 1624 1625,
  .make 951 1625 1626,
  .make 952 1626 1627,
  .make 953 1627 1628,
  .make 954 1628 1629,
  .make 955 1629 1630,
  .make 956 1630 1631,
  .make 957 1631 1632,
  .make 958 1632 1633,
  .make 959 1633 1634,
  .make 960 1634 1635,
  .make 961 1635 1636,
  .make 962 1636 1637]
private def block480 : List Gate := [
  .make 963 1637 1638,
  .make 964 1638 1639,
  .make 965 1639 1640,
  .make 966 1640 1641,
  .make 967 1641 1642,
  .make 968 1642 1643,
  .make 969 1643 1644,
  .make 970 1644 1645,
  .make 971 1645 1646]
private def block489 : List Gate := [
  .make 972 1646 1647,
  .make 973 1647 1648,
  .make 974 1648 1649,
  .make 975 1649 1650,
  .make 976 1650 1651,
  .make 977 1651 1652,
  .make 978 1652 1653,
  .make 979 1653 1654,
  .make 980 1654 1655,
  .make 981 1655 1656,
  .make 982 1656 1657,
  .make 983 1657 1658,
  .make 984 1658 1659,
  .make 985 1659 1660,
  .make 986 1660 1661,
  .make 987 1661 1662,
  .make 988 1662 1663,
  .make 989 1663 1664,
  .make 990 1664 1665,
  .make 991 1665 1666,
  .make 992 1666 1667,
  .make 993 1667 1668,
  .make 994 1668 1669,
  .make 995 1669 1670,
  .make 996 1670 1671,
  .make 997 1671 1672,
  .make 998 1672 1673,
  .make 999 1673 1674,
  .make 1000 1674 1675,
  .make 1001 1675 1676,
  .make 1002 1676 1677,
  .make 1003 1677 1678,
  .make 1004 1678 1679,
  .make 1005 1679 1680,
  .make 1006 1680 1681,
  .make 1007 1681 1682,
  .make 1008 1682 1683,
  .make 1009 1683 1684,
  .make 1010 1684 1685,
  .make 1011 1685 1686,
  .make 1012 1686 1687,
  .make 1013 1687 1688,
  .make 1014 1688 1689,
  .make 1015 1689 1690,
  .make 1016 1690 1691,
  .make 1017 1691 1692,
  .make 1018 1692 1693,
  .make 1019 1693 1694,
  .make 1020 1694 1705,
  .make 1021 1705 1706,
  .make 1022 1706 1707,
  .make 1023 1707 1708,
  .make 1024 1708 1709,
  .make 1025 1709 1710,
  .make 1026 1710 1711,
  .make 1027 1711 1712,
  .cx 1712 1028,
  .pop 1027 1711 1712,
  .cx 1711 1027,
  .pop 1026 1710 1711,
  .cx 1710 1026,
  .pop 1025 1709 1710,
  .cx 1709 1025,
  .pop 1024 1708 1709,
  .cx 1708 1024,
  .pop 1023 1707 1708,
  .cx 1707 1023,
  .pop 1022 1706 1707,
  .cx 1706 1022,
  .pop 1021 1705 1706,
  .cx 1705 1021,
  .pop 1020 1694 1705,
  .cx 1694 1020,
  .pop 1019 1693 1694,
  .cx 1693 1019,
  .pop 1018 1692 1693,
  .cx 1692 1018,
  .pop 1017 1691 1692,
  .cx 1691 1017,
  .pop 1016 1690 1691,
  .cx 1690 1016,
  .pop 1015 1689 1690,
  .cx 1689 1015,
  .pop 1014 1688 1689,
  .cx 1688 1014,
  .pop 1013 1687 1688,
  .cx 1687 1013]
private def block576 : List Gate := [
  .pop 1012 1686 1687,
  .cx 1686 1012,
  .pop 1011 1685 1686,
  .cx 1685 1011,
  .pop 1010 1684 1685,
  .cx 1684 1010,
  .pop 1009 1683 1684,
  .cx 1683 1009,
  .pop 1008 1682 1683]
private def block585 : List Gate := [
  .cx 1682 1008,
  .pop 1007 1681 1682,
  .cx 1681 1007,
  .pop 1006 1680 1681,
  .cx 1680 1006,
  .pop 1005 1679 1680,
  .cx 1679 1005,
  .pop 1004 1678 1679,
  .cx 1678 1004,
  .pop 1003 1677 1678,
  .cx 1677 1003,
  .pop 1002 1676 1677,
  .cx 1676 1002,
  .pop 1001 1675 1676,
  .cx 1675 1001,
  .pop 1000 1674 1675,
  .cx 1674 1000,
  .pop 999 1673 1674,
  .cx 1673 999,
  .pop 998 1672 1673,
  .cx 1672 998,
  .pop 997 1671 1672,
  .cx 1671 997,
  .pop 996 1670 1671,
  .cx 1670 996,
  .pop 995 1669 1670,
  .cx 1669 995,
  .pop 994 1668 1669,
  .cx 1668 994,
  .pop 993 1667 1668,
  .cx 1667 993,
  .pop 992 1666 1667,
  .cx 1666 992,
  .pop 991 1665 1666,
  .cx 1665 991,
  .pop 990 1664 1665,
  .cx 1664 990,
  .pop 989 1663 1664,
  .cx 1663 989,
  .pop 988 1662 1663,
  .cx 1662 988,
  .pop 987 1661 1662,
  .cx 1661 987,
  .pop 986 1660 1661,
  .cx 1660 986,
  .pop 985 1659 1660,
  .cx 1659 985,
  .pop 984 1658 1659,
  .cx 1658 984,
  .pop 983 1657 1658,
  .cx 1657 983,
  .pop 982 1656 1657,
  .cx 1656 982,
  .pop 981 1655 1656,
  .cx 1655 981,
  .pop 980 1654 1655,
  .cx 1654 980,
  .pop 979 1653 1654,
  .cx 1653 979,
  .pop 978 1652 1653,
  .cx 1652 978,
  .pop 977 1651 1652,
  .cx 1651 977,
  .pop 976 1650 1651,
  .cx 1650 976,
  .pop 975 1649 1650,
  .cx 1649 975,
  .pop 974 1648 1649,
  .cx 1648 974,
  .pop 973 1647 1648,
  .cx 1647 973,
  .pop 972 1646 1647,
  .cx 1646 972,
  .pop 971 1645 1646,
  .cx 1645 971,
  .pop 970 1644 1645,
  .cx 1644 970,
  .pop 969 1643 1644,
  .cx 1643 969,
  .pop 968 1642 1643,
  .cx 1642 968,
  .pop 967 1641 1642,
  .cx 1641 967,
  .pop 966 1640 1641,
  .cx 1640 966,
  .pop 965 1639 1640,
  .cx 1639 965]
private def block672 : List Gate := [
  .pop 964 1638 1639,
  .cx 1638 964,
  .pop 963 1637 1638,
  .cx 1637 963,
  .pop 962 1636 1637,
  .cx 1636 962,
  .pop 961 1635 1636,
  .cx 1635 961,
  .pop 960 1634 1635]
private def block681 : List Gate := [
  .cx 1634 960,
  .pop 959 1633 1634,
  .cx 1633 959,
  .pop 958 1632 1633,
  .cx 1632 958,
  .pop 957 1631 1632,
  .cx 1631 957,
  .pop 956 1630 1631,
  .cx 1630 956,
  .pop 955 1629 1630,
  .cx 1629 955,
  .pop 954 1628 1629,
  .cx 1628 954,
  .pop 953 1627 1628,
  .cx 1627 953,
  .pop 952 1626 1627,
  .cx 1626 952,
  .pop 951 1625 1626,
  .cx 1625 951,
  .pop 950 1624 1625,
  .cx 1624 950,
  .pop 949 1623 1624,
  .cx 1623 949,
  .pop 948 1622 1623,
  .cx 1622 948,
  .pop 947 1621 1622,
  .cx 1621 947,
  .pop 946 1620 1621,
  .cx 1620 946,
  .pop 945 1619 1620,
  .cx 1619 945,
  .pop 944 1618 1619,
  .cx 1618 944,
  .pop 943 1617 1618,
  .cx 1617 943,
  .pop 942 1616 1617,
  .cx 1616 942,
  .pop 941 1615 1616,
  .cx 1615 941,
  .pop 940 1614 1615,
  .cx 1614 940,
  .pop 939 1613 1614,
  .cx 1613 939,
  .pop 938 1612 1613,
  .cx 1612 938,
  .pop 937 1611 1612,
  .cx 1611 937,
  .pop 936 1610 1611,
  .cx 1610 936,
  .pop 935 1609 1610,
  .cx 1609 935,
  .pop 934 1608 1609,
  .cx 1608 934,
  .pop 933 1607 1608,
  .cx 1607 933,
  .pop 932 1606 1607,
  .cx 1606 932,
  .pop 931 1605 1606,
  .cx 1605 931,
  .pop 930 1604 1605,
  .cx 1604 930,
  .pop 929 1603 1604,
  .cx 1603 929,
  .pop 928 1602 1603,
  .cx 1602 928,
  .pop 927 1601 1602,
  .cx 1601 927,
  .pop 926 1600 1601,
  .cx 1600 926,
  .pop 1697 1599 1600,
  .cx 1599 1697,
  .pop 1696 1598 1599,
  .cx 1598 1696,
  .pop 1695 1701 1598,
  .cx 1701 1695,
  .cx 1597 1695,
  .cx 1597 1696,
  .cx 1597 1697,
  .cx 1597 926,
  .cx 1597 927,
  .cx 1597 928,
  .cx 1597 929,
  .cx 1597 930,
  .cx 1597 931,
  .cx 1597 932,
  .cx 1597 933,
  .cx 1597 934]
private def block768 : List Gate := [
  .cx 1597 935,
  .cx 1597 936,
  .cx 1597 937,
  .cx 1597 938,
  .cx 1597 939,
  .cx 1597 940,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943]
private def block777 : List Gate := [
  .cx 1597 944,
  .cx 1597 945,
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1562 1613,
  .cx 1564 1613]
private def block864 : List Gate := [
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1028 1598,
  .ccx 1613 1598 1028,
  .cx 1028 1598]
private def block873 : List Gate := [
  .cx 1027 1028,
  .ccx 1613 1028 1027,
  .cx 1027 1028,
  .cx 1026 1027,
  .ccx 1613 1027 1026,
  .cx 1026 1027,
  .cx 1025 1026,
  .ccx 1613 1026 1025,
  .cx 1025 1026,
  .cx 1024 1025,
  .ccx 1613 1025 1024,
  .cx 1024 1025,
  .cx 1023 1024,
  .ccx 1613 1024 1023,
  .cx 1023 1024,
  .cx 1022 1023,
  .ccx 1613 1023 1022,
  .cx 1022 1023,
  .cx 1021 1022,
  .ccx 1613 1022 1021,
  .cx 1021 1022,
  .cx 1020 1021,
  .ccx 1613 1021 1020,
  .cx 1020 1021,
  .cx 1019 1020,
  .ccx 1613 1020 1019,
  .cx 1019 1020,
  .cx 1018 1019,
  .ccx 1613 1019 1018,
  .cx 1018 1019,
  .cx 1017 1018,
  .ccx 1613 1018 1017,
  .cx 1017 1018,
  .cx 1016 1017,
  .ccx 1613 1017 1016,
  .cx 1016 1017,
  .cx 1015 1016,
  .ccx 1613 1016 1015,
  .cx 1015 1016,
  .cx 1014 1015,
  .ccx 1613 1015 1014,
  .cx 1014 1015,
  .cx 1013 1014,
  .ccx 1613 1014 1013,
  .cx 1013 1014,
  .cx 1012 1013,
  .ccx 1613 1013 1012,
  .cx 1012 1013,
  .cx 1011 1012,
  .ccx 1613 1012 1011,
  .cx 1011 1012,
  .cx 1010 1011,
  .ccx 1613 1011 1010,
  .cx 1010 1011,
  .cx 1009 1010,
  .ccx 1613 1010 1009,
  .cx 1009 1010,
  .cx 1008 1009,
  .ccx 1613 1009 1008,
  .cx 1008 1009,
  .cx 1007 1008,
  .ccx 1613 1008 1007,
  .cx 1007 1008,
  .cx 1006 1007,
  .ccx 1613 1007 1006,
  .cx 1006 1007,
  .cx 1005 1006,
  .ccx 1613 1006 1005,
  .cx 1005 1006,
  .cx 1004 1005,
  .ccx 1613 1005 1004,
  .cx 1004 1005,
  .cx 1003 1004,
  .ccx 1613 1004 1003,
  .cx 1003 1004,
  .cx 1002 1003,
  .ccx 1613 1003 1002,
  .cx 1002 1003,
  .cx 1001 1002,
  .ccx 1613 1002 1001,
  .cx 1001 1002,
  .cx 1000 1001,
  .ccx 1613 1001 1000,
  .cx 1000 1001,
  .cx 999 1000,
  .ccx 1613 1000 999,
  .cx 999 1000]
private def block960 : List Gate := [
  .cx 998 999,
  .ccx 1613 999 998,
  .cx 998 999,
  .cx 997 998,
  .ccx 1613 998 997,
  .cx 997 998,
  .cx 996 997,
  .ccx 1613 997 996,
  .cx 996 997]
private def block969 : List Gate := [
  .cx 995 996,
  .ccx 1613 996 995,
  .cx 995 996,
  .cx 994 995,
  .ccx 1613 995 994,
  .cx 994 995,
  .cx 993 994,
  .ccx 1613 994 993,
  .cx 993 994,
  .cx 992 993,
  .ccx 1613 993 992,
  .cx 992 993,
  .cx 991 992,
  .ccx 1613 992 991,
  .cx 991 992,
  .cx 990 991,
  .ccx 1613 991 990,
  .cx 990 991,
  .cx 989 990,
  .ccx 1613 990 989,
  .cx 989 990,
  .cx 988 989,
  .ccx 1613 989 988,
  .cx 988 989,
  .cx 987 988,
  .ccx 1613 988 987,
  .cx 987 988,
  .cx 986 987,
  .ccx 1613 987 986,
  .cx 986 987,
  .cx 985 986,
  .ccx 1613 986 985,
  .cx 985 986,
  .cx 984 985,
  .ccx 1613 985 984,
  .cx 984 985,
  .cx 983 984,
  .ccx 1613 984 983,
  .cx 983 984,
  .cx 982 983,
  .ccx 1613 983 982,
  .cx 982 983,
  .cx 981 982,
  .ccx 1613 982 981,
  .cx 981 982,
  .cx 980 981,
  .ccx 1613 981 980,
  .cx 980 981,
  .cx 979 980,
  .ccx 1613 980 979,
  .cx 979 980,
  .cx 978 979,
  .ccx 1613 979 978,
  .cx 978 979,
  .cx 977 978,
  .ccx 1613 978 977,
  .cx 977 978,
  .cx 976 977,
  .ccx 1613 977 976,
  .cx 976 977,
  .cx 975 976,
  .ccx 1613 976 975,
  .cx 975 976,
  .cx 974 975,
  .ccx 1613 975 974,
  .cx 974 975,
  .cx 973 974,
  .ccx 1613 974 973,
  .cx 973 974,
  .cx 972 973,
  .ccx 1613 973 972,
  .cx 972 973,
  .cx 971 972,
  .ccx 1613 972 971,
  .cx 971 972,
  .cx 970 971,
  .ccx 1613 971 970,
  .cx 970 971,
  .cx 969 970,
  .ccx 1613 970 969,
  .cx 969 970,
  .cx 968 969,
  .ccx 1613 969 968,
  .cx 968 969,
  .cx 967 968,
  .ccx 1613 968 967,
  .cx 967 968]
private def block1056 : List Gate := [
  .cx 966 967,
  .ccx 1613 967 966,
  .cx 966 967,
  .cx 965 966,
  .ccx 1613 966 965,
  .cx 965 966,
  .cx 964 965,
  .ccx 1613 965 964,
  .cx 964 965]
private def block1065 : List Gate := [
  .cx 963 964,
  .ccx 1613 964 963,
  .cx 963 964,
  .cx 962 963,
  .ccx 1613 963 962,
  .cx 962 963,
  .cx 961 962,
  .ccx 1613 962 961,
  .cx 961 962,
  .cx 960 961,
  .ccx 1613 961 960,
  .cx 960 961,
  .cx 959 960,
  .ccx 1613 960 959,
  .cx 959 960,
  .cx 958 959,
  .ccx 1613 959 958,
  .cx 958 959,
  .cx 957 958,
  .ccx 1613 958 957,
  .cx 957 958,
  .cx 956 957,
  .ccx 1613 957 956,
  .cx 956 957,
  .cx 955 956,
  .ccx 1613 956 955,
  .cx 955 956,
  .cx 954 955,
  .ccx 1613 955 954,
  .cx 954 955,
  .cx 953 954,
  .ccx 1613 954 953,
  .cx 953 954,
  .cx 952 953,
  .ccx 1613 953 952,
  .cx 952 953,
  .cx 951 952,
  .ccx 1613 952 951,
  .cx 951 952,
  .cx 950 951,
  .ccx 1613 951 950,
  .cx 950 951,
  .cx 949 950,
  .ccx 1613 950 949,
  .cx 949 950,
  .cx 948 949,
  .ccx 1613 949 948,
  .cx 948 949,
  .cx 947 948,
  .ccx 1613 948 947,
  .cx 947 948,
  .cx 946 947,
  .ccx 1613 947 946,
  .cx 946 947,
  .cx 945 946,
  .ccx 1613 946 945,
  .cx 945 946,
  .cx 944 945,
  .ccx 1613 945 944,
  .cx 944 945,
  .cx 943 944,
  .ccx 1613 944 943,
  .cx 943 944,
  .cx 942 943,
  .ccx 1613 943 942,
  .cx 942 943,
  .cx 941 942,
  .ccx 1613 942 941,
  .cx 941 942,
  .cx 940 941,
  .ccx 1613 941 940,
  .cx 940 941,
  .cx 939 940,
  .ccx 1613 940 939,
  .cx 939 940,
  .cx 938 939,
  .ccx 1613 939 938,
  .cx 938 939,
  .cx 937 938,
  .ccx 1613 938 937,
  .cx 937 938,
  .cx 936 937,
  .ccx 1613 937 936,
  .cx 936 937,
  .cx 935 936,
  .ccx 1613 936 935,
  .cx 935 936]
private def block1152 : List Gate := [
  .cx 934 935,
  .ccx 1613 935 934,
  .cx 934 935,
  .cx 933 934,
  .ccx 1613 934 933,
  .cx 933 934,
  .cx 932 933,
  .ccx 1613 933 932,
  .cx 932 933]
private def block1161 : List Gate := [
  .cx 931 932,
  .ccx 1613 932 931,
  .cx 931 932,
  .cx 930 931,
  .ccx 1613 931 930,
  .cx 930 931,
  .cx 929 930,
  .ccx 1613 930 929,
  .cx 929 930,
  .cx 928 929,
  .ccx 1613 929 928,
  .cx 928 929,
  .cx 927 928,
  .ccx 1613 928 927,
  .cx 927 928,
  .cx 926 927,
  .ccx 1613 927 926,
  .cx 926 927,
  .cx 1697 926,
  .ccx 1613 926 1697,
  .cx 1697 926,
  .cx 1696 1697,
  .ccx 1613 1697 1696,
  .cx 1696 1697,
  .cx 1695 1696,
  .ccx 1613 1696 1695,
  .cx 1695 1696,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1598 1600,
  .ccx 1613 1600 1598,
  .cx 1598 1600,
  .cx 1028 1599,
  .ccx 1613 1599 1028,
  .cx 1028 1599,
  .cx 1027 1598,
  .ccx 1613 1598 1027,
  .cx 1027 1598,
  .cx 1026 1028,
  .ccx 1613 1028 1026,
  .cx 1026 1028,
  .cx 1025 1027,
  .ccx 1613 1027 1025,
  .cx 1025 1027,
  .cx 1024 1026,
  .ccx 1613 1026 1024,
  .cx 1024 1026,
  .cx 1023 1025,
  .ccx 1613 1025 1023,
  .cx 1023 1025,
  .cx 1022 1024,
  .ccx 1613 1024 1022,
  .cx 1022 1024,
  .cx 1021 1023,
  .ccx 1613 1023 1021,
  .cx 1021 1023,
  .cx 1020 1022,
  .ccx 1613 1022 1020,
  .cx 1020 1022,
  .cx 1019 1021,
  .ccx 1613 1021 1019,
  .cx 1019 1021,
  .cx 1018 1020,
  .ccx 1613 1020 1018,
  .cx 1018 1020,
  .cx 1017 1019,
  .ccx 1613 1019 1017,
  .cx 1017 1019,
  .cx 1016 1018,
  .ccx 1613 1018 1016,
  .cx 1016 1018,
  .cx 1015 1017,
  .ccx 1613 1017 1015]
private def block1248 : List Gate := [
  .cx 1015 1017,
  .cx 1014 1016,
  .ccx 1613 1016 1014,
  .cx 1014 1016,
  .cx 1013 1015,
  .ccx 1613 1015 1013,
  .cx 1013 1015,
  .cx 1012 1014,
  .ccx 1613 1014 1012]
private def block1257 : List Gate := [
  .cx 1012 1014,
  .cx 1011 1013,
  .ccx 1613 1013 1011,
  .cx 1011 1013,
  .cx 1010 1012,
  .ccx 1613 1012 1010,
  .cx 1010 1012,
  .cx 1009 1011,
  .ccx 1613 1011 1009,
  .cx 1009 1011,
  .cx 1008 1010,
  .ccx 1613 1010 1008,
  .cx 1008 1010,
  .cx 1007 1009,
  .ccx 1613 1009 1007,
  .cx 1007 1009,
  .cx 1006 1008,
  .ccx 1613 1008 1006,
  .cx 1006 1008,
  .cx 1005 1007,
  .ccx 1613 1007 1005,
  .cx 1005 1007,
  .cx 1004 1006,
  .ccx 1613 1006 1004,
  .cx 1004 1006,
  .cx 1003 1005,
  .ccx 1613 1005 1003,
  .cx 1003 1005,
  .cx 1002 1004,
  .ccx 1613 1004 1002,
  .cx 1002 1004,
  .cx 1001 1003,
  .ccx 1613 1003 1001,
  .cx 1001 1003,
  .cx 1000 1002,
  .ccx 1613 1002 1000,
  .cx 1000 1002,
  .cx 999 1001,
  .ccx 1613 1001 999,
  .cx 999 1001,
  .cx 998 1000,
  .ccx 1613 1000 998,
  .cx 998 1000,
  .cx 997 999,
  .ccx 1613 999 997,
  .cx 997 999,
  .cx 996 998,
  .ccx 1613 998 996,
  .cx 996 998,
  .cx 995 997,
  .ccx 1613 997 995,
  .cx 995 997,
  .cx 994 996,
  .ccx 1613 996 994,
  .cx 994 996,
  .cx 993 995,
  .ccx 1613 995 993,
  .cx 993 995,
  .cx 992 994,
  .ccx 1613 994 992,
  .cx 992 994,
  .cx 991 993,
  .ccx 1613 993 991,
  .cx 991 993,
  .cx 990 992,
  .ccx 1613 992 990,
  .cx 990 992,
  .cx 989 991,
  .ccx 1613 991 989,
  .cx 989 991,
  .cx 988 990,
  .ccx 1613 990 988,
  .cx 988 990,
  .cx 987 989,
  .ccx 1613 989 987,
  .cx 987 989,
  .cx 986 988,
  .ccx 1613 988 986,
  .cx 986 988,
  .cx 985 987,
  .ccx 1613 987 985,
  .cx 985 987,
  .cx 984 986,
  .ccx 1613 986 984,
  .cx 984 986,
  .cx 983 985,
  .ccx 1613 985 983]
private def block1344 : List Gate := [
  .cx 983 985,
  .cx 982 984,
  .ccx 1613 984 982,
  .cx 982 984,
  .cx 981 983,
  .ccx 1613 983 981,
  .cx 981 983,
  .cx 980 982,
  .ccx 1613 982 980]
private def block1353 : List Gate := [
  .cx 980 982,
  .cx 979 981,
  .ccx 1613 981 979,
  .cx 979 981,
  .cx 978 980,
  .ccx 1613 980 978,
  .cx 978 980,
  .cx 977 979,
  .ccx 1613 979 977,
  .cx 977 979,
  .cx 976 978,
  .ccx 1613 978 976,
  .cx 976 978,
  .cx 975 977,
  .ccx 1613 977 975,
  .cx 975 977,
  .cx 974 976,
  .ccx 1613 976 974,
  .cx 974 976,
  .cx 973 975,
  .ccx 1613 975 973,
  .cx 973 975,
  .cx 972 974,
  .ccx 1613 974 972,
  .cx 972 974,
  .cx 971 973,
  .ccx 1613 973 971,
  .cx 971 973,
  .cx 970 972,
  .ccx 1613 972 970,
  .cx 970 972,
  .cx 969 971,
  .ccx 1613 971 969,
  .cx 969 971,
  .cx 968 970,
  .ccx 1613 970 968,
  .cx 968 970,
  .cx 967 969,
  .ccx 1613 969 967,
  .cx 967 969,
  .cx 966 968,
  .ccx 1613 968 966,
  .cx 966 968,
  .cx 965 967,
  .ccx 1613 967 965,
  .cx 965 967,
  .cx 964 966,
  .ccx 1613 966 964,
  .cx 964 966,
  .cx 963 965,
  .ccx 1613 965 963,
  .cx 963 965,
  .cx 962 964,
  .ccx 1613 964 962,
  .cx 962 964,
  .cx 961 963,
  .ccx 1613 963 961,
  .cx 961 963,
  .cx 960 962,
  .ccx 1613 962 960,
  .cx 960 962,
  .cx 959 961,
  .ccx 1613 961 959,
  .cx 959 961,
  .cx 958 960,
  .ccx 1613 960 958,
  .cx 958 960,
  .cx 957 959,
  .ccx 1613 959 957,
  .cx 957 959,
  .cx 956 958,
  .ccx 1613 958 956,
  .cx 956 958,
  .cx 955 957,
  .ccx 1613 957 955,
  .cx 955 957,
  .cx 954 956,
  .ccx 1613 956 954,
  .cx 954 956,
  .cx 953 955,
  .ccx 1613 955 953,
  .cx 953 955,
  .cx 952 954,
  .ccx 1613 954 952,
  .cx 952 954,
  .cx 951 953,
  .ccx 1613 953 951]
private def block1440 : List Gate := [
  .cx 951 953,
  .cx 950 952,
  .ccx 1613 952 950,
  .cx 950 952,
  .cx 949 951,
  .ccx 1613 951 949,
  .cx 949 951,
  .cx 948 950,
  .ccx 1613 950 948]
private def block1449 : List Gate := [
  .cx 948 950,
  .cx 947 949,
  .ccx 1613 949 947,
  .cx 947 949,
  .cx 946 948,
  .ccx 1613 948 946,
  .cx 946 948,
  .cx 945 947,
  .ccx 1613 947 945,
  .cx 945 947,
  .cx 944 946,
  .ccx 1613 946 944,
  .cx 944 946,
  .cx 943 945,
  .ccx 1613 945 943,
  .cx 943 945,
  .cx 942 944,
  .ccx 1613 944 942,
  .cx 942 944,
  .cx 941 943,
  .ccx 1613 943 941,
  .cx 941 943,
  .cx 940 942,
  .ccx 1613 942 940,
  .cx 940 942,
  .cx 939 941,
  .ccx 1613 941 939,
  .cx 939 941,
  .cx 938 940,
  .ccx 1613 940 938,
  .cx 938 940,
  .cx 937 939,
  .ccx 1613 939 937,
  .cx 937 939,
  .cx 936 938,
  .ccx 1613 938 936,
  .cx 936 938,
  .cx 935 937,
  .ccx 1613 937 935,
  .cx 935 937,
  .cx 934 936,
  .ccx 1613 936 934,
  .cx 934 936,
  .cx 933 935,
  .ccx 1613 935 933,
  .cx 933 935,
  .cx 932 934,
  .ccx 1613 934 932,
  .cx 932 934,
  .cx 931 933,
  .ccx 1613 933 931,
  .cx 931 933,
  .cx 930 932,
  .ccx 1613 932 930,
  .cx 930 932,
  .cx 929 931,
  .ccx 1613 931 929,
  .cx 929 931,
  .cx 928 930,
  .ccx 1613 930 928,
  .cx 928 930,
  .cx 927 929,
  .ccx 1613 929 927,
  .cx 927 929,
  .cx 926 928,
  .ccx 1613 928 926,
  .cx 926 928,
  .cx 1697 927,
  .ccx 1613 927 1697,
  .cx 1697 927,
  .cx 1696 926,
  .ccx 1613 926 1696,
  .cx 1696 926,
  .cx 1695 1697,
  .ccx 1613 1697 1695,
  .cx 1695 1697,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613]
private def block1536 : List Gate := [
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1600 1604,
  .ccx 1613 1604 1600,
  .cx 1600 1604,
  .cx 1599 1603]
private def block1545 : List Gate := [
  .ccx 1613 1603 1599,
  .cx 1599 1603,
  .cx 1598 1602,
  .ccx 1613 1602 1598,
  .cx 1598 1602,
  .cx 1028 1601,
  .ccx 1613 1601 1028,
  .cx 1028 1601,
  .cx 1027 1600,
  .ccx 1613 1600 1027,
  .cx 1027 1600,
  .cx 1026 1599,
  .ccx 1613 1599 1026,
  .cx 1026 1599,
  .cx 1025 1598,
  .ccx 1613 1598 1025,
  .cx 1025 1598,
  .cx 1024 1028,
  .ccx 1613 1028 1024,
  .cx 1024 1028,
  .cx 1023 1027,
  .ccx 1613 1027 1023,
  .cx 1023 1027,
  .cx 1022 1026,
  .ccx 1613 1026 1022,
  .cx 1022 1026,
  .cx 1021 1025,
  .ccx 1613 1025 1021,
  .cx 1021 1025,
  .cx 1020 1024,
  .ccx 1613 1024 1020,
  .cx 1020 1024,
  .cx 1019 1023,
  .ccx 1613 1023 1019,
  .cx 1019 1023,
  .cx 1018 1022,
  .ccx 1613 1022 1018,
  .cx 1018 1022,
  .cx 1017 1021,
  .ccx 1613 1021 1017,
  .cx 1017 1021,
  .cx 1016 1020,
  .ccx 1613 1020 1016,
  .cx 1016 1020,
  .cx 1015 1019,
  .ccx 1613 1019 1015,
  .cx 1015 1019,
  .cx 1014 1018,
  .ccx 1613 1018 1014,
  .cx 1014 1018,
  .cx 1013 1017,
  .ccx 1613 1017 1013,
  .cx 1013 1017,
  .cx 1012 1016,
  .ccx 1613 1016 1012,
  .cx 1012 1016,
  .cx 1011 1015,
  .ccx 1613 1015 1011,
  .cx 1011 1015,
  .cx 1010 1014,
  .ccx 1613 1014 1010,
  .cx 1010 1014,
  .cx 1009 1013,
  .ccx 1613 1013 1009,
  .cx 1009 1013,
  .cx 1008 1012,
  .ccx 1613 1012 1008,
  .cx 1008 1012,
  .cx 1007 1011,
  .ccx 1613 1011 1007,
  .cx 1007 1011,
  .cx 1006 1010,
  .ccx 1613 1010 1006,
  .cx 1006 1010,
  .cx 1005 1009,
  .ccx 1613 1009 1005,
  .cx 1005 1009,
  .cx 1004 1008,
  .ccx 1613 1008 1004,
  .cx 1004 1008,
  .cx 1003 1007,
  .ccx 1613 1007 1003,
  .cx 1003 1007,
  .cx 1002 1006,
  .ccx 1613 1006 1002,
  .cx 1002 1006,
  .cx 1001 1005]
private def block1632 : List Gate := [
  .ccx 1613 1005 1001,
  .cx 1001 1005,
  .cx 1000 1004,
  .ccx 1613 1004 1000,
  .cx 1000 1004,
  .cx 999 1003,
  .ccx 1613 1003 999,
  .cx 999 1003,
  .cx 998 1002]
private def block1641 : List Gate := [
  .ccx 1613 1002 998,
  .cx 998 1002,
  .cx 997 1001,
  .ccx 1613 1001 997,
  .cx 997 1001,
  .cx 996 1000,
  .ccx 1613 1000 996,
  .cx 996 1000,
  .cx 995 999,
  .ccx 1613 999 995,
  .cx 995 999,
  .cx 994 998,
  .ccx 1613 998 994,
  .cx 994 998,
  .cx 993 997,
  .ccx 1613 997 993,
  .cx 993 997,
  .cx 992 996,
  .ccx 1613 996 992,
  .cx 992 996,
  .cx 991 995,
  .ccx 1613 995 991,
  .cx 991 995,
  .cx 990 994,
  .ccx 1613 994 990,
  .cx 990 994,
  .cx 989 993,
  .ccx 1613 993 989,
  .cx 989 993,
  .cx 988 992,
  .ccx 1613 992 988,
  .cx 988 992,
  .cx 987 991,
  .ccx 1613 991 987,
  .cx 987 991,
  .cx 986 990,
  .ccx 1613 990 986,
  .cx 986 990,
  .cx 985 989,
  .ccx 1613 989 985,
  .cx 985 989,
  .cx 984 988,
  .ccx 1613 988 984,
  .cx 984 988,
  .cx 983 987,
  .ccx 1613 987 983,
  .cx 983 987,
  .cx 982 986,
  .ccx 1613 986 982,
  .cx 982 986,
  .cx 981 985,
  .ccx 1613 985 981,
  .cx 981 985,
  .cx 980 984,
  .ccx 1613 984 980,
  .cx 980 984,
  .cx 979 983,
  .ccx 1613 983 979,
  .cx 979 983,
  .cx 978 982,
  .ccx 1613 982 978,
  .cx 978 982,
  .cx 977 981,
  .ccx 1613 981 977,
  .cx 977 981,
  .cx 976 980,
  .ccx 1613 980 976,
  .cx 976 980,
  .cx 975 979,
  .ccx 1613 979 975,
  .cx 975 979,
  .cx 974 978,
  .ccx 1613 978 974,
  .cx 974 978,
  .cx 973 977,
  .ccx 1613 977 973,
  .cx 973 977,
  .cx 972 976,
  .ccx 1613 976 972,
  .cx 972 976,
  .cx 971 975,
  .ccx 1613 975 971,
  .cx 971 975,
  .cx 970 974,
  .ccx 1613 974 970,
  .cx 970 974,
  .cx 969 973]
private def block1728 : List Gate := [
  .ccx 1613 973 969,
  .cx 969 973,
  .cx 968 972,
  .ccx 1613 972 968,
  .cx 968 972,
  .cx 967 971,
  .ccx 1613 971 967,
  .cx 967 971,
  .cx 966 970]
private def block1737 : List Gate := [
  .ccx 1613 970 966,
  .cx 966 970,
  .cx 965 969,
  .ccx 1613 969 965,
  .cx 965 969,
  .cx 964 968,
  .ccx 1613 968 964,
  .cx 964 968,
  .cx 963 967,
  .ccx 1613 967 963,
  .cx 963 967,
  .cx 962 966,
  .ccx 1613 966 962,
  .cx 962 966,
  .cx 961 965,
  .ccx 1613 965 961,
  .cx 961 965,
  .cx 960 964,
  .ccx 1613 964 960,
  .cx 960 964,
  .cx 959 963,
  .ccx 1613 963 959,
  .cx 959 963,
  .cx 958 962,
  .ccx 1613 962 958,
  .cx 958 962,
  .cx 957 961,
  .ccx 1613 961 957,
  .cx 957 961,
  .cx 956 960,
  .ccx 1613 960 956,
  .cx 956 960,
  .cx 955 959,
  .ccx 1613 959 955,
  .cx 955 959,
  .cx 954 958,
  .ccx 1613 958 954,
  .cx 954 958,
  .cx 953 957,
  .ccx 1613 957 953,
  .cx 953 957,
  .cx 952 956,
  .ccx 1613 956 952,
  .cx 952 956,
  .cx 951 955,
  .ccx 1613 955 951,
  .cx 951 955,
  .cx 950 954,
  .ccx 1613 954 950,
  .cx 950 954,
  .cx 949 953,
  .ccx 1613 953 949,
  .cx 949 953,
  .cx 948 952,
  .ccx 1613 952 948,
  .cx 948 952,
  .cx 947 951,
  .ccx 1613 951 947,
  .cx 947 951,
  .cx 946 950,
  .ccx 1613 950 946,
  .cx 946 950,
  .cx 945 949,
  .ccx 1613 949 945,
  .cx 945 949,
  .cx 944 948,
  .ccx 1613 948 944,
  .cx 944 948,
  .cx 943 947,
  .ccx 1613 947 943,
  .cx 943 947,
  .cx 942 946,
  .ccx 1613 946 942,
  .cx 942 946,
  .cx 941 945,
  .ccx 1613 945 941,
  .cx 941 945,
  .cx 940 944,
  .ccx 1613 944 940,
  .cx 940 944,
  .cx 939 943,
  .ccx 1613 943 939,
  .cx 939 943,
  .cx 938 942,
  .ccx 1613 942 938,
  .cx 938 942,
  .cx 937 941]
private def block1824 : List Gate := [
  .ccx 1613 941 937,
  .cx 937 941,
  .cx 936 940,
  .ccx 1613 940 936,
  .cx 936 940,
  .cx 935 939,
  .ccx 1613 939 935,
  .cx 935 939,
  .cx 934 938]
private def block1833 : List Gate := [
  .ccx 1613 938 934,
  .cx 934 938,
  .cx 933 937,
  .ccx 1613 937 933,
  .cx 933 937,
  .cx 932 936,
  .ccx 1613 936 932,
  .cx 932 936,
  .cx 931 935,
  .ccx 1613 935 931,
  .cx 931 935,
  .cx 930 934,
  .ccx 1613 934 930,
  .cx 930 934,
  .cx 929 933,
  .ccx 1613 933 929,
  .cx 929 933,
  .cx 928 932,
  .ccx 1613 932 928,
  .cx 928 932,
  .cx 927 931,
  .ccx 1613 931 927,
  .cx 927 931,
  .cx 926 930,
  .ccx 1613 930 926,
  .cx 926 930,
  .cx 1697 929,
  .ccx 1613 929 1697,
  .cx 1697 929,
  .cx 1696 928,
  .ccx 1613 928 1696,
  .cx 1696 928,
  .cx 1695 927,
  .ccx 1613 927 1695,
  .cx 1695 927,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1604 1612,
  .ccx 1613 1612 1604,
  .cx 1604 1612,
  .cx 1603 1611,
  .ccx 1613 1611 1603,
  .cx 1603 1611,
  .cx 1602 1610,
  .ccx 1613 1610 1602,
  .cx 1602 1610,
  .cx 1601 1609,
  .ccx 1613 1609 1601,
  .cx 1601 1609,
  .cx 1600 1608,
  .ccx 1613 1608 1600,
  .cx 1600 1608,
  .cx 1599 1607,
  .ccx 1613 1607 1599,
  .cx 1599 1607,
  .cx 1598 1606,
  .ccx 1613 1606 1598,
  .cx 1598 1606,
  .cx 1028 1605,
  .ccx 1613 1605 1028,
  .cx 1028 1605,
  .cx 1027 1604,
  .ccx 1613 1604 1027,
  .cx 1027 1604,
  .cx 1026 1603,
  .ccx 1613 1603 1026,
  .cx 1026 1603,
  .cx 1025 1602,
  .ccx 1613 1602 1025,
  .cx 1025 1602,
  .cx 1024 1601,
  .ccx 1613 1601 1024,
  .cx 1024 1601]
private def block1920 : List Gate := [
  .cx 1023 1600,
  .ccx 1613 1600 1023,
  .cx 1023 1600,
  .cx 1022 1599,
  .ccx 1613 1599 1022,
  .cx 1022 1599,
  .cx 1021 1598,
  .ccx 1613 1598 1021,
  .cx 1021 1598]
private def block1929 : List Gate := [
  .cx 1020 1028,
  .ccx 1613 1028 1020,
  .cx 1020 1028,
  .cx 1019 1027,
  .ccx 1613 1027 1019,
  .cx 1019 1027,
  .cx 1018 1026,
  .ccx 1613 1026 1018,
  .cx 1018 1026,
  .cx 1017 1025,
  .ccx 1613 1025 1017,
  .cx 1017 1025,
  .cx 1016 1024,
  .ccx 1613 1024 1016,
  .cx 1016 1024,
  .cx 1015 1023,
  .ccx 1613 1023 1015,
  .cx 1015 1023,
  .cx 1014 1022,
  .ccx 1613 1022 1014,
  .cx 1014 1022,
  .cx 1013 1021,
  .ccx 1613 1021 1013,
  .cx 1013 1021,
  .cx 1012 1020,
  .ccx 1613 1020 1012,
  .cx 1012 1020,
  .cx 1011 1019,
  .ccx 1613 1019 1011,
  .cx 1011 1019,
  .cx 1010 1018,
  .ccx 1613 1018 1010,
  .cx 1010 1018,
  .cx 1009 1017,
  .ccx 1613 1017 1009,
  .cx 1009 1017,
  .cx 1008 1016,
  .ccx 1613 1016 1008,
  .cx 1008 1016,
  .cx 1007 1015,
  .ccx 1613 1015 1007,
  .cx 1007 1015,
  .cx 1006 1014,
  .ccx 1613 1014 1006,
  .cx 1006 1014,
  .cx 1005 1013,
  .ccx 1613 1013 1005,
  .cx 1005 1013,
  .cx 1004 1012,
  .ccx 1613 1012 1004,
  .cx 1004 1012,
  .cx 1003 1011,
  .ccx 1613 1011 1003,
  .cx 1003 1011,
  .cx 1002 1010,
  .ccx 1613 1010 1002,
  .cx 1002 1010,
  .cx 1001 1009,
  .ccx 1613 1009 1001,
  .cx 1001 1009,
  .cx 1000 1008,
  .ccx 1613 1008 1000,
  .cx 1000 1008,
  .cx 999 1007,
  .ccx 1613 1007 999,
  .cx 999 1007,
  .cx 998 1006,
  .ccx 1613 1006 998,
  .cx 998 1006,
  .cx 997 1005,
  .ccx 1613 1005 997,
  .cx 997 1005,
  .cx 996 1004,
  .ccx 1613 1004 996,
  .cx 996 1004,
  .cx 995 1003,
  .ccx 1613 1003 995,
  .cx 995 1003,
  .cx 994 1002,
  .ccx 1613 1002 994,
  .cx 994 1002,
  .cx 993 1001,
  .ccx 1613 1001 993,
  .cx 993 1001,
  .cx 992 1000,
  .ccx 1613 1000 992,
  .cx 992 1000]
private def block2016 : List Gate := [
  .cx 991 999,
  .ccx 1613 999 991,
  .cx 991 999,
  .cx 990 998,
  .ccx 1613 998 990,
  .cx 990 998,
  .cx 989 997,
  .ccx 1613 997 989,
  .cx 989 997]
private def block2025 : List Gate := [
  .cx 988 996,
  .ccx 1613 996 988,
  .cx 988 996,
  .cx 987 995,
  .ccx 1613 995 987,
  .cx 987 995,
  .cx 986 994,
  .ccx 1613 994 986,
  .cx 986 994,
  .cx 985 993,
  .ccx 1613 993 985,
  .cx 985 993,
  .cx 984 992,
  .ccx 1613 992 984,
  .cx 984 992,
  .cx 983 991,
  .ccx 1613 991 983,
  .cx 983 991,
  .cx 982 990,
  .ccx 1613 990 982,
  .cx 982 990,
  .cx 981 989,
  .ccx 1613 989 981,
  .cx 981 989,
  .cx 980 988,
  .ccx 1613 988 980,
  .cx 980 988,
  .cx 979 987,
  .ccx 1613 987 979,
  .cx 979 987,
  .cx 978 986,
  .ccx 1613 986 978,
  .cx 978 986,
  .cx 977 985,
  .ccx 1613 985 977,
  .cx 977 985,
  .cx 976 984,
  .ccx 1613 984 976,
  .cx 976 984,
  .cx 975 983,
  .ccx 1613 983 975,
  .cx 975 983,
  .cx 974 982,
  .ccx 1613 982 974,
  .cx 974 982,
  .cx 973 981,
  .ccx 1613 981 973,
  .cx 973 981,
  .cx 972 980,
  .ccx 1613 980 972,
  .cx 972 980,
  .cx 971 979,
  .ccx 1613 979 971,
  .cx 971 979,
  .cx 970 978,
  .ccx 1613 978 970,
  .cx 970 978,
  .cx 969 977,
  .ccx 1613 977 969,
  .cx 969 977,
  .cx 968 976,
  .ccx 1613 976 968,
  .cx 968 976,
  .cx 967 975,
  .ccx 1613 975 967,
  .cx 967 975,
  .cx 966 974,
  .ccx 1613 974 966,
  .cx 966 974,
  .cx 965 973,
  .ccx 1613 973 965,
  .cx 965 973,
  .cx 964 972,
  .ccx 1613 972 964,
  .cx 964 972,
  .cx 963 971,
  .ccx 1613 971 963,
  .cx 963 971,
  .cx 962 970,
  .ccx 1613 970 962,
  .cx 962 970,
  .cx 961 969,
  .ccx 1613 969 961,
  .cx 961 969,
  .cx 960 968,
  .ccx 1613 968 960,
  .cx 960 968]
private def block2112 : List Gate := [
  .cx 959 967,
  .ccx 1613 967 959,
  .cx 959 967,
  .cx 958 966,
  .ccx 1613 966 958,
  .cx 958 966,
  .cx 957 965,
  .ccx 1613 965 957,
  .cx 957 965]
private def block2121 : List Gate := [
  .cx 956 964,
  .ccx 1613 964 956,
  .cx 956 964,
  .cx 955 963,
  .ccx 1613 963 955,
  .cx 955 963,
  .cx 954 962,
  .ccx 1613 962 954,
  .cx 954 962,
  .cx 953 961,
  .ccx 1613 961 953,
  .cx 953 961,
  .cx 952 960,
  .ccx 1613 960 952,
  .cx 952 960,
  .cx 951 959,
  .ccx 1613 959 951,
  .cx 951 959,
  .cx 950 958,
  .ccx 1613 958 950,
  .cx 950 958,
  .cx 949 957,
  .ccx 1613 957 949,
  .cx 949 957,
  .cx 948 956,
  .ccx 1613 956 948,
  .cx 948 956,
  .cx 947 955,
  .ccx 1613 955 947,
  .cx 947 955,
  .cx 946 954,
  .ccx 1613 954 946,
  .cx 946 954,
  .cx 945 953,
  .ccx 1613 953 945,
  .cx 945 953,
  .cx 944 952,
  .ccx 1613 952 944,
  .cx 944 952,
  .cx 943 951,
  .ccx 1613 951 943,
  .cx 943 951,
  .cx 942 950,
  .ccx 1613 950 942,
  .cx 942 950,
  .cx 941 949,
  .ccx 1613 949 941,
  .cx 941 949,
  .cx 940 948,
  .ccx 1613 948 940,
  .cx 940 948,
  .cx 939 947,
  .ccx 1613 947 939,
  .cx 939 947,
  .cx 938 946,
  .ccx 1613 946 938,
  .cx 938 946,
  .cx 937 945,
  .ccx 1613 945 937,
  .cx 937 945,
  .cx 936 944,
  .ccx 1613 944 936,
  .cx 936 944,
  .cx 935 943,
  .ccx 1613 943 935,
  .cx 935 943,
  .cx 934 942,
  .ccx 1613 942 934,
  .cx 934 942,
  .cx 933 941,
  .ccx 1613 941 933,
  .cx 933 941,
  .cx 932 940,
  .ccx 1613 940 932,
  .cx 932 940,
  .cx 931 939,
  .ccx 1613 939 931,
  .cx 931 939,
  .cx 930 938,
  .ccx 1613 938 930,
  .cx 930 938,
  .cx 929 937,
  .ccx 1613 937 929,
  .cx 929 937,
  .cx 928 936,
  .ccx 1613 936 928,
  .cx 928 936]
private def block2208 : List Gate := [
  .cx 927 935,
  .ccx 1613 935 927,
  .cx 927 935,
  .cx 926 934,
  .ccx 1613 934 926,
  .cx 926 934,
  .cx 1697 933,
  .ccx 1613 933 1697,
  .cx 1697 933]
private def block2217 : List Gate := [
  .cx 1696 932,
  .ccx 1613 932 1696,
  .cx 1696 932,
  .cx 1695 931,
  .ccx 1613 931 1695,
  .cx 1695 931,
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .x 1613,
  .cx 1597 1613,
  .ccx 1576 1701 423,
  .ccx 1576 1613 424,
  .ccx 1562 1701 424,
  .ccx 1562 1613 425,
  .ccx 1563 1701 425,
  .ccx 1563 1613 426,
  .ccx 1564 1701 426,
  .ccx 1564 1613 427,
  .ccx 1565 1701 427,
  .ccx 1565 1613 428,
  .ccx 1566 1701 428,
  .ccx 1566 1613 429,
  .ccx 1567 1701 429,
  .ccx 1567 1613 430,
  .ccx 1568 1701 430,
  .ccx 1568 1613 431,
  .ccx 1569 1701 431,
  .ccx 1569 1613 432,
  .ccx 1570 1701 432,
  .ccx 1570 1613 433,
  .ccx 1571 1701 433,
  .ccx 1571 1613 434,
  .ccx 1572 1701 434,
  .ccx 1572 1613 435,
  .ccx 1573 1701 435,
  .ccx 1573 1613 436,
  .ccx 1574 1701 436,
  .ccx 1574 1613 437,
  .ccx 1575 1701 437,
  .ccx 1575 1613 438,
  .ccx 1560 1701 438,
  .ccx 1560 1613 439,
  .cx 1576 1614,
  .cx 1695 423,
  .ccx 1614 423 1695,
  .cx 1562 1614,
  .cx 1696 424,
  .ccx 1614 424 1696,
  .cx 1563 1614,
  .cx 1697 425,
  .ccx 1614 425 1697,
  .cx 1564 1614,
  .cx 926 426,
  .ccx 1614 426 926,
  .cx 1565 1614,
  .cx 927 427,
  .ccx 1614 427 927,
  .cx 1566 1614,
  .cx 928 428,
  .ccx 1614 428 928,
  .cx 1567 1614,
  .cx 929 429,
  .ccx 1614 429 929,
  .cx 1568 1614,
  .cx 930 430,
  .ccx 1614 430 930,
  .cx 1569 1614,
  .cx 931 431,
  .ccx 1614 431 931,
  .cx 1570 1614,
  .cx 932 432,
  .ccx 1614 432 932,
  .cx 1571 1614,
  .cx 933 433,
  .ccx 1614 433 933,
  .cx 1572 1614,
  .cx 434 934,
  .cx 934 434,
  .ccx 1614 934 434,
  .cx 1573 1614,
  .cx 435 935]
private def block2304 : List Gate := [
  .cx 935 435,
  .ccx 1614 935 435,
  .cx 1574 1614,
  .cx 436 936,
  .cx 936 436,
  .ccx 1614 936 436,
  .cx 1575 1614,
  .cx 437 937,
  .cx 937 437]
private def block2313 : List Gate := [
  .ccx 1614 937 437,
  .cx 1560 1614,
  .cx 438 938,
  .cx 938 438,
  .ccx 1614 938 438,
  .cx 439 939,
  .cx 939 439,
  .ccx 1614 939 439,
  .cx 440 940,
  .cx 940 440,
  .ccx 1614 940 440,
  .cx 1560 1614,
  .cx 1575 1614,
  .cx 1574 1614,
  .cx 1573 1614,
  .cx 1572 1614,
  .cx 1571 1614,
  .cx 1570 1614,
  .cx 1569 1614,
  .cx 1568 1614,
  .cx 1567 1614,
  .cx 1566 1614,
  .cx 1565 1614,
  .cx 1564 1614,
  .cx 1563 1614,
  .cx 1562 1614,
  .cx 1576 1614,
  .cx 1597 1613,
  .x 1613,
  .pop 1701 1596 1597,
  .cx 1589 1596,
  .cx 1590 1596,
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .pop 1568 300 1595,
  .pop 1567 1578 1594,
  .pop 1566 1580 1593,
  .pop 1565 1582 1592,
  .pop 1564 1584 1591,
  .pop 1563 1586 1590,
  .pop 1562 1588 1589,
  .pop 288 1587 1588,
  .pop 289 1586 1587,
  .pop 290 1585 1586,
  .pop 291 1584 1585,
  .pop 292 1583 1584,
  .pop 293 1582 1583,
  .pop 294 1581 1582,
  .pop 295 1580 1581,
  .pop 296 1579 1580,
  .pop 297 1578 1579,
  .pop 298 1577 1578,
  .pop 299 300 1577,
  .cx 1559 1576,
  .cx 1561 1576,
  .cx 1575 1560,
  .pop 1560 1785 1575,
  .cx 1574 1560,
  .pop 1560 1786 1574,
  .cx 1573 1560,
  .pop 1560 1787 1573,
  .cx 1572 1560,
  .pop 1560 1788 1572,
  .cx 1571 1560,
  .pop 1560 1789 1571,
  .cx 1570 1560,
  .pop 1560 1790 1570,
  .cx 1569 1560,
  .pop 1560 1791 1569,
  .cx 1568 1560,
  .pop 1560 1792 1568,
  .cx 1567 1560,
  .pop 1560 1793 1567,
  .cx 1566 1560,
  .pop 1560 1794 1566,
  .cx 1565 1560]
private def block2400 : List Gate := [
  .pop 1560 1795 1565,
  .cx 1564 1560,
  .pop 1560 1796 1564,
  .cx 1563 1560,
  .pop 1560 1797 1563,
  .cx 1562 1560,
  .pop 1560 1798 1562,
  .cx 1561 1560,
  .pop 1560 1799 1561]
private def block2409 : List Gate := [
  .cx 1698 1560,
  .cx 1559 1560,
  .pop 1698 1699 1559]
private def block2412 : List Gate := [
  .ccx 1556 423 908,
  .ccx 1556 424 909,
  .ccx 1556 425 910,
  .ccx 1556 426 911,
  .ccx 1556 427 912,
  .ccx 1556 428 913,
  .ccx 1556 429 914,
  .ccx 1556 430 915,
  .ccx 1556 431 916,
  .ccx 1556 432 917,
  .ccx 1556 433 918,
  .x 908,
  .x 909,
  .x 910,
  .x 911,
  .x 912,
  .x 913,
  .x 914,
  .x 915,
  .x 916,
  .x 917,
  .x 918,
  .make 908 1558 1559,
  .make 909 1559 1560,
  .make 910 1560 1561,
  .make 911 1561 1562,
  .make 912 1562 1563,
  .make 913 1563 1564,
  .make 914 1564 1565,
  .make 915 1565 1566,
  .make 916 1566 1567,
  .make 917 1567 1568,
  .cx 1568 918,
  .pop 917 1567 1568,
  .cx 1567 917,
  .pop 916 1566 1567,
  .cx 1566 916,
  .pop 915 1565 1566,
  .cx 1565 915,
  .pop 914 1564 1565,
  .cx 1564 914,
  .pop 913 1563 1564,
  .cx 1563 913,
  .pop 912 1562 1563,
  .cx 1562 912,
  .pop 911 1561 1562,
  .cx 1561 911,
  .pop 910 1560 1561,
  .cx 1560 910,
  .pop 909 1559 1560,
  .cx 1559 909,
  .pop 908 1558 1559,
  .cx 1558 908,
  .x 908,
  .x 909,
  .x 910,
  .x 911,
  .x 912,
  .x 913,
  .x 914,
  .x 915,
  .x 916,
  .x 917,
  .x 918,
  .pop 907 1557 1558,
  .cx 422 1557,
  .x 1557,
  .make 431 432 1558,
  .x 1558,
  .x 433,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .x 941,
  .x 942,
  .x 943,
  .x 944,
  .x 945,
  .x 946,
  .x 947]
private def block2496 : List Gate := [
  .x 948,
  .x 949,
  .x 950,
  .x 951,
  .x 952,
  .x 953,
  .x 954,
  .x 955,
  .x 956]
private def block2505 : List Gate := [
  .x 957,
  .x 958,
  .x 959,
  .x 960,
  .x 961,
  .x 962,
  .x 963,
  .x 964,
  .x 965,
  .x 966,
  .x 967,
  .x 968,
  .x 969,
  .x 970,
  .x 971,
  .x 972,
  .x 973,
  .x 974,
  .x 975,
  .x 976,
  .x 977,
  .x 978,
  .x 979,
  .x 980,
  .x 981,
  .x 982,
  .x 983,
  .x 984,
  .x 985,
  .x 986,
  .x 987,
  .x 988,
  .x 989,
  .x 990,
  .x 991,
  .x 992,
  .x 993,
  .x 994,
  .x 995,
  .x 996,
  .x 997,
  .x 998,
  .x 999,
  .x 1000,
  .x 1001,
  .x 1002,
  .x 1003,
  .x 1004,
  .x 1005,
  .x 1006,
  .x 1007,
  .x 1008,
  .x 1009,
  .x 1010,
  .x 1011,
  .x 1012,
  .x 1013,
  .x 1014,
  .x 1015,
  .x 1016,
  .x 1017,
  .x 1018,
  .x 1019,
  .x 1020,
  .x 1021,
  .x 1022,
  .x 1023,
  .x 1024,
  .x 1025,
  .x 1026,
  .x 1027,
  .x 1028,
  .x 1598,
  .x 1599,
  .x 1600,
  .x 1601,
  .x 1602,
  .x 1603,
  .x 1604,
  .x 1605,
  .x 1606,
  .x 1607,
  .x 1608,
  .x 1609,
  .x 1610,
  .x 1611,
  .x 1612]
private def block2592 : List Gate := [
  .make 1558 433 1559,
  .make 1559 934 1560,
  .make 1560 935 1561,
  .make 1561 936 1562,
  .make 1562 937 1563,
  .make 1563 938 1564,
  .make 1564 939 1565,
  .make 1565 940 1566,
  .make 1566 941 1567]
private def block2601 : List Gate := [
  .make 1567 942 1568,
  .make 1568 943 1569,
  .make 1569 944 1570,
  .make 1570 945 1571,
  .make 1571 946 1572,
  .make 1572 947 1573,
  .make 1573 948 1574,
  .make 1574 949 1575,
  .make 1575 950 1576,
  .make 1576 951 1577,
  .make 1577 952 1578,
  .make 1578 953 1579,
  .make 1579 954 1580,
  .make 1580 955 1581,
  .make 1581 956 1582,
  .make 1582 957 1583,
  .make 1583 958 1584,
  .make 1584 959 1585,
  .make 1585 960 1586,
  .make 1586 961 1587,
  .make 1587 962 1588,
  .make 1588 963 1589,
  .make 1589 964 1590,
  .make 1590 965 1591,
  .make 1591 966 1592,
  .make 1592 967 1593,
  .make 1593 968 1594,
  .make 1594 969 1595,
  .make 1595 970 1596,
  .make 1596 971 1597,
  .make 1597 972 1613,
  .make 1613 973 1614,
  .make 1614 974 1615,
  .make 1615 975 1616,
  .make 1616 976 1617,
  .make 1617 977 1618,
  .make 1618 978 1619,
  .make 1619 979 1620,
  .make 1620 980 1621,
  .make 1621 981 1622,
  .make 1622 982 1623,
  .make 1623 983 1624,
  .make 1624 984 1625,
  .make 1625 985 1626,
  .make 1626 986 1627,
  .make 1627 987 1628,
  .make 1628 988 1629,
  .make 1629 989 1630,
  .make 1630 990 1631,
  .make 1631 991 1632,
  .make 1632 992 1633,
  .make 1633 993 1634,
  .make 1634 994 1635,
  .make 1635 995 1636,
  .make 1636 996 1637,
  .make 1637 997 1638,
  .make 1638 998 1639,
  .make 1639 999 1640,
  .make 1640 1000 1641,
  .make 1641 1001 1642,
  .make 1642 1002 1643,
  .make 1643 1003 1644,
  .make 1644 1004 1645,
  .make 1645 1005 1646,
  .make 1646 1006 1647,
  .make 1647 1007 1648,
  .make 1648 1008 1649,
  .make 1649 1009 1650,
  .make 1650 1010 1651,
  .make 1651 1011 1652,
  .make 1652 1012 1653,
  .make 1653 1013 1654,
  .make 1654 1014 1655,
  .make 1655 1015 1656,
  .make 1656 1016 1657,
  .make 1657 1017 1658,
  .make 1658 1018 1659,
  .make 1659 1019 1660,
  .make 1660 1020 1661,
  .make 1661 1021 1662,
  .make 1662 1022 1663,
  .make 1663 1023 1664,
  .make 1664 1024 1665,
  .make 1665 1025 1666,
  .make 1666 1026 1667,
  .make 1667 1027 1668,
  .make 1668 1028 1669]
private def block2688 : List Gate := [
  .make 1669 1598 1670,
  .make 1670 1599 1671,
  .make 1671 1600 1672,
  .make 1672 1601 1673,
  .make 1673 1602 1674,
  .make 1674 1603 1675,
  .make 1675 1604 1676,
  .make 1676 1605 1677,
  .make 1677 1606 1678]
private def block2697 : List Gate := [
  .make 1678 1607 1679,
  .make 1679 1608 1680,
  .make 1680 1609 1681,
  .make 1681 1610 1682,
  .make 1682 1611 1683,
  .make 1683 1612 1684,
  .cx 1684 1557,
  .x 1557,
  .pop 1683 1612 1684,
  .pop 1682 1611 1683,
  .pop 1681 1610 1682,
  .pop 1680 1609 1681,
  .pop 1679 1608 1680,
  .pop 1678 1607 1679,
  .pop 1677 1606 1678,
  .pop 1676 1605 1677,
  .pop 1675 1604 1676,
  .pop 1674 1603 1675,
  .pop 1673 1602 1674,
  .pop 1672 1601 1673,
  .pop 1671 1600 1672,
  .pop 1670 1599 1671,
  .pop 1669 1598 1670,
  .pop 1668 1028 1669,
  .pop 1667 1027 1668,
  .pop 1666 1026 1667,
  .pop 1665 1025 1666,
  .pop 1664 1024 1665,
  .pop 1663 1023 1664,
  .pop 1662 1022 1663,
  .pop 1661 1021 1662,
  .pop 1660 1020 1661,
  .pop 1659 1019 1660,
  .pop 1658 1018 1659,
  .pop 1657 1017 1658,
  .pop 1656 1016 1657,
  .pop 1655 1015 1656,
  .pop 1654 1014 1655,
  .pop 1653 1013 1654,
  .pop 1652 1012 1653,
  .pop 1651 1011 1652,
  .pop 1650 1010 1651,
  .pop 1649 1009 1650,
  .pop 1648 1008 1649,
  .pop 1647 1007 1648,
  .pop 1646 1006 1647,
  .pop 1645 1005 1646,
  .pop 1644 1004 1645,
  .pop 1643 1003 1644,
  .pop 1642 1002 1643,
  .pop 1641 1001 1642,
  .pop 1640 1000 1641,
  .pop 1639 999 1640,
  .pop 1638 998 1639,
  .pop 1637 997 1638,
  .pop 1636 996 1637,
  .pop 1635 995 1636,
  .pop 1634 994 1635,
  .pop 1633 993 1634,
  .pop 1632 992 1633,
  .pop 1631 991 1632,
  .pop 1630 990 1631,
  .pop 1629 989 1630,
  .pop 1628 988 1629,
  .pop 1627 987 1628,
  .pop 1626 986 1627,
  .pop 1625 985 1626,
  .pop 1624 984 1625,
  .pop 1623 983 1624,
  .pop 1622 982 1623,
  .pop 1621 981 1622,
  .pop 1620 980 1621,
  .pop 1619 979 1620,
  .pop 1618 978 1619,
  .pop 1617 977 1618,
  .pop 1616 976 1617,
  .pop 1615 975 1616,
  .pop 1614 974 1615,
  .pop 1613 973 1614,
  .pop 1597 972 1613,
  .pop 1596 971 1597,
  .pop 1595 970 1596,
  .pop 1594 969 1595,
  .pop 1593 968 1594,
  .pop 1592 967 1593,
  .pop 1591 966 1592,
  .pop 1590 965 1591]
private def block2784 : List Gate := [
  .pop 1589 964 1590,
  .pop 1588 963 1589,
  .pop 1587 962 1588,
  .pop 1586 961 1587,
  .pop 1585 960 1586,
  .pop 1584 959 1585,
  .pop 1583 958 1584,
  .pop 1582 957 1583,
  .pop 1581 956 1582]
private def block2793 : List Gate := [
  .pop 1580 955 1581,
  .pop 1579 954 1580,
  .pop 1578 953 1579,
  .pop 1577 952 1578,
  .pop 1576 951 1577,
  .pop 1575 950 1576,
  .pop 1574 949 1575,
  .pop 1573 948 1574,
  .pop 1572 947 1573,
  .pop 1571 946 1572,
  .pop 1570 945 1571,
  .pop 1569 944 1570,
  .pop 1568 943 1569,
  .pop 1567 942 1568,
  .pop 1566 941 1567,
  .pop 1565 940 1566,
  .pop 1564 939 1565,
  .pop 1563 938 1564,
  .pop 1562 937 1563,
  .pop 1561 936 1562,
  .pop 1560 935 1561,
  .pop 1559 934 1560,
  .pop 1558 433 1559,
  .x 1612,
  .x 1611,
  .x 1610,
  .x 1609,
  .x 1608,
  .x 1607,
  .x 1606,
  .x 1605,
  .x 1604,
  .x 1603,
  .x 1602,
  .x 1601,
  .x 1600,
  .x 1599,
  .x 1598,
  .x 1028,
  .x 1027,
  .x 1026,
  .x 1025,
  .x 1024,
  .x 1023,
  .x 1022,
  .x 1021,
  .x 1020,
  .x 1019,
  .x 1018,
  .x 1017,
  .x 1016,
  .x 1015,
  .x 1014,
  .x 1013,
  .x 1012,
  .x 1011,
  .x 1010,
  .x 1009,
  .x 1008,
  .x 1007,
  .x 1006,
  .x 1005,
  .x 1004,
  .x 1003,
  .x 1002,
  .x 1001,
  .x 1000,
  .x 999,
  .x 998,
  .x 997,
  .x 996,
  .x 995,
  .x 994,
  .x 993,
  .x 992,
  .x 991,
  .x 990,
  .x 989,
  .x 988,
  .x 987,
  .x 986,
  .x 985,
  .x 984,
  .x 983,
  .x 982,
  .x 981,
  .x 980]
private def block2880 : List Gate := [
  .x 979,
  .x 978,
  .x 977,
  .x 976,
  .x 975,
  .x 974,
  .x 973,
  .x 972,
  .x 971]
private def block2889 : List Gate := [
  .x 970,
  .x 969,
  .x 968,
  .x 967,
  .x 966,
  .x 965,
  .x 964,
  .x 963,
  .x 962,
  .x 961,
  .x 960,
  .x 959,
  .x 958,
  .x 957,
  .x 956,
  .x 955,
  .x 954,
  .x 953,
  .x 952,
  .x 951,
  .x 950,
  .x 949,
  .x 948,
  .x 947,
  .x 946,
  .x 945,
  .x 944,
  .x 943,
  .x 942,
  .x 941,
  .x 940,
  .x 939,
  .x 938,
  .x 937,
  .x 936,
  .x 935,
  .x 934,
  .x 433,
  .x 1558,
  .pop 431 432 1558,
  .make 1556 1557 1558,
  .x 1558,
  .x 907,
  .x 908,
  .x 909,
  .x 910,
  .x 911,
  .x 912,
  .x 913,
  .x 914,
  .x 915,
  .x 916,
  .x 917,
  .x 918,
  .make 1558 907 1559,
  .make 1559 908 1560,
  .make 1560 909 1561,
  .make 1561 910 1562,
  .make 1562 911 1563,
  .make 1563 912 1564,
  .make 1564 913 1565,
  .make 1565 914 1566,
  .make 1566 915 1567,
  .make 1567 916 1568,
  .make 1568 917 1569,
  .make 1569 918 1570,
  .cx 1570 1556,
  .x 1556,
  .pop 1569 918 1570,
  .pop 1568 917 1569,
  .pop 1567 916 1568,
  .pop 1566 915 1567,
  .pop 1565 914 1566,
  .pop 1564 913 1565,
  .pop 1563 912 1564,
  .pop 1562 911 1563,
  .pop 1561 910 1562,
  .pop 1560 909 1561,
  .pop 1559 908 1560,
  .pop 1558 907 1559,
  .x 918,
  .x 917,
  .x 916,
  .x 915,
  .x 914,
  .x 913,
  .x 912]
private def block2976 : List Gate := [
  .x 911,
  .x 910,
  .x 909,
  .x 908,
  .x 907,
  .x 1558,
  .x 286,
  .x 287,
  .x 288]
private def block2985 : List Gate := [
  .x 289,
  .x 290,
  .x 291,
  .x 292,
  .x 293,
  .x 294,
  .x 295,
  .x 296,
  .x 297,
  .x 298,
  .x 299,
  .x 300,
  .cx 1700 907,
  .cx 1700 908,
  .cx 1700 909,
  .cx 1700 910,
  .cx 1700 911,
  .cx 1700 912,
  .cx 1700 913,
  .cx 1700 914,
  .cx 1700 915,
  .cx 1700 916,
  .cx 1700 917,
  .cx 1700 918,
  .cx 422 907,
  .ccx 300 907 422,
  .cx 422 907,
  .cx 423 908,
  .ccx 300 908 423,
  .cx 423 908,
  .cx 424 909,
  .ccx 300 909 424,
  .cx 424 909,
  .cx 425 910,
  .ccx 300 910 425,
  .cx 425 910,
  .cx 426 911,
  .ccx 300 911 426,
  .cx 426 911,
  .cx 427 912,
  .ccx 300 912 427,
  .cx 427 912,
  .cx 428 913,
  .ccx 300 913 428,
  .cx 428 913,
  .cx 429 914,
  .ccx 300 914 429,
  .cx 429 914,
  .cx 430 915,
  .ccx 300 915 430,
  .cx 430 915,
  .cx 431 916,
  .ccx 300 916 431,
  .cx 431 916,
  .cx 432 917,
  .ccx 300 917 432,
  .cx 432 917,
  .cx 433 918,
  .ccx 300 918 433,
  .cx 433 918]
private def block3045 : List Gate := [
  .x 1799,
  .make 1702 1799 1556,
  .x 1798,
  .make 1556 1798 1559,
  .x 1797,
  .make 1559 1797 1560,
  .x 1796,
  .make 1560 1796 1561,
  .x 1795,
  .make 1561 1795 1562,
  .cx 1562 1699,
  .pop 1561 1795 1562,
  .x 1795,
  .pop 1560 1796 1561,
  .x 1796,
  .pop 1559 1797 1560,
  .x 1797,
  .pop 1556 1798 1559,
  .x 1798,
  .pop 1702 1799 1556,
  .x 1799,
  .cx 934 919,
  .cx 919 934,
  .cx 934 919,
  .cx 935 920,
  .cx 920 935,
  .cx 935 920]
private def block3072 : List Gate := [
  .cx 936 921,
  .cx 921 936,
  .cx 936 921,
  .cx 937 922,
  .cx 922 937,
  .cx 937 922,
  .cx 938 923,
  .cx 923 938,
  .cx 938 923]
private def block3081 : List Gate := [
  .cx 939 924,
  .cx 924 939,
  .cx 939 924,
  .cx 940 925,
  .cx 925 940,
  .cx 940 925,
  .cx 941 926,
  .cx 926 941,
  .cx 941 926,
  .cx 942 927,
  .cx 927 942,
  .cx 942 927,
  .cx 943 928,
  .cx 928 943,
  .cx 943 928,
  .cx 944 929,
  .cx 929 944,
  .cx 944 929,
  .cx 945 930,
  .cx 930 945,
  .cx 945 930,
  .cx 946 931,
  .cx 931 946,
  .cx 946 931,
  .cx 947 932,
  .cx 932 947,
  .cx 947 932,
  .cx 948 933,
  .cx 933 948,
  .cx 948 933,
  .cx 949 934,
  .cx 934 949,
  .cx 949 934,
  .cx 950 935,
  .cx 935 950,
  .cx 950 935,
  .cx 951 936,
  .cx 936 951,
  .cx 951 936,
  .cx 952 937,
  .cx 937 952,
  .cx 952 937,
  .cx 953 938,
  .cx 938 953,
  .cx 953 938,
  .cx 954 939,
  .cx 939 954,
  .cx 954 939,
  .cx 955 940,
  .cx 940 955,
  .cx 955 940,
  .cx 956 941,
  .cx 941 956,
  .cx 956 941,
  .cx 957 942,
  .cx 942 957,
  .cx 957 942,
  .cx 958 943,
  .cx 943 958,
  .cx 958 943,
  .cx 959 944,
  .cx 944 959,
  .cx 959 944,
  .cx 960 945,
  .cx 945 960,
  .cx 960 945,
  .cx 961 946,
  .cx 946 961,
  .cx 961 946,
  .cx 962 947,
  .cx 947 962,
  .cx 962 947,
  .cx 963 948,
  .cx 948 963,
  .cx 963 948,
  .cx 964 949,
  .cx 949 964,
  .cx 964 949,
  .cx 965 950,
  .cx 950 965,
  .cx 965 950,
  .cx 966 951,
  .cx 951 966,
  .cx 966 951,
  .cx 967 952,
  .cx 952 967,
  .cx 967 952]
private def block3168 : List Gate := [
  .cx 968 953,
  .cx 953 968,
  .cx 968 953,
  .cx 969 954,
  .cx 954 969,
  .cx 969 954,
  .cx 970 955,
  .cx 955 970,
  .cx 970 955]
private def block3177 : List Gate := [
  .cx 971 956,
  .cx 956 971,
  .cx 971 956,
  .cx 972 957,
  .cx 957 972,
  .cx 972 957,
  .cx 973 958,
  .cx 958 973,
  .cx 973 958,
  .cx 974 959,
  .cx 959 974,
  .cx 974 959,
  .cx 975 960,
  .cx 960 975,
  .cx 975 960,
  .cx 976 961,
  .cx 961 976,
  .cx 976 961,
  .cx 977 962,
  .cx 962 977,
  .cx 977 962,
  .cx 978 963,
  .cx 963 978,
  .cx 978 963,
  .cx 979 964,
  .cx 964 979,
  .cx 979 964,
  .cx 980 965,
  .cx 965 980,
  .cx 980 965,
  .cx 981 966,
  .cx 966 981,
  .cx 981 966,
  .cx 982 967,
  .cx 967 982,
  .cx 982 967,
  .cx 983 968,
  .cx 968 983,
  .cx 983 968,
  .cx 984 969,
  .cx 969 984,
  .cx 984 969,
  .cx 985 970,
  .cx 970 985,
  .cx 985 970,
  .cx 986 971,
  .cx 971 986,
  .cx 986 971,
  .cx 987 972,
  .cx 972 987,
  .cx 987 972,
  .cx 988 973,
  .cx 973 988,
  .cx 988 973,
  .cx 989 974,
  .cx 974 989,
  .cx 989 974,
  .cx 990 975,
  .cx 975 990,
  .cx 990 975,
  .cx 991 976,
  .cx 976 991,
  .cx 991 976,
  .cx 992 977,
  .cx 977 992,
  .cx 992 977,
  .cx 993 978,
  .cx 978 993,
  .cx 993 978,
  .cx 994 979,
  .cx 979 994,
  .cx 994 979,
  .cx 995 980,
  .cx 980 995,
  .cx 995 980,
  .cx 996 981,
  .cx 981 996,
  .cx 996 981,
  .cx 997 982,
  .cx 982 997,
  .cx 997 982,
  .cx 998 983,
  .cx 983 998,
  .cx 998 983,
  .cx 999 984,
  .cx 984 999,
  .cx 999 984]
private def block3264 : List Gate := [
  .cx 1000 985,
  .cx 985 1000,
  .cx 1000 985,
  .cx 1001 986,
  .cx 986 1001,
  .cx 1001 986,
  .cx 1002 987,
  .cx 987 1002,
  .cx 1002 987]
private def block3273 : List Gate := [
  .cx 1003 988,
  .cx 988 1003,
  .cx 1003 988,
  .cx 1004 989,
  .cx 989 1004,
  .cx 1004 989,
  .cx 1005 990,
  .cx 990 1005,
  .cx 1005 990,
  .cx 1006 991,
  .cx 991 1006,
  .cx 1006 991,
  .cx 1007 992,
  .cx 992 1007,
  .cx 1007 992,
  .cx 1008 993,
  .cx 993 1008,
  .cx 1008 993,
  .cx 1009 994,
  .cx 994 1009,
  .cx 1009 994,
  .cx 1010 995,
  .cx 995 1010,
  .cx 1010 995,
  .cx 1011 996,
  .cx 996 1011,
  .cx 1011 996,
  .cx 1012 997,
  .cx 997 1012,
  .cx 1012 997,
  .cx 1013 998,
  .cx 998 1013,
  .cx 1013 998,
  .cx 1014 999,
  .cx 999 1014,
  .cx 1014 999,
  .cx 1015 1000,
  .cx 1000 1015,
  .cx 1015 1000,
  .cx 1016 1001,
  .cx 1001 1016,
  .cx 1016 1001,
  .cx 1017 1002,
  .cx 1002 1017,
  .cx 1017 1002,
  .cx 1018 1003,
  .cx 1003 1018,
  .cx 1018 1003,
  .cx 1019 1004,
  .cx 1004 1019,
  .cx 1019 1004,
  .cx 1020 1005,
  .cx 1005 1020,
  .cx 1020 1005,
  .cx 1021 1006,
  .cx 1006 1021,
  .cx 1021 1006,
  .cx 1022 1007,
  .cx 1007 1022,
  .cx 1022 1007,
  .cx 1023 1008,
  .cx 1008 1023,
  .cx 1023 1008,
  .cx 1024 1009,
  .cx 1009 1024,
  .cx 1024 1009,
  .cx 1025 1010,
  .cx 1010 1025,
  .cx 1025 1010,
  .cx 1026 1011,
  .cx 1011 1026,
  .cx 1026 1011,
  .cx 1027 1012,
  .cx 1012 1027,
  .cx 1027 1012,
  .cx 1028 1013,
  .cx 1013 1028,
  .cx 1028 1013,
  .cx 1557 1691,
  .cx 1691 1557,
  .cx 1557 1691,
  .cx 1558 1692,
  .cx 1692 1558,
  .cx 1558 1692,
  .cx 1700 1693,
  .cx 1693 1700,
  .cx 1700 1693]
private def block3360 : List Gate := [
  .cx 1698 1694,
  .cx 1694 1698,
  .cx 1698 1694,
  .cx 1702 1695,
  .cx 1695 1702,
  .cx 1702 1695,
  .cx 1701 1696,
  .cx 1696 1701,
  .cx 1701 1696]
private def group0 : List Gate := block0 ++ block9 ++ block96 ++ block105 ++ block192 ++ block201 ++ block288 ++ block297 ++ block384 ++ block393 ++ block480 ++ block489 ++ block576 ++ block585 ++ block672 ++ block681 ++ block768 ++ block777 ++ block864 ++ block873 ++ block960 ++ block969 ++ block1056 ++ block1065 ++ block1152 ++ block1161 ++ block1248 ++ block1257 ++ block1344 ++ block1353 ++ block1440 ++ block1449 ++ block1536 ++ block1545 ++ block1632 ++ block1641 ++ block1728 ++ block1737 ++ block1824 ++ block1833 ++ block1920 ++ block1929 ++ block2016 ++ block2025 ++ block2112 ++ block2121 ++ block2208 ++ block2217 ++ block2304 ++ block2313 ++ block2400 ++ block2409
private def pre0 : Nat := (0x1fe007fffffffffffffffffffffffeffffeffffe <<< 1556)
private def post0 : Nat := (0x1fe007fffffffffffffffffff80002ffffefffe8 <<< 1556)
private theorem cert0 : bitCheck group0 post0 = some pre0 := by decide +kernel
private def group1 : List Gate := block2412 ++ block2496 ++ block2505 ++ block2592 ++ block2601 ++ block2688 ++ block2697 ++ block2784 ++ block2793 ++ block2880 ++ block2889 ++ block2976 ++ block2985
private def pre1 : Nat := (0x1fe007fffffffffffffffffffe0003fffffffff8 <<< 1556)
private def post1 : Nat := (0x1fe007fffffffffffffffffffe0003fffffffff8 <<< 1556)
private theorem cert1 : bitCheck group1 post1 = some pre1 := by decide +kernel
private def group2 : List Gate := block3045 ++ block3072 ++ block3081 ++ block3168 ++ block3177 ++ block3264 ++ block3273 ++ block3360
private def pre2 : Nat := (0x1fe0007ffffffffffffffffffe0003fffffffff9 <<< 1556)
private def post2 : Nat := (0x1fe0007ffffffffffffffffffe0003fffffffff9 <<< 1556)
private theorem cert2 : bitCheck group2 post2 = some pre2 := by decide +kernel
private def ops := group0 ++ (group1 ++ group2)
private theorem fPart0 : leave270Part0 = GateMirror.forward block0 ++ GateMirror.forward block9 := by rfl
private theorem bPart0 : leaveInv270Part0 = GateMirror.inverse block3360 ++ GateMirror.inverse block3273 := by rfl
private theorem fPart1 : leave270Part1 = GateMirror.forward block96 ++ GateMirror.forward block105 := by rfl
private theorem bPart1 : leaveInv270Part1 = GateMirror.inverse block3264 ++ GateMirror.inverse block3177 := by rfl
private theorem fPart2 : leave270Part2 = GateMirror.forward block192 ++ GateMirror.forward block201 := by rfl
private theorem bPart2 : leaveInv270Part2 = GateMirror.inverse block3168 ++ GateMirror.inverse block3081 := by rfl
private theorem fPart3 : leave270Part3 = GateMirror.forward block288 ++ GateMirror.forward block297 := by rfl
private theorem bPart3 : leaveInv270Part3 = GateMirror.inverse block3072 ++ GateMirror.inverse block3045 ++ GateMirror.inverse block2985 := by rfl
private theorem fPart4 : leave270Part4 = GateMirror.forward block384 ++ GateMirror.forward block393 := by rfl
private theorem bPart4 : leaveInv270Part4 = GateMirror.inverse block2976 ++ GateMirror.inverse block2889 := by rfl
private theorem fPart5 : leave270Part5 = GateMirror.forward block480 ++ GateMirror.forward block489 := by rfl
private theorem bPart5 : leaveInv270Part5 = GateMirror.inverse block2880 ++ GateMirror.inverse block2793 := by rfl
private theorem fPart6 : leave270Part6 = GateMirror.forward block576 ++ GateMirror.forward block585 := by rfl
private theorem bPart6 : leaveInv270Part6 = GateMirror.inverse block2784 ++ GateMirror.inverse block2697 := by rfl
private theorem fPart7 : leave270Part7 = GateMirror.forward block672 ++ GateMirror.forward block681 := by rfl
private theorem bPart7 : leaveInv270Part7 = GateMirror.inverse block2688 ++ GateMirror.inverse block2601 := by rfl
private theorem fPart8 : leave270Part8 = GateMirror.forward block768 ++ GateMirror.forward block777 := by rfl
private theorem bPart8 : leaveInv270Part8 = GateMirror.inverse block2592 ++ GateMirror.inverse block2505 := by rfl
private theorem fPart9 : leave270Part9 = GateMirror.forward block864 ++ GateMirror.forward block873 := by rfl
private theorem bPart9 : leaveInv270Part9 = GateMirror.inverse block2496 ++ GateMirror.inverse block2412 ++ GateMirror.inverse block2409 := by rfl
private theorem fPart10 : leave270Part10 = GateMirror.forward block960 ++ GateMirror.forward block969 := by rfl
private theorem bPart10 : leaveInv270Part10 = GateMirror.inverse block2400 ++ GateMirror.inverse block2313 := by rfl
private theorem fPart11 : leave270Part11 = GateMirror.forward block1056 ++ GateMirror.forward block1065 := by rfl
private theorem bPart11 : leaveInv270Part11 = GateMirror.inverse block2304 ++ GateMirror.inverse block2217 := by rfl
private theorem fPart12 : leave270Part12 = GateMirror.forward block1152 ++ GateMirror.forward block1161 := by rfl
private theorem bPart12 : leaveInv270Part12 = GateMirror.inverse block2208 ++ GateMirror.inverse block2121 := by rfl
private theorem fPart13 : leave270Part13 = GateMirror.forward block1248 ++ GateMirror.forward block1257 := by rfl
private theorem bPart13 : leaveInv270Part13 = GateMirror.inverse block2112 ++ GateMirror.inverse block2025 := by rfl
private theorem fPart14 : leave270Part14 = GateMirror.forward block1344 ++ GateMirror.forward block1353 := by rfl
private theorem bPart14 : leaveInv270Part14 = GateMirror.inverse block2016 ++ GateMirror.inverse block1929 := by rfl
private theorem fPart15 : leave270Part15 = GateMirror.forward block1440 ++ GateMirror.forward block1449 := by rfl
private theorem bPart15 : leaveInv270Part15 = GateMirror.inverse block1920 ++ GateMirror.inverse block1833 := by rfl
private theorem fPart16 : leave270Part16 = GateMirror.forward block1536 ++ GateMirror.forward block1545 := by rfl
private theorem bPart16 : leaveInv270Part16 = GateMirror.inverse block1824 ++ GateMirror.inverse block1737 := by rfl
private theorem fPart17 : leave270Part17 = GateMirror.forward block1632 ++ GateMirror.forward block1641 := by rfl
private theorem bPart17 : leaveInv270Part17 = GateMirror.inverse block1728 ++ GateMirror.inverse block1641 := by rfl
private theorem fPart18 : leave270Part18 = GateMirror.forward block1728 ++ GateMirror.forward block1737 := by rfl
private theorem bPart18 : leaveInv270Part18 = GateMirror.inverse block1632 ++ GateMirror.inverse block1545 := by rfl
private theorem fPart19 : leave270Part19 = GateMirror.forward block1824 ++ GateMirror.forward block1833 := by rfl
private theorem bPart19 : leaveInv270Part19 = GateMirror.inverse block1536 ++ GateMirror.inverse block1449 := by rfl
private theorem fPart20 : leave270Part20 = GateMirror.forward block1920 ++ GateMirror.forward block1929 := by rfl
private theorem bPart20 : leaveInv270Part20 = GateMirror.inverse block1440 ++ GateMirror.inverse block1353 := by rfl
private theorem fPart21 : leave270Part21 = GateMirror.forward block2016 ++ GateMirror.forward block2025 := by rfl
private theorem bPart21 : leaveInv270Part21 = GateMirror.inverse block1344 ++ GateMirror.inverse block1257 := by rfl
private theorem fPart22 : leave270Part22 = GateMirror.forward block2112 ++ GateMirror.forward block2121 := by rfl
private theorem bPart22 : leaveInv270Part22 = GateMirror.inverse block1248 ++ GateMirror.inverse block1161 := by rfl
private theorem fPart23 : leave270Part23 = GateMirror.forward block2208 ++ GateMirror.forward block2217 := by rfl
private theorem bPart23 : leaveInv270Part23 = GateMirror.inverse block1152 ++ GateMirror.inverse block1065 := by rfl
private theorem fPart24 : leave270Part24 = GateMirror.forward block2304 ++ GateMirror.forward block2313 := by rfl
private theorem bPart24 : leaveInv270Part24 = GateMirror.inverse block1056 ++ GateMirror.inverse block969 := by rfl
private theorem fPart25 : leave270Part25 = GateMirror.forward block2400 ++ GateMirror.forward block2409 ++ GateMirror.forward block2412 := by rfl
private theorem bPart25 : leaveInv270Part25 = GateMirror.inverse block960 ++ GateMirror.inverse block873 := by rfl
private theorem fPart26 : leave270Part26 = GateMirror.forward block2496 ++ GateMirror.forward block2505 := by rfl
private theorem bPart26 : leaveInv270Part26 = GateMirror.inverse block864 ++ GateMirror.inverse block777 := by rfl
private theorem fPart27 : leave270Part27 = GateMirror.forward block2592 ++ GateMirror.forward block2601 := by rfl
private theorem bPart27 : leaveInv270Part27 = GateMirror.inverse block768 ++ GateMirror.inverse block681 := by rfl
private theorem fPart28 : leave270Part28 = GateMirror.forward block2688 ++ GateMirror.forward block2697 := by rfl
private theorem bPart28 : leaveInv270Part28 = GateMirror.inverse block672 ++ GateMirror.inverse block585 := by rfl
private theorem fPart29 : leave270Part29 = GateMirror.forward block2784 ++ GateMirror.forward block2793 := by rfl
private theorem bPart29 : leaveInv270Part29 = GateMirror.inverse block576 ++ GateMirror.inverse block489 := by rfl
private theorem fPart30 : leave270Part30 = GateMirror.forward block2880 ++ GateMirror.forward block2889 := by rfl
private theorem bPart30 : leaveInv270Part30 = GateMirror.inverse block480 ++ GateMirror.inverse block393 := by rfl
private theorem fPart31 : leave270Part31 = GateMirror.forward block2976 ++ GateMirror.forward block2985 ++ GateMirror.forward block3045 := by rfl
private theorem bPart31 : leaveInv270Part31 = GateMirror.inverse block384 ++ GateMirror.inverse block297 := by rfl
private theorem fPart32 : leave270Part32 = GateMirror.forward block3072 ++ GateMirror.forward block3081 := by rfl
private theorem bPart32 : leaveInv270Part32 = GateMirror.inverse block288 ++ GateMirror.inverse block201 := by rfl
private theorem fPart33 : leave270Part33 = GateMirror.forward block3168 ++ GateMirror.forward block3177 := by rfl
private theorem bPart33 : leaveInv270Part33 = GateMirror.inverse block192 ++ GateMirror.inverse block105 := by rfl
private theorem fPart34 : leave270Part34 = GateMirror.forward block3264 ++ GateMirror.forward block3273 := by rfl
private theorem bPart34 : leaveInv270Part34 = GateMirror.inverse block96 ++ GateMirror.inverse block9 := by rfl
private theorem fPart35 : leave270Part35 = GateMirror.forward block3360 := by rfl
private theorem bPart35 : leaveInv270Part35 = GateMirror.inverse block0 := by rfl
private theorem fEq : GateMirror.forward ops = leave270 := by
  simp only [ops,group0,group1,group2,fwAppend,leave270,fPart0,fPart1,fPart2,fPart3,fPart4,fPart5,fPart6,fPart7,fPart8,fPart9,fPart10,fPart11,fPart12,fPart13,fPart14,fPart15,fPart16,fPart17,fPart18,fPart19,fPart20,fPart21,fPart22,fPart23,fPart24,fPart25,fPart26,fPart27,fPart28,fPart29,fPart30,fPart31,fPart32,fPart33,fPart34,fPart35,List.append_assoc]
private theorem bEq : GateMirror.inverse ops = leaveInv270 := by
  simp only [ops,group0,group1,group2,bwAppend,leaveInv270,bPart0,bPart1,bPart2,bPart3,bPart4,bPart5,bPart6,bPart7,bPart8,bPart9,bPart10,bPart11,bPart12,bPart13,bPart14,bPart15,bPart16,bPart17,bPart18,bPart19,bPart20,bPart21,bPart22,bPart23,bPart24,bPart25,bPart26,bPart27,bPart28,bPart29,bPart30,bPart31,bPart32,bPart33,bPart34,bPart35,List.append_assoc]

private theorem pEq : GateMirror.forward group0 = leave270.take 2412 := by rfl
private theorem takePrefix (a b : Program) (n : Nat) (len : a.length=n) :
    (a++b).take n=a := by
  rw [←len,List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil]
private theorem qEq : GateMirror.forward (group0++group1) = leave270.take 3045 := by
  have len : (GateMirror.forward (group0++group1)).length=3045 := by decide +kernel
  have cut : (GateMirror.forward ops).take 3045=GateMirror.forward (group0++group1) := by
    rw [ops,←List.append_assoc,fwAppend]
    exact takePrefix _ _ _ len
  exact cut.symm.trans (congrArg (List.take 3045) fEq)

def initialSites : List Wire := List.range' 1556 139 ++ List.range' 1705 8
theorem inverts (s:State) (phase:∀m,(run leave270 m s).phase=s.phase)
    (initial:∀q∈initialSites,s.basis q=false)
    (core:zeros (run (leave270.take 2412) [] s) [1560,1576,1596,1613,1614])
    (post:(run (leave270.take 3045) [] s).basis 1556=false) (m n:List Bool) :
    run leaveInv270 n (run leave270 m s)=s := by
  let s1:=run (GateMirror.forward group0) [] s
  let s2:=run (GateMirror.forward group1) [] s1
  have s2e:s2=run (GateMirror.forward (group0++group1)) [] s:=by
    simp [s2,s1,GateMirror.forward,List.map_append,run_append]
  have i0:Masked s pre0:=subMask (by decide +kernel) (fromList initial)
  obtain ⟨h0,r0,z0⟩:=bit_sound group0 s _ _ cert0 i0
  have kc:zeros s1 [1560,1576,1596,1613,1614]:=by simpa only [s1,pEq] using core
  have i1:Masked s1 pre1:=subMask (by decide +kernel) (bothMasks z0 (fromList kc))
  obtain ⟨h1,r1,z1⟩:=bit_sound group1 s1 _ _ cert1 i1
  have kp:zeros s2 [1556]:=by
    intro q hq
    obtain rfl: q=1556:=by simpa using hq
    rw [s2e,qEq];exact post
  have i2:Masked s2 pre2:=subMask (by decide +kernel) (bothMasks z1 (fromList kp))
  obtain ⟨h2,r2,z2⟩:=bit_sound group2 s2 _ _ cert2 i2
  have phys:∀g∈ops,proper g=true:=by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact h0 g h
    · rcases List.mem_append.mp h with h|h
      · exact h1 g h
      · exact h2 g h
  have ready:Ready s ops:=ready_append _ _ _ r0 (ready_append _ _ _ r1 r2)
  rw [←bEq,←fEq]
  exact invert ops s phys (all_prepared ops s phys (by rwa [fEq])) ready m n
end ECDSAAdd.Entrant.StairPacket.Leave270Mirror

end

/- middle: certified source line 21669. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave270Selector Leave270RetireActual Leave270Barrel Leave270High Leave270Word Leave270Join
open LeaveReadoutFrame Leave270OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def body:Program := ((leave270.drop 242).take 2170)
theorem shape : body=fullPrefix false++Leave270Core.work := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, eq_self, Bool.false_eq_true, ↓reduceIte, ECDSAAdd.Entrant.StairPacket.Leave270Selector.fullPrefix, ECDSAAdd.Entrant.StairPacket.Leave270Selector.program, ECDSAAdd.Entrant.StairPacket.Leave270Selector.initPC, ECDSAAdd.Entrant.StairPacket.Leave270Core.work, ECDSAAdd.Entrant.StairPacket.Leave270Routed.body]
def untouched (q:Wire) := q∉(fullPrefix false).map destination
instance (q:Wire):Decidable (untouched q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run

theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool)
    (small:min z.u z.v<2^121) (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (shadow:∀i<18,s.basis (423+i)=(Leave270TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈[ports.crossing,ports.near]++List.range' 1559 39,s.basis q=false)
    (par:parityBits ports s.basis=oddBits (IntegerHigh.letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤LeaveSelector.key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=LeaveSelector.key (actualMode 121 z))) :
    let out:=run body tape s
    let t:=run (fullPrefix false) tape s
    out.phase=s.phase ∧ (∀i<121,out.basis (live i)=(Leave270TrueMiddle.F z).testBit i) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀q,outside wire 121 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → out.basis q=cleared t.basis q) := by
  let k:=actualMode 121 z
  let t:=run (fullPrefix false) tape s
  have base : ∀q:Nat,1561≤q → q≤1597 → s.basis q=false := by
    intro q lo hi
    apply zero
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  have prepared:t=⟨s.phase,fun q=>(prior k q).read s.basis⟩ := preparedState false s tape s.basis z.u k mode
    (zero _ (by decide)) (zero _ (by decide))
    (beforeFresh _ _ _ base (zero _ (by decide)) (zero _ (by decide))) events
  have sym (q:Wire):t.basis q=(prior k q).read s.basis := congrArg (fun st:State=>st.basis q) prepared
  have keep (q:Wire) (ok:untouched q) : t.basis q=s.basis q := preserved _ s tape q ok
  have cs : ∀q∈carries,untouched q := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pad : ∀i:Fin 121,106 ≤ i.val → untouched (wire i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sh : ∀i:Fin 18,untouched (423+i.val) := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have ysOK : ∀q∈ys,untouched q := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pa : ∀q∈paritySites,untouched q := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw : ∀i:Fin 15,untouched (Leave270Hit.swaps i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270Routed.untouched); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have math:=Leave270Loaded.signed z s.basis small odd room (fun i hi=>shadow i (Nat.lt_trans hi (by decide : 16<18))) par
  have flags:=mode_flags (s.basis 1698) (s.basis 1699) (⟨IntegerHigh.wait 15 z.u, by have h:=IntegerHigh.wait_le 15 z.u;omega⟩:Fin 16)
  have leftOK:left k=(t.basis 1698 && t.basis 1699) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.1
  have rightOK:right k=(t.basis 1698 && !t.basis 1699) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.2.1
  have done:=Leave270Core.result z t (tape.drop (measurementCount (fullPrefix false))) k s.basis small odd room
    (fun q h=>(keep _ (cs q h)).trans (clean q h)) (fun i lo hi=>(keep _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (fun q h=>(sym q).trans (Leave270Loaded.tags z s.basis q h)) (fun i h=>(keep _ (sh ⟨i,h⟩)).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h=>keep _ (ysOK q h))).trans bank)
    ((sym _).trans math.1) (fun far=>(sym _).trans (math.2.2 far)) (fun j=>sym _)
    (fun q h=>(keep _ (pa q h)).symm) (by rw [sym 1597,sym 1701]; exact math.2.1) leftOK rightOK
    (fun on i hi h=>(keep _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans (by rw [prepared]),done.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave270Routed

end

/- front: certified source line 26553. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270EntryAction
open Arithmetic Partial LeaveSelector Leave270Selector Leave270Close Leave270InputScan Leave270Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oddRead (v:BasisState) := (List.range 15).map (fun i=> !v (ports.g+i))
theorem flipped : flipHistory=notRegister history := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem historyGeom : ∀q∈history,q∉scanPart.map destination ∧ q∉Leave270EraseActual.program.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem parity (s:State) (m:List Bool) : parityBits ports (run entry m s).basis=oddRead s.basis := by
  let u:=run scanPart m s
  let n:=m.drop (measurementCount scanPart)
  let v:=run flipHistory n u
  have inv:v=⟨u.phase,fun q=>if q∈history then !u.basis q else u.basis q⟩ := by
    change run flipHistory n u=_
    rw [flipped,notRegister_correct _ (by decide)]
  have sites : ∀j:Fin 15,ports.g+j.val∈history := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  have mem:=sites ⟨i,List.mem_range.mp hi⟩
  obtain ⟨before,after⟩:=historyGeom _ mem
  rw [Leave270Front.emitted,run_append,run_take,run_append,run_take]
  change (run _ _ v).basis _=_
  rw [preserved _ v _ _ after,inv]
  change (if _ then !u.basis _ else u.basis _)=_
  rw [if_pos mem,preserved _ s m _ before]

theorem upperBits (a:SkywalkNat.State) (v:BasisState)
    (bits:∀i<19,v (422+i)=((a.u+a.v)/2^121).testBit i) :
    ∀i<18,v (423+i)=((a.u+a.v)/2^122).testBit i := by
  intro i hi
  have div:(a.u+a.v)/2^122=((a.u+a.v)/2^121)/2^1 := by rw [Nat.div_div_eq_div_mul];rfl
  rw [div,Nat.testBit_div_two_pow]
  rw [show (423:Nat)+i=422+(i+1) by omega]
  exact bits (i+1) (Nat.succ_lt_succ hi)
end ECDSAAdd.Entrant.StairPacket.Leave270EntryAction

end

/- front: certified source line 26594. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion270 Leave270InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave270Front LeaveSelector Leave270Selector

def watched : List Wire := [1701,1702]++List.range' 1559 39

theorem frame (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    ∀q∈watched,(run entry m s).basis q=s.basis q := by
  let a:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  let e:=negative sg a.u
  let u:=run scanPart m s
  let t:=m.drop (measurementCount scanPart)
  let v:=run flipHistory t u
  let tape:=t.drop (measurementCount flipHistory)
  have scanActual:=Leave270InputScan.result s m a.u a.v G sg ready fresh
  have hist (q:Wire) (h:q∉flipHistory.map destination) : v.basis q=u.basis q := preserved _ _ _ _ h
  have phase : v.phase=u.phase := by rfl
  have outputBits (i:Nat) (hi:i<19) : v.basis (422+i)=((a.u+a.v)/2^121).testBit i ∧ v.basis (907+i)=((a.u-e.toNat)/2^121).testBit i := by
    have ok : ∀j:Fin 19,422+j.val∉flipHistory.map destination ∧ 907+j.val∉flipHistory.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [hist _ (ok ⟨i,hi⟩).1,hist _ (ok ⟨i,hi⟩).2];exact scanActual.2.2.1 i hi
  have same (q:Wire) (good:q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs) : v.basis q=s.basis q :=
    (hist _ good.1).trans (scanActual.2.2.2 _ good.2.1 good.2.2)
  have clean : ∀q∈1556::1557::1558::fullC,v.basis q=false := by
    intro q h
    rw [same _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈1556::1557::1558::fullC,q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs) q h)]
    exact scratch _ h
  have temps : ∀p∈longPairs,v.basis p.2=false := by
    intro p h
    rw [same _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1700 ∧ p.2∉RailPair.sites pairs) p h)]
    exact temp _ h
  have cap:=LeaveShadowRails.inputFit 121 z small
  have fit : (a.u-e.toNat)/2^121 < 2^19 := lt_of_le_of_lt (Nat.div_le_div_right (show a.u-e.toNat≤a.u+a.v by omega)) cap.2
  have se : e.toNat≤1 := by cases e <;> decide
  have su : e.toNat≤a.u := by
    by_cases h : 0<a.u
    · omega
    · simp [e,negative,h]
  have done:=Leave270EraseActual.result v tape a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  rw [Leave270Front.emitted,run_append,run_take,run_append,run_take]
  intro q h
  have geometry : ∀q∈watched,q∉1556::1557::1558::fullM ∧ q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have g:=geometry q h
  exact (done.2.2.2.2 q g.1).trans (same q g.2)

end ECDSAAdd.Entrant.StairPacket.Leave270FrontReady

end

/- middle: certified source line 26653. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion270 Leave270OutputPorts LeaveReadoutFrame
open Leave270Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retained : ∀q∈1556::1558::smallM,q∉Leave270Routed.body.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem carryIndex : ∀q∈smallC,∃i:Fin 39,q=1559+i.val := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
attribute [local irreducible] run SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m m':List Bool)
    (small:min z.u z.v<2^121) (mag0:regValue fullM s.basis=0)
    (flags:let a:=step^[15] (Shadow.reduced 121 15 z)
           let e:=(negative sg a.u).toNat
           s.basis 1556=decide (2^121≤a.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^121) a.u a.v e)
    (liveBits:∀i<121,(run Leave270Routed.body m s).basis (live i)=(Leave270TrueMiddle.F z).testBit i)
    (retired:∀i:Fin 39,(run Leave270Routed.body m s).basis (1559+i.val)=false) :
    let a:=step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let u:=run Leave270Routed.body m s
    let v:=run restore m' u
    v.phase=u.phase ∧ (∀q,q∉smallM → v.basis q=u.basis q) ∧
      regValue smallM v.basis=(mag/2^122)%2^11 ∧
      v.basis 1556=decide (2^121≤mag) ∧ (∀i<121,v.basis (live i)=(Leave270TrueMiddle.F z).testBit i) := by
  let u:=run Leave270Routed.body m s
  have keep (q:Wire) (h:q∈1556::1558::smallM) : u.basis q=s.basis q := preserved _ _ _ q (retained q h)
  have clear:∀q∈smallC,u.basis q=false := by
    intro q h
    obtain ⟨i,rfl⟩:=carryIndex q h
    exact retired i
  have mag:regValue smallM u.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    exact (keep q (by simp [h])).trans ((regValue_zero _ _).mp mag0 q ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈smallM,q∈fullM) q h))
  have reg:=(outputRegisters u (Leave270TrueMiddle.F z) liveBits).1
  have old:= (keep 1556 (by decide)).trans flags.1
  have new:=Leave270Restored.result z sg u m' small clear mag
    ⟨old,(congrArg Bool.toNat (keep 1558 (by decide))).trans flags.2,reg⟩
  have ch:=LeaveRestoreTruth.truth 121 z small sg
  refine ⟨new.1,new.2.1,new.2.2,?_,?_⟩
  · rw [new.2.1 _ (by decide),old,ch.1,ch.2.2.2]
  · intro i hi
    have outside:∀j:Fin 121,live j∉smallM := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (new.2.1 _ (outside ⟨i,hi⟩)).trans (liveBits i hi)

end ECDSAAdd.Entrant.StairPacket.Leave270RoutedRestore

end

/- front: certified source line 27288. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion270
open Leave270Front Leave270FrontReady LeaveSelector Leave270Selector Leave270Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem prepare (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (zero:∀q∈watched,s.basis q=false) (k:Mode) (smallU:Nat)
    (mode:k=farMode ((run entry m s).basis 1698) ((run entry m s).basis 1699) smallU)
    (exchange:right k=true → ∀i<15,i≤key k → (run entry m s).basis (swaps i)=decide (i=key k)) :
    let a:=run entry m s
    run (entry++fullPrefix false) m s=⟨a.phase,fun q=>(sim Leave270Selector.prepare (LeaveSelector.start ports false k) q).read a.basis⟩ := by
  let a:=run entry m s
  have keep:=Leave270FrontReady.frame s m z G sg small ready fresh scratch temp
  have clear (q:Wire) (h:q∈watched) : a.basis q=false := (keep q h).trans (zero q h)
  have cells (q:Nat) (lo:1561≤q) (hi:q≤1597) : q∈watched := by
    unfold watched
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  rw [run_append,run_take]
  apply preparedState false a _ a.basis smallU k mode (clear _ (by decide)) (clear _ (by decide))
  · exact beforeFresh ports k a.basis (fun q lo hi=>clear q (cells q lo hi)) (clear _ (by decide)) (clear _ (by decide))
  · exact exchange

end ECDSAAdd.Entrant.StairPacket.Leave270FrontPrepare

end

/- middle: certified source line 27324. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program:=leave270.take 2476
theorem shape : program=entry++(Leave270Routed.body++restore) := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.LeaveCompanion270.restore, ECDSAAdd.Entrant.StairPacket.Leave270Front.entry, ECDSAAdd.Entrant.StairPacket.Leave270Routed.body, ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.program]
def unmodified (q:Wire) := q∉entry.map destination
instance (q:Wire):Decidable (unmodified q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z))) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run program m s
    out.phase=s.phase ∧ regValue smallM out.basis=(mag/2^122)%2^11 ∧
    out.basis 1556=decide (2^121≤mag) ∧ (∀i<121,out.basis (live i)=(Leave270TrueMiddle.F z).testBit i) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  have front:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave270FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pad:∀i:Fin 121,106 ≤ i.val → unmodified (wire i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have rawBank:∀q∈ys,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw:∀i:Fin 15,unmodified (Leave270Hit.swaps i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have used:=Leave270Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave270EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave270EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave270RoutedRestore.result z sg a n (n.drop (measurementCount Leave270Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take]
  exact ⟨restored.1.trans (used.1.trans front.1),restored.2.2.1,restored.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic

end

/- middle: certified source line 27385. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^121) (odd : z.v % 2 = 1)
    (record : readCells (shape 13) 0 15 (mappedBasis 13 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    Leave270EntryAction.oddRead s.basis = oddBits (letters 15 (Shadow.reduced 121 15 z)) := by
  have ports : Leave270EntryAction.oddRead s.basis =
      (readCells (shape 13) 0 15 (mappedBasis 13 s.basis)).map (fun pair => !pair.1) := by rfl
  rw [ports,record,←true_records 121 z small odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd _ _ small odd)

end ECDSAAdd.Entrant.StairPacket.Leave270RecordedParity

end

/- middle: certified source line 27854. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave270FullArithmetic Leave270Join Leave270Word

def program:=leave270.take 2412
theorem shape:program=entry++Leave270Routed.body := by simp only [ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270Front.entry, ECDSAAdd.Entrant.StairPacket.Leave270Routed.body, ECDSAAdd.Entrant.StairPacket.Leave270CoreCheckpoint.program]
def rawSites:=List.range' 1613 82 ++ List.range' 1703 82

def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 121,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  have front:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave270FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pad:∀i:Fin 121,106 ≤ i.val → unmodified (wire i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have rawBank:∀q∈ys,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw:∀i:Fin 15,unmodified (Leave270Hit.swaps i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have used:=Leave270Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave270EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave270EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave270Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave270CoreCheckpoint

end

/- middle: certified source line 27938. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave270FullArithmetic Leave270Join
def targets := (pendingPairs++clearFlagPairs).map Prod.snd

private theorem geometry : ∀q∈targets,q∉smallM ∧
    ((∃i:Fin 39,q=1559+i.val) ∨
      (q∈carries ∧ (∀i:Fin 121,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
       q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597))) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z))) :
    ∀q∈targets,(run program m s).basis q=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  have front:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave270FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pad:∀i:Fin 121,106 ≤ i.val → unmodified (wire i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have rawBank:∀q∈ys,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw:∀i:Fin 15,unmodified (Leave270Hit.swaps i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have used:=Leave270Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave270EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave270EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave270RoutedRestore.result z sg a n (n.drop (measurementCount Leave270Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  intro q hq
  obtain ⟨outsideMag,side⟩:=geometry q hq
  rw [Leave270FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ outsideMag]
  rcases side with ⟨i,rfl⟩|⟨carry,notWire,cols,noPrefix,noSelector⟩
  · exact used.2.2.2.1 i
  · rw [used.2.2.2.2 q (fun i hi=>notWire ⟨i,hi⟩) cols,cleared,if_neg noSelector]
    exact (preserved (fullPrefix false) a n q noPrefix).trans ((kept q (cs q carry)).trans (clean q carry))
end ECDSAAdd.Entrant.StairPacket.Leave270FlagScratch

end

/- middle: certified source line 28003. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion270 Leave270InputScan Leave270Front
open LeaveReadoutFrame Leave270MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave270.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem split : Leave270FullArithmetic.program=beforeOpen++(openPart++interior) := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270MaskThrough.openPart, ECDSAAdd.Entrant.StairPacket.Leave270MaskThrough.interior, ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.program, ECDSAAdd.Entrant.StairPacket.Leave270MaskCut.beforeOpen]
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave270FullArithmetic.program m s
    v.basis 907=decide (2^121≤mag%(2*2^121)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave270InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1700 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1700 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 907 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 907=e.basis 907 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)))
  have raw:e.basis 907=((h.u-(negative sg h.u).toNat)/2^121).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 121 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave270MaskCut

end

/- middle: certified source line 28062. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

theorem result (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^121) (odd : z.v % 2 = 1)
    (record : readCells (shape 13) 0 15 (mappedBasis 13 s.basis) =
      SkywalkTrace.trace 15 (encode g sg z.u z.v)) :
    let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
    Leave270Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd ∧
    (right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) →
      s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z))) := by
  let xs:=SkywalkTrace.trace 15 (encode g sg z.u z.v)
  have tape : (List.range 15).map (fun i=>s.basis (Leave270Hit.swaps i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record]
    rfl
  constructor
  · rw [←record];rfl
  · intro rightSide i hi early
    have far : Shadow.far 121 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩:=modeKey 121 z far
    have side : decide (2^121≤z.u)=false := by rw [orientation] at rightSide;simpa using rightSide
    have keyWait : key (actualMode 121 z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveTraceHistory.firstSwap 121 z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before

end ECDSAAdd.Entrant.StairPacket.Leave270RecordedEvents

end

/- tail: certified source line 28567. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave270.take 2982
theorem shape : program=Leave270FullArithmetic.program++(Leave270MaskThrough.closePart++Leave270TailFlags.program) := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270MaskThrough.closePart, ECDSAAdd.Entrant.StairPacket.Leave270TailFlags.program, ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.program, ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore.program]
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 114 15 a)
    let v:=run Leave270FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^114≤a.u)) ∧
      regValue smallM out.basis=(mag/2^122)%2^11 ∧
      (∀i<121,out.basis (live i)=(Leave270TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave270FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave270FullArithmetic.program)
  let u:=run Leave270MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave270MaskThrough.closePart)
  have ar:=Leave270FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave270FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave270MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 121,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have bits:∀i<121,u.basis (live i)=(Leave270TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 114 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave270TrueMiddle.F z/2^8<2^113 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave270NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave270FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave270FlagScratch.targets,q≠1557 ∧ q≠1558 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave270TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 114 15 a)
  let side:=f && decide (2^114≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore
end

/- tail: certified source line 28995. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def afterFront:Program := ((leave270.drop 242).take 2740)
theorem shape : Leave270BeforeStore.program=entry++afterFront := by simp only [ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270Front.entry, ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore.program, ECDSAAdd.Entrant.StairPacket.Leave270StoreCoordinates.afterFront]
def afterFlip:Program := ((leave270.drop 93).take 2889)
theorem flippedShape : Leave270BeforeStore.program=Leave270InputScan.scanPart++(flipHistory++afterFlip) := by simp only [ECDSAAdd.Entrant.WSlimV3.seg_merge, ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270InputScan.scanPart, ECDSAAdd.Entrant.StairPacket.Leave270Front.flipHistory, ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore.program, ECDSAAdd.Entrant.StairPacket.Leave270StoreCoordinates.afterFlip]
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let out:=run Leave270BeforeStore.program m s
    out.basis 1700=negative sg a.u ∧ (∀q∈history,out.basis q= !s.basis q) ∧
    (∀i:Fin 12,out.basis (422+i.val)=(a.u+a.v).testBit (121+i.val) ∧
        out.basis (907+i.val)=mag.testBit (121+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  let out:=run Leave270BeforeStore.program m s
  have src:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have stored:=Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have lowMag:=( Leave270MaskCut.result s m z G sg small ready fresh scratch temp).1
  have raw (q:Wire) (ok:q∉afterFront.map destination):out.basis q=(run entry m s).basis q := by
    change (run Leave270BeforeStore.program m s).basis q=_
    rw [shape,run_append,run_take];exact preserved _ _ _ _ ok
  have truth:=LeaveShadowRails.retainedLow 121 z small sg
  have hist (q:Wire) (hq:q∈history):out.basis q= !s.basis q := by
    let sc:=run Leave270InputScan.scanPart m s
    let tape:=m.drop (measurementCount Leave270InputScan.scanPart)
    let v:=run flipHistory tape sc
    have inv:v=⟨sc.phase,fun q=>if q∈history then !sc.basis q else sc.basis q⟩ := by
      change run flipHistory tape sc=_
      rw [Leave270EntryAction.flipped,notRegister_correct _ (by decide)]
    have bounds:∀q∈history,286≤q ∧ q≤300 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have all : afterFlip.all (fun g=>decide (destination g<286 ∨ 300<destination g))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have ok:∀q∈history,q∉afterFlip.map destination := by
      intro q member bad
      obtain ⟨g,hg,rfl⟩:=List.mem_map.mp bad
      have hit := of_decide_eq_true (List.all_eq_true.mp all g hg)
      obtain ⟨l,r⟩:=bounds _ member
      exact hit.elim (Nat.not_lt_of_ge l) (Nat.not_lt_of_ge r)
    change (run Leave270BeforeStore.program m s).basis q=_
    rw [flippedShape,run_append,run_take,run_append,run_take]
    change (run _ _ v).basis q=_
    rw [preserved _ _ _ _ (ok q hq),inv]
    change (if _ then !sc.basis q else sc.basis q)=_
    rw [if_pos hq,preserved _ _ _ _ ((Leave270EntryAction.historyGeom _ hq).1)]
  refine ⟨(raw 1700 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))).trans (src.2.2.1.trans truth.1.symm),hist,?_⟩
  intro i
  cases ix:i.val with
  | zero =>
    simp only [Nat.add_zero]
    have same:=congrArg (fun n:Nat=>n.testBit 121) truth.2.1
    simp only [Nat.testBit_mod_two_pow,show decide (121<122)=true from rfl,Bool.true_and] at same
    have a0:=src.2.2.2.2.2 0 (by decide)
    rw [Nat.testBit_div_two_pow] at a0
    have bit:=thresholdBit (a.u-(negative sg a.u).toNat) (2^121) (by decide)
    rw [Nat.testBit_div_two_pow] at bit
    exact ⟨(raw 422 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))).trans (a0.trans same.symm), (stored.2.2.2.2.2.2 _ (by decide) (by decide) (by decide)).trans (lowMag.trans bit.symm)⟩
  | succ j =>
    have hj:j<11:=by have lim:=i.isLt;omega
    have mapA : ∀u:Fin 11,live u.val=422+(u.val+1) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have mapM : ∀u:Fin 11,smallM.getD u.val 0=907+(u.val+1) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have pos:=stored.2.2.2.2.2.1 j (by omega)
    have signedBit:=HighBankAdjust.bit_read smallM j out.basis (by exact hj)
    rw [mapM ⟨j,hj⟩,stored.2.2.2.2.1,Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr hj,Bool.true_and,Nat.testBit_div_two_pow] at signedBit
    change out.basis (live j)=((a.u+a.v)/2^122).testBit j at pos
    rw [mapA ⟨j,hj⟩,Nat.testBit_div_two_pow] at pos
    simpa only [show j+122=121+(j+1) by omega] using And.intro pos signedBit
end ECDSAAdd.Entrant.StairPacket.Leave270StoreCoordinates
end

/- tail: certified source line 29397. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program := leave270.take 3045
theorem shape : program=Leave270BeforeStore.program++beforeTags := by simp only [ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.Leave270Close.beforeTags, ECDSAAdd.Entrant.StairPacket.Leave270BeforeStore.program, ECDSAAdd.Entrant.StairPacket.Leave270StoreMapped.program]
attribute [local irreducible] run SkywalkNat.step

private theorem store (s v:State) (m:List Bool) (G sign:Bool) (sum mag:Nat)
    (previous:s.basis 300=G) (hist:∀q∈history,v.basis q= !s.basis q) (signed:v.basis 1700=sign)
    (words:∀i:Fin 12,v.basis (422+i.val)=sum.testBit (121+i.val) ∧ v.basis (907+i.val)=mag.testBit (121+i.val)) :
    let out:=run beforeTags m v
    out.phase=v.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 12,let pos:=sum.testBit (121+i.val);let neg:=mag.testBit (121+i.val) ^^ sign
                   out.basis (422+i.val)=(if G then neg else pos) ∧ out.basis (907+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=v.basis q := by
  have wrote:=lowResult v m
  let h:=fun q:Wire=>if q∈history then !v.basis q else v.basis q
  have ctrl:h 300=G := by simp only [h,if_pos (by decide : 300∈history),hist 300 (by decide),Bool.not_not,previous]
  have signBit:h 1700=sign := by simpa only [h,if_neg (by decide : 1700∉history)] using signed
  refine ⟨wrote.1,?_,?_,?_⟩
  · intro q hq
    have sep:∀a∈history,a∉RailPair.sites low:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    rw [wrote.2.1 q (sep q hq)];simp only [if_pos hq,hist q hq,Bool.not_not]
  · intro i
    let pair:Wire×Wire:=(422+i.val,907+i.val)
    have sites:∀j:Fin 12,(422+j.val,907+j.val)∈low ∧ 422+j.val∉history ∧ 907+j.val∉history:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have l:=wrote.2.2 pair (sites i).1
    change _=(if h 300 then h pair.2 ^^ h 1700 else h pair.1) ∧ _=(if h 300 then h pair.1 else h pair.2 ^^ h 1700) at l
    have pos:h pair.1=sum.testBit (121+i.val):=by simpa only [h,pair,if_neg (sites i).2.1] using (words i).1
    have neg:h pair.2=mag.testBit (121+i.val):=by simpa only [h,pair,if_neg (sites i).2.2] using (words i).2
    rw [ctrl,signBit,pos,neg] at l
    exact l
  · intro q lo hn
    exact (wrote.2.1 q lo).trans (if_neg hn)

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let before:=run Leave270BeforeStore.program m s
    let out:=run program m s
    out.phase=s.phase ∧ (∀q∈history,out.basis q=s.basis q) ∧
    (∀i:Fin 12,let pos:=(a.u+a.v).testBit (121+i.val);let neg:=mag.testBit (121+i.val) ^^ sign
                   out.basis (422+i.val)=(if G then neg else pos) ∧ out.basis (907+i.val)=(if G then pos else neg)) ∧
    ∀q,q∉RailPair.sites low → q∉history → out.basis q=before.basis q := by
  have coords:=Leave270StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have prev:s.basis 300=G := by have h:=ready.2.2.1;cases G <;> exact h
  have phase:=(Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have done:=store s _ (m.drop (measurementCount Leave270BeforeStore.program)) G _ _ _ prev coords.2.1 coords.1 coords.2.2
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans phase,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave270StoreMapped
end

/- tail: certified source line 30093. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave270FullArithmetic Leave270Word Leave270Join Leave270Close
theorem untouchedHigh (q:Nat) (h:441≤q ∧ q≤528) : q∉Leave270StoreMapped.program.map destination := by
  have all:Leave270StoreMapped.program.all (fun g=>decide (destination g<441 ∨ 528<destination g))=true:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro m
  obtain ⟨g,hg,rfl⟩:=List.mem_map.mp m
  exact (of_decide_eq_true (List.all_eq_true.mp all g hg)).elim (Nat.not_lt_of_ge h.1) (Nat.not_lt_of_ge h.2)
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z))) (top:∀q:Nat,441≤q → q≤528 → s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) :
    ∀i:Fin 95,(run Leave270StoreMapped.program m s).basis (434+i.val)=false := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  have front:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave270FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have pad:∀i:Fin 121,106 ≤ i.val → unmodified (wire i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have rawBank:∀q∈ys,unmodified q:=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have sw:∀i:Fin 15,unmodified (Leave270Hit.swaps i):=by ((try unfold ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.unmodified); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have used:=Leave270Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave270EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave270EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have restored:=Leave270RoutedRestore.result z sg a n (n.drop (measurementCount Leave270Routed.body)) small
    front.2.1 ⟨front.2.2.2.1,front.2.2.2.2.1⟩ used.2.1 used.2.2.2.1
  have store:=(Leave270StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flag:=(Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2.2.2.2
  intro i
  let q:Nat:=434+i.val
  by_cases ext:441≤q
  · have hi:q≤528 := by dsimp [q]; have h:=i.isLt;omega
    exact (preserved Leave270StoreMapped.program s m q (untouchedHigh q ⟨ext,hi⟩)).trans (top q ext hi)
  · have lim:i.val<7 := by dsimp [q] at ext;omega
    let j:Fin 7:=⟨i.val,lim⟩
    have geom:∀j:Fin 7,let q:Nat:=434+j.val
        q∉RailPair.sites low ∧ q∉history ∧ q≠1556 ∧ q≠1557 ∧ q≠1558 ∧ q∉smallM ∧ ∃i:Fin 18,q=(row i).free := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    obtain ⟨l,h,x,y,z,mr,idx,e⟩:=geom j
    rw [store _ l h,flag _ x y z]
    rw [Leave270FullArithmetic.shape,run_append,run_take,run_append,run_take,restored.2.1 _ mr]
    exact e ▸ used.2.2.1 idx
end ECDSAAdd.Entrant.StairPacket.Leave270HighZero
end

/- tail: certified source line 30166. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def suffix:= ((leave270.drop 334).take 2711)
theorem split : Leave270StoreMapped.program=(entry++fullPrefix false)++suffix := by simp only [ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, Bool.false_eq_true, ↓reduceIte, ECDSAAdd.Entrant.StairPacket.Leave270Selector.fullPrefix, ECDSAAdd.Entrant.StairPacket.Leave270Selector.program, ECDSAAdd.Entrant.StairPacket.Leave270Selector.initPC, ECDSAAdd.Entrant.StairPacket.Leave270Front.entry, ECDSAAdd.Entrant.StairPacket.Leave270StoreMapped.program, ECDSAAdd.Entrant.StairPacket.Leave270PostReady.suffix]
def rawSites := [1698,1699]++(Leave270Close.events.map Prod.fst)

private theorem avoid (prg:Program) (sites:List Wire) (checked:prg.all (fun g=>decide (destination g∉sites))=true) (q:Wire) (mem:q∈sites) :
    q∉prg.map destination := by
  intro bad
  obtain ⟨g,h,rfl⟩:=List.mem_map.mp bad
  exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)) mem

theorem rawLayout:∀q∈rawSites,q∉Leave270StoreMapped.program.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem keptLayout:∀q∈[1701,1702],q∉suffix.map destination := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

private theorem nearOf (p:Ports) (k:Mode) (sym:Sym) (controls:reads p sym=LeaveSelector.controls p k):
    sym p.near=.bit (nearby k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at controls
  exact controls.1
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) :
    let out:=run Leave270StoreMapped.program m s
    let f:=decide (Shadow.far 121 15 z)
    out.basis 1698=s.basis 1698 ∧ out.basis 1699=s.basis 1699 ∧
    out.basis 1702=nearby (actualMode 121 z) ∧
    out.basis 1701=(f && HighBankSum.cross (Leave270TrueMiddle.d z)) ∧
    (∀p∈Leave270Close.events,out.basis p.1=s.basis p.1 ∧ out.basis p.2=false) := by
  let a:=run entry m s
  let k:=actualMode 121 z
  let o:=run Leave270StoreMapped.program m s
  have selRaw (q:Wire) (ok:q∉entry.map destination):a.basis q=s.basis q := preserved entry s m q ok
  have sw:∀i:Fin 15,Leave270Hit.swaps i∉entry.map destination:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have prepared:=Leave270FrontPrepare.prepare s m z G sg small ready fresh scratch temp zero k z.u
    (by change k=farMode (a.basis _) (a.basis _) z.u;rw [selRaw _ (by decide),selRaw _ (by decide)];exact mode)
    (fun on i hi h=>(selRaw _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  have hit (q:Wire) (ok:q∈[1701,1702]):o.basis q=(Leave270RetireActual.prior k q).read a.basis := by
    change (run Leave270StoreMapped.program m s).basis q=_
    rw [split,run_append,run_take,preserved _ _ _ q (keptLayout q ok),prepared];rfl
  have h:=Leave270Front.result s m z G sg small ready fresh scratch temp
  have act:=Leave270EntryAction.upperBits _ a.basis h.2.2.2.2.2
  have math:=Leave270Loaded.signed z a.basis small odd room (fun i hi=>act i (Nat.lt_trans hi (by decide : 16<18)))
    ((Leave270EntryAction.parity s m).trans par)
  have near:Leave270RetireActual.prior k 1702=.bit (nearby k) := nearOf ports k _ (controlCert k)
  have plain (q:Wire) (ok:q∈rawSites):o.basis q=s.basis q:=preserved _ _ _ _ (rawLayout q ok)
  have store:=(Leave270StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have cleared:=Leave270FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  refine ⟨plain _ (by decide),plain _ (by decide),(hit _ (by decide)).trans (congrArg (Expr.read a.basis) near),?_,?_⟩
  · refine (hit _ (by decide)).trans (math.1.trans ?_);by_cases g:Shadow.far 121 15 z <;> simp [g]
  · intro p member
    have geom:∀p∈Leave270Close.events,p.1∈rawSites ∧ p.2∉RailPair.sites low ∧ p.2∉history ∧
      (p.2=1556 ∨ (p.2≠1556 ∧ p.2≠1557 ∧ p.2≠1558 ∧ p.2∈Leave270FlagScratch.targets)) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    obtain ⟨src,nl,nh,dst⟩:=geom _ member
    refine ⟨plain _ src,(store _ nl nh).trans ?_⟩
    rcases dst with e|⟨a,b,c,hq⟩
    · rw [e];exact flags.2.1
    · exact (flags.2.2.2.2.2.2 _ a b c).trans (cleared _ hq)
end ECDSAAdd.Entrant.StairPacket.Leave270PostReady
end

/- roundtrip: certified source line 30579. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121)
    (phase:∀o,(run leave270 o s).phase=s.phase)
    : run leaveInv270 n (run leave270 m s)=s:=by
  have atCore:=Leave270CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave270PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have initial : ∀q∈Leave270Mirror.initialSites,s.basis q=false := by
    have native :
        ((IntegerPacket.ports (shape 13) 15).carry.map (windowNet 13)) =
          List.range' 1556 139 := by decide +kernel
    intro q hq
    change q∈List.range' 1556 139 ++ List.range' 1705 8 at hq
    rcases List.mem_append.mp hq with hn | he
    · apply native_carry 13 _ s ready q
      rw [native]
      exact hn
    · apply clean q
      exact (by decide +kernel :
        ∀q∈List.range' 1705 8,q∈Leave270High.carries) q he
  apply Leave270Mirror.inverts s phase initial _ _ m n
  · exact Leave270CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1799,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave270Roundtrip
end

/- tail: certified source line 30614. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem split : leave270=Leave270StoreMapped.program++afterLow := by simp only [ECDSAAdd.Entrant.WSlimV3.take_drop', eq_self, ECDSAAdd.Entrant.StairPacket.Leave270Close.afterLow, ECDSAAdd.Entrant.StairPacket.Leave270StoreMapped.program]
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 121 15 z → chain (decide (2^121≤z.u)) xs)
    (first:Shadow.far 121 15 z → decide (2^121≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave270Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1698=decide (Shadow.far 121 15 z))
    (side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u))) :
    let u:=decide (2^121≤z.u)
    let active:=decide (Shadow.far 121 15 z)
    let v:=run Leave270StoreMapped.program m s
    let out:=run leave270 m s
    out.phase=s.phase ∧ out.basis 1694=active ∧ out.basis 1695=(active && afterFlags u (xs.take 5)) ∧
      out.basis 1696=(active && HighBankSum.cross (Leave270TrueMiddle.d z)) ∧
      ∀q,out.basis q=writeBit v.basis 1699 false (LeaveRelocation.source moves q) := by
  let v:=run Leave270StoreMapped.program m s
  let u:=decide (2^121≤z.u)
  let active:=decide (Shadow.far 121 15 z)
  let w:Fin 16:=⟨wait 15 z.u,by have h:=wait_le 15 z.u;omega⟩
  have h:=Leave270PostReady.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have pre:=(Leave270StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).1
  have reads:Leave270Close.events.map (fun p=>v.basis p.1)=(xs.take 5).map Prod.snd :=
    (List.map_congr_left (fun p hp=>(h.2.2.2.2 p hp).1)).trans saved
  have done:=Leave270Posted.result v (m.drop (measurementCount Leave270StoreMapped.program)) active u (HighBankSum.cross (Leave270TrueMiddle.d z)) w xs len
    (fun hf=>historyOK (of_decide_eq_true hf)) (fun hf hu=>first (of_decide_eq_true hf) hu)
    reads (h.1.trans far) (h.2.1.trans side) h.2.2.1 h.2.2.2.1 (fun p hp=>(h.2.2.2.2 p hp).2)
  dsimp only
  rw [split,run_append,run_take]
  exact ⟨done.1.trans pre,done.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave270Whole
end

/- tail: certified source line 31024. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave270Word

def zeros := (List.range' 1556 135)++(List.range' 1697 88)++List.range' 1014 15
def retired (q:Wire):Prop:=
  q=1699 ∨ (q≠1699 ∧ q∉RailPair.sites low ∧ q∉history ∧
  (q=1556 ∨ (q≠1556 ∧ q≠1557 ∧ q≠1558 ∧
   ((q∈Leave270CoreCheckpoint.targets ∧ q∉smallM) ∨ (∃i:Fin 15,q=live (106+i.val))))))
instance (q:Wire):Decidable (retired q):=by unfold retired;infer_instance
theorem routed:∀q∈zeros,retired (LeaveRelocation.source moves q) := by
  have key : ∀ q ∈ zeros, (q ∉ moves.map Prod.fst ∧ q ∉ moves.map Prod.snd ∧ retired q) ∨
      retired (LeaveRelocation.source moves q) := by
    unfold retired
    open ECDSAAdd.Entrant.WSlimV3 in decide +kernel
  intro q hq
  rcases key q hq with ⟨h1, h2, h3⟩ | h
  · rwa [ECDSAAdd.Entrant.WSlimV3.source_fix moves q h1 h2]
  · exact h
theorem restoreShape : Leave270FullArithmetic.program=Leave270CoreCheckpoint.program++restore := by simp only [ECDSAAdd.Entrant.WSlimV3.take_merge, eq_self, ECDSAAdd.Entrant.StairPacket.LeaveCompanion270.restore, ECDSAAdd.Entrant.StairPacket.Leave270FullArithmetic.program, ECDSAAdd.Entrant.StairPacket.Leave270CoreCheckpoint.program]
private theorem intervalIndex (n : Nat) (lo : 1559 ≤ n) (hi : n < 1559+39) : ∃ j : Fin 39, 1559+j.val=n := by
  exact ⟨⟨n-1559, by omega⟩, by change 1559+(n-1559)=n; omega⟩
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 121 15 z → chain (decide (2^121≤z.u)) xs)
    (first:Shadow.far 121 15 z → decide (2^121≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave270Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1698=decide (Shadow.far 121 15 z))
    (side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u))) (quiet:∀q∈Leave270CoreCheckpoint.rawSites,s.basis q=false) (narrow:Leave270TrueMiddle.F z<2^106) :
    ∀q∈zeros,(run leave270 m s).basis q=false := by
  let c:=run Leave270CoreCheckpoint.program m s
  have h:=Leave270CoreCheckpoint.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have zerosAt (q:Wire) (mem:q∈Leave270CoreCheckpoint.targets):c.basis q=false := by
    simp only [Leave270CoreCheckpoint.targets,List.mem_append,List.mem_map] at mem
    rcases mem with ((scr|free)|raw)|mag
    · obtain ⟨lo,hi⟩:=List.mem_range'_1.mp scr
      obtain ⟨j,id⟩:=intervalIndex q lo hi
      rw [←id];exact h.1 j
    · obtain ⟨j,_,rfl⟩:=free;exact h.2.1 j
    · exact (h.2.2.1 q raw).trans (quiet q raw)
    · exact h.2.2.2 q mag
  have cleanCs:∀q∈smallC,c.basis q=false := fun q hq=>zerosAt _ ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈smallC,q∈Leave270CoreCheckpoint.targets) q hq)
  have clearM:regValue smallM c.basis=0:=(regValue_zero _ _).mpr (fun q hq=>h.2.2.2 q ((by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀q∈smallM,q∈Leave270CoreCheckpoint.magSites) q hq))
  have rest:=restore_run c (m.drop (measurementCount Leave270CoreCheckpoint.program)) cleanCs clearM
  have coreDone (q:Wire) (mem:q∈Leave270CoreCheckpoint.targets) (notM:q∉smallM):(run Leave270FullArithmetic.program m s).basis q=false:=by
    rw [restoreShape,run_append,run_take,rest.2.1 _ notM];exact zerosAt q mem
  have whole:=Leave270Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=(Leave270StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound).2.2.2
  have flags:=Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
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
end ECDSAAdd.Entrant.StairPacket.Leave270BoundaryClean
end

/- tail: certified source line 31110. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 121 15 z → chain (decide (2^121≤z.u)) xs)
    (first:Shadow.far 121 15 z → decide (2^121≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave270Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1698=decide (Shadow.far 121 15 z))
    (side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u))) :
    let a:=SkywalkNat.step^[15] z
    let sign:=negative sg a.u
    let mag:=a.u-sign.toNat
    let next:=decide (Shadow.far 114 15 a)
    let out:=run leave270 m s
    out.basis 1691=next ∧ out.basis 1692=(next && decide (2^114≤a.u)) ∧ out.basis 1693=sign ∧
      (∀q∈history,out.basis q=s.basis q) ∧
      (∀i:Fin 12,let pos:=(a.u+a.v).testBit (121+i.val);let neg:=mag.testBit (121+i.val) ^^ sign
                   out.basis (422+i.val)=(if G then neg else pos) ∧ out.basis (907+i.val)=(if G then pos else neg)) ∧
      ∀i:Fin 95,out.basis (919+i.val)=(a.u+a.v).testBit (133+i.val) := by
  let out:=run leave270 m s
  let v:=run Leave270StoreMapped.program m s
  let b:=run Leave270BeforeStore.program m s
  have whole:=Leave270Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have store:=Leave270StoreMapped.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have before:=Leave270BeforeStore.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have coords:=Leave270StoreCoordinates.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  have atSite (q src:Wire) (link:LeaveRelocation.source moves q=src) (clear:src≠1699):out.basis q=v.basis src := by
    rw [whole.2.2.2.2,link];simp [writeBit,clear,v]
  have flagAt (q src:Wire) (link:LeaveRelocation.source moves q=src)
      (outside:src≠1699 ∧ src∉RailPair.sites low ∧ src∉history):out.basis q=b.basis src :=
    (atSite q src link outside.1).trans (store.2.2.2 _ outside.2.1 outside.2.2)
  refine ⟨(flagAt 1691 1557 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by decide)).trans before.2.2.1,
    (flagAt 1692 1558 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by decide)).trans before.2.2.2.1,
    (flagAt 1693 1700 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by decide)).trans coords.1,?_,?_,?_⟩
  · intro q hq
    have intact:∀q∈history,LeaveRelocation.source moves q=q ∧ q≠1699:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact (atSite q q (intact q hq).1 (intact q hq).2).trans (store.2.1 q hq)
  · intro i
    have intact:∀j:Fin 12,LeaveRelocation.source moves (422+j.val)=422+j.val ∧
      LeaveRelocation.source moves (907+j.val)=907+j.val ∧ 422+j.val≠1699 ∧ 907+j.val≠1699 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    obtain ⟨hx,hy,dx,dy⟩:=intact i
    exact ⟨(atSite _ _ hx dx).trans (store.2.2.1 i).1,(atSite _ _ hy dy).trans (store.2.2.1 i).2⟩
  · intro i
    have geo:∀j:Fin 95,live (11+j.val)≠1699 ∧ live (11+j.val)∉RailPair.sites low ∧ live (11+j.val)∉history := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    have a:=flagAt _ _ (upperMap i).1 (geo i)
    have n:11+i.val<121 := by have h:=i.isLt;omega
    have hi:=(before.2.2.2.2.2.1 _ n)
    unfold Leave270TrueMiddle.F at hi
    rw [Nat.testBit_div_two_pow] at hi
    exact a.trans (by simpa only [show (11+i.val)+122=133+i.val by omega] using hi)
end ECDSAAdd.Entrant.StairPacket.Leave270EndWords
end

/- tail: certified source line 31603. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

theorem lowFrame (i:Fin 121) (s:State) (m:List Bool) :
    let v:=run leave270 m s
    v.basis (301+i.val)=s.basis (301+i.val) ∧ v.basis (786+i.val)=s.basis (786+i.val) := by
  have cover:leave270.all (fun g=>decide ((destination g<301 ∨ 422≤destination g) ∧ (destination g<786 ∨ 907≤destination g)))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have safe (q:Nat) (inside:(301≤q ∧ q<422) ∨ (786≤q ∧ q<907)):q∉leave270.map destination := by
    intro h;obtain ⟨g,hg,rfl⟩:=List.mem_map.mp h
    obtain ⟨a,d⟩:=of_decide_eq_true (List.all_eq_true.mp cover g hg)
    rcases inside with ⟨l,r⟩|⟨l,r⟩
    · exact a.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
    · exact d.elim (Nat.not_lt_of_ge l) (Nat.not_le_of_lt r)
  have hi:=i.isLt
  exact ⟨preserved _ s m _ (safe _ (Or.inl ⟨by omega,by omega⟩)),
    preserved _ s m _ (safe _ (Or.inr ⟨by omega,by omega⟩))⟩

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (par:Leave270EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 121 15 z)))
    (mode:actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u)
    (events:right (actualMode 121 z)=true → ∀i<15,i≤key (actualMode 121 z) → s.basis (Leave270Hit.swaps i)=decide (i=key (actualMode 121 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121) (xs:List (Bool×Bool)) (len:xs.length=15)
    (historyOK:Shadow.far 121 15 z → chain (decide (2^121≤z.u)) xs)
    (first:Shadow.far 121 15 z → decide (2^121≤z.u)=false → ∀i(h:i<xs.length),i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u))
    (saved:Leave270Close.events.map (fun p=>s.basis p.1)=(xs.take 5).map Prod.snd)
    (far:s.basis 1698=decide (Shadow.far 121 15 z))
    (side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u)))
    (highZero:∀q:Nat,441≤q → q≤528 → s.basis q=false)
    (raw:State) (input:let a:=SkywalkNat.step^[15] z
       SkywalkIntegerInput Leave270WideWords.L (SkywalkRails.encode G sg a.u a.v).a (SkywalkRails.encode G sg a.u a.v).b G raw.basis) :
    let o:=pullState (OB5.sig 284) raw
    let out:=run leave270 m s
    (∀i:Fin 133,out.basis (301+i.val)=o.basis (301+i.val) ∧ out.basis (786+i.val)=o.basis (786+i.val)) ∧
    ∀i:Fin 95,out.basis (434+i.val)=false ∧
      out.basis (919+i.val)=(if o.basis 300 then o.basis (919+i.val) else o.basis (434+i.val)) := by
  let a:=SkywalkNat.step^[15] z
  let h:=SkywalkNat.step^[15] (Shadow.reduced 121 15 z)
  let o:=pullState (OB5.sig 284) raw
  let out:=run leave270 m s
  have word:=Leave270EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have whole:=Leave270Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound xs len historyOK first saved far side
  have cleared:=Leave270HighZero.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events highZero nextSmall bound
  have orient:o.basis 300=G := by
    have geo:Leave270WideWords.L.previous=OB5.sig 284 300:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    change raw.basis (OB5.sig 284 300)=G
    rw [←geo];exact input.2.2.1
  have law:=LeaveShadowRails.retainedLow 121 z small sg
  constructor
  · intro i
    have fit:i.val<228:=by have h:=i.isLt;omega
    have ref:=Leave270WideWords.wide a G sg raw input ⟨i.val,fit⟩
    by_cases low:i.val<121
    · have hw:=Leave270WideWords.short h G sg s ready ⟨i.val,low⟩
      have untouched:=lowFrame ⟨i.val,low⟩ s m
      have spos:=LeaveSignedCoordinates.sharedDigit _ _ 121 i.val law.2.1 (Nat.le_of_lt low)
      have smag:=LeaveSignedCoordinates.sharedDigit _ _ 121 i.val law.2.2 (Nat.le_of_lt low)
      dsimp only at ref hw
      rw [law.1,spos,smag] at ref
      exact ⟨untouched.1.trans (hw.1.trans ref.1.symm),untouched.2.trans (hw.2.trans ref.2.symm)⟩
    · let j:Fin 12:=⟨i.val-121,by have h:=i.isLt;omega⟩
      have eq:121+j.val=i.val:=by dsimp [j];omega
      have vals:=word.2.2.2.2.1 j
      dsimp only at ref vals
      rw [eq,show (422:Nat)+j.val=301+i.val by omega,show (907:Nat)+j.val=786+i.val by omega] at vals
      exact ⟨vals.1.trans ref.1.symm,vals.2.trans ref.2.symm⟩
  · intro i
    let j:Fin 228:=⟨133+i.val,by have h:=i.isLt;omega⟩
    have ref:=Leave270WideWords.wide a G sg raw input j
    dsimp only [j] at ref
    rw [show 301+(133+i.val)=434+i.val by omega,show 786+(133+i.val)=919+i.val by omega] at ref
    have free:(run leave270 m s).basis (434+i.val)=false := by
      rw [whole.2.2.2.2,(upperMap i).2]
      exact (Function.update_of_ne (by have h:=i.isLt;change (434:Nat)+i.val≠1699;omega) _ _).trans (cleared i)
    refine ⟨free,?_⟩
    change out.basis (919+i.val)=(if o.basis 300 then o.basis (919+i.val) else o.basis (434+i.val))
    rw [orient,word.2.2.2.2.2 i];cases G <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using (by first | exact ref.1.symm | exact ref.2.symm)
end ECDSAAdd.Entrant.StairPacket.Leave270BoundaryRails
end

/- tail: certified source line 31704. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion270 Leave270Front Leave270Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

theorem swapPolarity : ∀i:Fin 15, LeaveSelector.parityAt (Leave270Hit.swaps i.val) leave270=some false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem result (s : State) (m : List Bool)
    (previous : ∀q∈Leave270Close.history,(run leave270 m s).basis q=s.basis q) :
    readCells (shape 13) 0 15 (mappedBasis 13 (run leave270 m s).basis) =
      readCells (shape 13) 0 15 (mappedBasis 13 s.basis) := by
  let rows (v : BasisState) := (List.range 15).map (fun i=>(v (286+i),v (Leave270Hit.swaps i)))
  have geometry (v : BasisState) : readCells (shape 13) 0 15 (mappedBasis 13 v)=rows v := by rfl
  rw [geometry,geometry]
  apply List.map_congr_left
  intro i hi
  have port : ∀i∈List.range 15,286+i∈Leave270Close.history := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  exact Prod.ext (previous _ (port _ hi)) (by simpa using polarity _ _ _ (swapPolarity ⟨i,List.mem_range.mp hi⟩) s m)

end ECDSAAdd.Entrant.StairPacket.Leave270PreservedRecords
end

/- tail: certified source line 31997. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^121)
    (ready:onRails 13 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis)
    (fresh:s.basis 1700=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 121 15 z+1<2^106)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,106 ≤ i → i<121 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0)
    (zero:∀q∈Leave270FrontReady.watched,s.basis q=false)
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114)
    (bound:Leave270TrueMiddle.F z<2^121)
    (far:s.basis 1698=decide (Shadow.far 121 15 z))
    (side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u))) (g0 s0 : Bool)
    (record : readCells (shape 13) 0 15 (mappedBasis 13 s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)) :
    let out:=run leave270 m s
    let cells:=readCells (shape 13) 0 15 (mappedBasis 13 out.basis)
    cells=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v) ∧
      out.basis 1694=decide (Shadow.far 121 15 z) ∧
      out.basis 1695=(decide (Shadow.far 121 15 z) && afterFlags (decide (z.v<z.u)) (cells.take 5)) ∧
      out.basis 1696=(decide (Shadow.far 121 15 z) && HighBankSum.cross (Leave270TrueMiddle.d z)) := by
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave270RecordedParity.result s z g0 s0 small odd record
  have mode : actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u:=by
    rw [far,side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave270RecordedEvents.result s z g0 s0 small odd record
  have all:=Leave270Whole.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have words:=Leave270EndWords.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode ev.2 nextSmall bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ small odd) (LeaveTraceHistory.firstSwap _ _ _ _ small odd) ev.1 far side
  have kept:=(Leave270PreservedRecords.result s m words.2.2.2.1).trans record
  refine ⟨kept,all.2.1,?_,all.2.2.2.1⟩
  rw [kept,all.2.2.1]
  by_cases active:Shadow.far 121 15 z
  · rw [LeaveTraceHistory.orient _ _ small active]
  · simp [active]
end ECDSAAdd.Entrant.StairPacket.Leave270ActualHistory
end

/- tail: certified source line 32050. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

def leftovers (q : Wire) : Prop :=
  (285≤q ∧ q<301) ∨ (1785≤q ∧ q<1813)

private theorem indexOfRange (q start count:Nat) (a:start≤q) (b:q<start+count) :
    ∃i:Fin count, start+i.val=q :=
  ⟨⟨q-start,by omega⟩,by change start+(q-start)=q;omega⟩

theorem result (s o : State) (neg far long : Bool)
    (phase : s.phase=o.phase) (sign : s.basis 1693=neg) (mode : s.basis 1691=far) (side : s.basis 1692=long)
    (low : ∀i:Fin 133, s.basis (301+i.val)=o.basis (301+i.val) ∧ s.basis (786+i.val)=o.basis (786+i.val))
    (high : ∀i:Fin 95, s.basis (434+i.val)=false ∧
      s.basis (919+i.val)=(if o.basis 300 then o.basis (919+i.val) else o.basis (434+i.val)))
    (ext : ∀q,Exterior 270 528 q → s.basis q=o.basis q)
    (left : ∀q,leftovers q → s.basis q=o.basis q)
    (clear : ∀q∈Leave270BoundaryClean.zeros,s.basis q=false)
    (released : ∀q,Leave270Reference.released q → s.basis q=o.basis q)
    (carry : ∀q:Wire,1556≤q → q≤1784 → o.basis q=false) :
    PackedCut Enter285.lowerPairs Enter285.upperPairs 300 1693 1691 1692 neg far long o (eraseSites Enter285.pending s) := by
  have loShape : Enter285.lowerPairs=(List.finRange 3).map (fun j=>(301+(130+j.val),786+(130+j.val))) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have hiShape : Enter285.upperPairs=(List.finRange 95).map (fun j=>(434+j.val,919+j.val)) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have away (q:Wire) (small:q<1556) : (eraseSites Enter285.pending s).basis q=s.basis q := by
    have no:q∉Enter285.pending:=by simp [Enter285.pending,Wire] at *;omega
    simp [eraseSites,no]
  refine ⟨phase,?_,?_,?_,?_,?_,?_⟩
  · simpa [eraseSites,Enter285.pending] using sign
  · simpa [eraseSites,Enter285.pending] using mode
  · simpa [eraseSites,Enter285.pending] using side
  · intro pair mem
    rw [loShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (301+(130+j.val)) (by change 301+(130+j.val)<1556;omega),away (786+(130+j.val)) (by change 786+(130+j.val)<1556;omega)]
    exact low ⟨130+j.val,by omega⟩
  · intro pair mem
    rw [hiShape] at mem
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp mem
    dsimp only
    have hj:=j.isLt
    rw [away (434+j.val) (by change 434+j.val<1556;omega),away (919+j.val) (by change 919+j.val<1556;omega)]
    exact high j
  · intro q notN notF notU _ notHi
    by_cases pending:q∈Enter285.pending
    · have range : ∀q∈Enter285.pending,1556≤q ∧ q≤1784 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
      obtain ⟨lo,hi⟩:=range q pending
      simp [eraseSites,pending,carry q lo hi]
    simp only [eraseSites,if_neg pending]
    by_cases external:Exterior 270 528 q
    · exact ext q external
    by_cases residual:leftovers q
    · exact left q residual
    by_cases retired:Leave270Reference.released q
    · exact released q retired
    have hiA (i:Fin 95) : 434+i.val∈sites Enter285.upperPairs := by
      exact (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀i:Fin 95,434+i.val∈sites Enter285.upperPairs) i
    have hiB (i:Fin 95) : 919+i.val∈sites Enter285.upperPairs := by
      exact (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel) : ∀i:Fin 95,919+i.val∈sites Enter285.upperPairs) i
    have outside (start count:Nat) (h:∀i:Fin count,start+i.val∈sites Enter285.upperPairs) : ¬(start≤q ∧ q<start+count) := by
      rintro ⟨a,b⟩
      obtain ⟨i,eq⟩:=indexOfRange q start count a b
      exact notHi (eq ▸ h i)
    have notA:=outside _ _ hiA
    have notB:=outside _ _ hiB
    by_cases a:301≤q ∧ q<434
    · obtain ⟨l,r⟩:=a
      obtain ⟨i,eq⟩:=indexOfRange q 301 133 l r
      exact eq ▸ (low i).1
    by_cases b:786≤q ∧ q<919
    · obtain ⟨l,r⟩:=b
      obtain ⟨i,eq⟩:=indexOfRange q 786 133 l r
      exact eq ▸ (low i).2
    have bounds : 1556≤q ∧ q≤1784 := by
      unfold Exterior at external;unfold leftovers at residual
      unfold Leave270Reference.released at retired
      simp only [Wire] at *
      omega
    rw [carry _ bounds.1 bounds.2]
    apply clear
    simp only [Leave270BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
    simp [Enter285.pending,Wire] at pending
    simp only [Wire] at *
    omega
end ECDSAAdd.Entrant.StairPacket.Leave270AssembleCut
end

/- tail: certified source line 32462. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
structure Numeric (z:SkywalkNat.State):Prop where
  small:min z.u z.v<2^121
  odd:z.v%2=1
  room:Shadow.high 121 15 z+1<2^106
  nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^114
  bound:Leave270TrueMiddle.F z<2^121
  tailBound:Leave270TrueMiddle.F z<2^106

theorem actualNumbers (x p:Nat) (good:WideReference.Bounds x p):
    Numeric (SkywalkNat.step^[270] (SkywalkNat.init x p)):=by
  let z:=SkywalkNat.step^[270] (SkywalkNat.init x p)
  have env:z.u+z.v≤2^241:=W.iter_sum_width x p 270 good.positive good.nonzero good.odd good.cap good.small good.coprime (by decide)
  have it:SkywalkNat.step^[15] z=SkywalkNat.step^[285] (SkywalkNat.init x p):=
    (Function.iterate_add_apply SkywalkNat.step 15 270 _).symm
  have nextEnv:(SkywalkNat.step^[15] z).u+(SkywalkNat.step^[15] z).v≤2^226:=by
    rw [it];exact W.iter_sum_width x p 285 good.positive good.nonzero good.odd good.cap good.small good.coprime (by decide)
  have high:(z.u+z.v)/2^137 ≤ 2^104:=by
    have h:=Nat.div_le_div_right (c:=2^137) env
    exact Nat.le_trans h (by decide)
  have out:((SkywalkNat.step^[15] z).u+(SkywalkNat.step^[15] z).v)/2^122≤2^104:=by
    have h:=Nat.div_le_div_right (c:=2^122) nextEnv
    exact Nat.le_trans h (by decide)
  refine ⟨true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide),
    (SkywalkNat.iter_valid 270 (SkywalkNat.init x p) good.positive good.odd).2.1,?_,?_,?_,?_⟩
  · change (z.u+z.v)/2^137+1<2^106
    omega
  · rw [it];exact true_small x p 285 (lt_trans good.small good.cap) good.cap (by decide)
  · change ((SkywalkNat.step^[15] z).u+(SkywalkNat.step^[15] z).v)/2^122<2^121
    omega
  · change ((SkywalkNat.step^[15] z).u+(SkywalkNat.step^[15] z).v)/2^122<2^106
    omega

def flags (z:SkywalkNat.State) (g0 s0:Bool):Bool×Bool:=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
structure Inputs (s:State) (z:SkywalkNat.State) (g0 s0:Bool):Prop extends Numeric z where
  ready:onRails 13 15 (encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).u (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)).v) s.basis
  fresh:s.basis 1700=false
  scratch:∀q∈1556::1557::1558::fullC,s.basis q=false
  temp:∀p∈longPairs,s.basis p.2=false
  clean:∀q∈carries,s.basis q=false
  padding:∀t:Nat,106≤t→t<121→s.basis (wire t)=false
  bank:regValue ys s.basis=if Shadow.far 121 15 z then Shadow.high 121 15 z else 0
  zero:∀q∈Leave270FrontReady.watched,s.basis q=false
  far:s.basis 1698=decide (Shadow.far 121 15 z)
  side:s.basis 1699=(decide (Shadow.far 121 15 z) && decide (2^121≤z.u))
  record:readCells (shape 13) 0 15 (mappedBasis 13 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
def spare:List Wire:=[1701,1702]++List.range' 1705 8
private def touch:= (1556::1557::1558::fullC) ++ longPairs.map Prod.snd ++ carries ++ ((List.range' 106 15).map wire) ++ Leave270FrontReady.watched
private theorem geometry:∀q∈touch,(1556≤q ∧ q≤1694) ∨ q∈spare:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem assemble (s:State) (z:SkywalkNat.State) (g0 s0:Bool) (numbers:Numeric z)
    (rails:onRails 13 15 (SkywalkTrace.next^[15] (encode g0 s0 (Shadow.reduced 121 15 z).u (Shadow.reduced 121 15 z).v)) s.basis)
    (record:readCells (shape 13) 0 15 (mappedBasis 13 s.basis)=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v))
    (saved:regValue ys s.basis=(if Shadow.far 121 15 z then Shadow.high 121 15 z else 0) ∧
      s.basis 1700=false ∧ s.basis 1698=decide (Shadow.far 121 15 z) ∧ s.basis 1699=decide (Shadow.far 121 15 z ∧ 2^121≤z.u))
    (ex:∀q∈spare,s.basis q=false):Inputs s z g0 s0:=by
  have cl:=Leave270Reference.nativeCarry _ s rails
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
    have hit:t∈List.range' 106 15:=List.mem_range'_1.mpr ⟨lo,hi⟩
    apply all
    have mem:=List.mem_map_of_mem (f:=wire) hit
    simp only [touch,List.mem_append];exact Or.inl (Or.inr mem)
  · intro q h;apply all;simp only [touch,List.mem_append];exact Or.inr h
  · rw [saved.2.2.2]
    by_cases f:Shadow.far 121 15 z <;> simp [f]
end ECDSAAdd.Entrant.StairPacket.Leave270Admission
end

/- tail: certified source line 32537. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000
attribute [local irreducible] Leave270Reference.origin Leave270Reference.endRaw Leave270Reference.reframe

theorem result (x p : Nat) (good:Bounds x p) (raw s:State) (m:List Bool) (g sg:Bool)
    (domain:Domain 270 x p raw)
    (input:InputAt 270 (encode g sg (unsigned 270 x p).u (unsigned 270 x p).v) raw)
    (record:physicalCells 13 s=SkywalkTrace.trace 15 (encode g sg (unsigned 270 x p).u (unsigned 270 x p).v))
    (kept:physicalCells 13 (run leave270 m s)=physicalCells 13 s)
     :
    ∀q,Leave270AssembleCut.leftovers q → (run leave270 m s).basis q=(Leave270Reference.origin raw s).basis q := by
  let out:=run leave270 m s
  let o:=Leave270Reference.origin raw s
  have geo : ∀i:Fin 15,windowNet 13 (ports (shape 13) i.val).a0=286+i.val ∧
      windowNet 13 (ports (shape 13) i.val).history=Leave270Hit.swaps i.val := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have agree (i:Fin 15) : out.basis (286+i.val)=o.basis (286+i.val) ∧
      out.basis (Leave270Hit.swaps i.val)=o.basis (Leave270Hit.swaps i.val) := by
    have old:=Leave270Reference.recorded_equal x p good raw s domain g sg input record i
    have now:=congrArg (fun a=>StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (shape 13) 0 15 (mappedBasis 13 out.basis)) i.val =
      StairArchiveRaw.read (readCells (shape 13) 0 15 (mappedBasis 13 s.basis)) i.val at now
    rw [read_cells _ _ _ _ _ i.isLt,read_cells _ _ _ _ _ i.isLt,Nat.zero_add] at now
    have eq:=now.trans old
    change (out.basis (windowNet 13 (ports (shape 13) i.val).a0),out.basis (windowNet 13 (ports (shape 13) i.val).history)) =
      (o.basis (windowNet 13 (ports (shape 13) i.val).a0),o.basis (windowNet 13 (ports (shape 13) i.val).history)) at eq
    rw [(geo i).1,(geo i).2] at eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  have previous : out.basis 285=o.basis 285 := by
    rw [show o.basis 285=s.basis 285 from Leave270Reference.inside raw s 285 (by decide +kernel)]
    have stable : LeaveSelector.parityAt 285 leave270=some false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    simpa [out] using polarity _ _ _ stable s m
  let gs:=(List.finRange 15).map (fun i=>286+i.val)
  let ss:=(List.finRange 15).map (fun i=>Leave270Hit.swaps i.val)
  intro q residual
  by_cases prev:q=285
  · subst q;exact previous
  by_cases gg:q∈gs
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp gg;exact (agree i).1
  by_cases sw:q∈ss
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp sw;exact (agree i).2
  by_cases old:q∈Leave270Reference.historySites
  · have stable : ∀q∈Leave270Reference.historySites,LeaveSelector.parityAt q leave270=some false := by decide +kernel
    have intact:out.basis q=s.basis q := by simpa only [Bool.xor_false] using polarity _ _ _ (stable q old) s m
    exact intact.trans (Leave270Reference.inside raw s q old).symm
  have census : ∀a:Fin 1813,Leave270AssembleCut.leftovers a.val → a.val≠285 → a.val∉gs → a.val∉ss → a.val∉Leave270Reference.historySites →
      False := by
    unfold Leave270AssembleCut.leftovers; dsimp only [gs,ss];rw [Leave270Reference.historySites_shape];(open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have bound:q<1813:=by unfold Leave270AssembleCut.leftovers at residual;simp only [Wire] at *;omega
  exact False.elim (census ⟨q,bound⟩ residual prev gg sw old)
end ECDSAAdd.Entrant.StairPacket.Leave270FrameHistory
end

/- roundtrip: certified source line 32808. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion270 PortalValues Leave270Barrel Leave270High HighBankBarrel
open Leave270Front LeaveSelector Leave270Selector Leave270OutputPorts LeaveReadoutFrame IntegerHigh Leave270Close
open Leave270Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
theorem Inputs.roundtrip {s:State} {z:SkywalkNat.State} {g0 s0:Bool}
    (h:Inputs s z g0 s0) (m n:List Bool) :
    run leaveInv270 n (run leave270 m s)=s := by
  let u:=flags z g0 s0
  let xs:=SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have par:=Leave270RecordedParity.result s z g0 s0 h.small h.odd h.record
  have mode : actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave270RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have ph (o:List Bool) : (run leave270 o s).phase=s.phase:=by
    exact (Leave270Whole.result s o z u.1 u.2 h.small h.ready h.fresh h.scratch h.temp
      h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall h.bound
      xs (SkywalkTrace.trace_length _ _)
      (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd)
      (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side).1
  exact Leave270Roundtrip.result s m n z u.1 u.2 h.small h.ready h.fresh h.scratch
    h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 h.nextSmall
    h.bound ph
end ECDSAAdd.Entrant.StairPacket.Leave270Admission
end

/- tail: certified source line 32831. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step Leave270Reference.origin Leave270Reference.endRaw Leave270Reference.reframe

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

theorem result (x p : Nat) (good:Bounds x p) (raw s : State) (m:List Bool) (g0 s0:Bool)
    (dom:Domain 270 x p raw)
    (input:InputAt 270 (encode g0 s0 (unsigned 270 x p).u (unsigned 270 x p).v) raw)
    (h:Leave270Admission.Inputs s (unsigned 270 x p) g0 s0)
    (phase:s.phase=(Leave270Reference.origin raw s).phase)
    (ext:∀q,Exterior 270 528 q → s.basis q=(Leave270Reference.origin raw s).basis q)
    (upper:∀q:Nat,441≤q → q≤528 → s.basis q=false)
    (quiet:∀q∈Leave270CoreCheckpoint.rawSites,s.basis q=false)
    (released:∀q,Leave270Reference.releasedInput q → s.basis q=false)
     :
    let z:=unsigned 270 x p
    let flags:=Leave270Admission.flags z g0 s0
    let a:=unsigned 285 x p
    let out:=run leave270 m s
    PackedCut Enter285.lowerPairs Enter285.upperPairs 300 1693 1691 1692 (PortalValues.negative flags.2 a.u)
      (decide (Shadow.far 114 15 a)) (decide (Shadow.far 114 15 a ∧ 2^114≤a.u))
      (pullState (OB5.sig 284) (Leave270Reference.endRaw raw s)) (eraseSites Enter285.pending out) := by
  let z:=unsigned 270 x p
  let flags:=Leave270Admission.flags z g0 s0
  let a:=SkywalkNat.step^[15] z
  let xs:=SkywalkTrace.trace 15 (encode g0 s0 z.u z.v)
  have endpointState : a=unsigned 285 x p := (Function.iterate_add_apply SkywalkNat.step 15 270 _).symm
  have signed:=Leave270Reference.advance_signed x p good raw s dom g0 s0 input h.small
  have nextInput : SkywalkIntegerInput Leave270WideWords.L (encode flags.1 flags.2 a.u a.v).a
      (encode flags.1 flags.2 a.u a.v).b flags.1 (Leave270Reference.endRaw raw s).basis := by
    rw [endpointState]
    change SkywalkIntegerInput _ (encode flags.1 flags.2 _ _).a (encode flags.1 flags.2 _ _).b (encode flags.1 flags.2 _ _).g _ at signed
    simpa only [flagEq] using signed
  have par:=Leave270RecordedParity.result s z g0 s0 h.small h.odd h.record
  have md : actualMode 121 z=farMode (s.basis 1698) (s.basis 1699) z.u:=by
    rw [h.far,h.side];exact LeaveTraceHistory.flags _ _
  have ev:=Leave270RecordedEvents.result s z g0 s0 h.small h.odd h.record
  have bits:=Leave270EndWords.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have whole:=Leave270Whole.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side
  have kept:=Leave270PreservedRecords.result s m bits.2.2.2.1
  have left:=Leave270FrameHistory.result x p good raw s m g0 s0 dom input h.record kept
  have rails:=Leave270BoundaryRails.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side upper (Leave270Reference.endRaw raw s) nextInput
  have clear:=Leave270BoundaryClean.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par md ev.2 h.nextSmall h.bound xs (SkywalkTrace.trace_length _ _) (LeaveTraceHistory.certifiedChain _ _ _ _ h.small h.odd) (LeaveTraceHistory.firstSwap _ _ _ _ h.small h.odd) ev.1 h.far h.side quiet h.tailBound
  dsimp only
  rw [←endpointState,Leave270Reference.endpoint]
  rw [Leave270Reference.endpoint] at rails
  apply Leave270AssembleCut.result _ _ _ _ _ (whole.1.trans phase) bits.2.2.1 bits.1
  · exact bits.2.1.trans (both _ _)
  · exact rails.1
  · exact rails.2
  · exact fun q hq=>(Leave270Reference.exterior s m q hq).trans (ext q hq)
  · exact left
  · exact clear
  · intro q hq
    have reference:=Leave270Reference.released_origin x p good raw s dom q hq
    by_cases old:Leave270Reference.releasedInput q
    · exact ((Leave270Reference.released_kept q old s m).trans (released q old)).trans reference.symm
    · have band:1014≤q ∧ q≤1028:=by
        unfold Leave270Reference.released Leave270Reference.releasedInput at *
        simp only [Wire] at *
        omega
      apply (clear q ?_).trans reference.symm
      simp only [Leave270BoundaryClean.zeros,List.mem_append,List.mem_range'_1]
      simp only [Wire] at *
      omega
  · exact Leave270Reference.carry x p good raw s dom
end ECDSAAdd.Entrant.StairPacket.Leave270CertifiedCut
end

/- tail: certified source line 33127. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Leave270ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
def rawPortsList : List Wire :=
  (List.finRange 20).map (fun i=>nativeRawPort 13 i.val) ++ [1694,1695,1696] ++ List.range' 1556 134
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i.val 0
theorem raw_first20 : ∀i:Fin 20,rawPorts ⟨i.val,by omega⟩=nativeRawPort 13 i.val := by decide +kernel
theorem raw_status : rawPorts 20=1694 ∧ rawPorts 21=1695 ∧ rawPorts 22=1696 := by decide +kernel
theorem raw_scratch (i : Fin 157) (lo : (23 : Nat) ≤ i.val) : rawPorts i=1556+(i.val-23) := by
  revert i
  decide +kernel

theorem result (s:State) (m:List Bool) (z:SkywalkNat.State) (g sg:Bool)
    (h:Leave270Admission.Inputs s z g sg) :
    let out:=run leave270 m s
    PastFacts 13 rawPorts 121 z g sg (HighBankSum.cross (Leave270TrueMiddle.d z)) out := by
  let flags:=Leave270Admission.flags z g sg
  have all:=Leave270ActualHistory.result s m z flags.1 flags.2 h.small h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero h.nextSmall h.bound h.far h.side g sg h.record
  exact ⟨all.1,
    (congrArg (run leave270 m s).basis raw_status.1).trans all.2.1,
    (congrArg (run leave270 m s).basis raw_status.2.1).trans all.2.2.1,
    (congrArg (run leave270 m s).basis raw_status.2.2).trans all.2.2.2⟩
end ECDSAAdd.Entrant.StairPacket.Leave270ArchiveCut
end


namespace ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction

def sourceIdx : Fin 23 := ⟨13,by decide⟩
abbrev rawPorts := Terminal285.rawPorts
abbrev codePorts := Terminal285.codePorts
def program (d : Bool) := renameProgram (OB5.sig 285) (Rolling1588.packAtTick d 275)
def reverse (d : Bool) := renameProgram (OB5.sig 285) (Rolling1588.unpackAtTick d 275)
def history (q : Fin 10) := OB5.sig 285 (History5.historyMap base 270 q)

structure Transition (inverse : Program) (s tick : State) : Prop where
  phase : tick.phase=s.phase
  keptFive : ∀i,tick.basis (history i)=s.basis (history i)
  keptBank : ∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=
    s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)
  scratch : ∀i:Fin 157,23 ≤ i.val → tick.basis (rawPorts i)=false
  undo : ∀n,run inverse n tick=s

end ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative


namespace ECDSAAdd.Entrant.StairPacket.Extension270.EndTick285
attribute [local irreducible] ECDSAAdd.run
open EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 285
def P:=TickRanges.tick base 285
def Q:=W.ReverseCarry.compactReceiverTick base 285
def physP:=renameProgram (OB5.sig 285) P
def physQ:=renameProgram (OB5.sig 285) Q
theorem supports : wires P⊆L.wires.toFinset ∧ wires Q⊆L.wires.toFinset :=
  ⟨(TickRanges.tick_support base 285 (by decide) base_pool_nodup).trans
    (W.repairedTick_support base 285 (by decide) base_pool_nodup),
    W.ReverseCarry.compactReceiverTick_support base 285 (by decide) base_pool_nodup⟩
theorem physical_free (R:Program) (sub:wires R⊆L.wires.toFinset) (q:Wire)
    (off:OB5.sig 285 q∉L.wires) : q∉wires (renameProgram (OB5.sig 285) R) := by
  rw [JointForward1588.wires_rename_image]
  intro h
  obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
  rw [OB5.sig_invol 285 (by decide)] at off
  exact off (List.mem_toFinset.mp (sub mem))
theorem spared : ∀q∈ParkEndpoint285.dst,OB5.sig 285 q∉L.wires := by decide +kernel
theorem stashP : ∀q∈ParkEndpoint285.dst,q∉wires physP := fun q hit=>physical_free P supports.1 q (spared q hit)
theorem stashQ : ∀q∈ParkEndpoint285.dst,q∉wires physQ := fun q hit=>physical_free Q supports.2 q (spared q hit)
open EndTick
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
def canonical:= W.compactSkywalkTick base 285
def Reads (a b:State) := ∀q∈L.wires.toFinset,a.basis q=b.basis q
theorem apply_old (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 285 original.basis) (a b:List Bool) :
    run P a actual=run canonical b actual:=by
  obtain ⟨w,sw,agree⟩:=Rolling1588.Integer.old_stage_local base d base_pool_nodup x p 285 (by decide) original stage
  have old:=TickRanges.tick_eq5 x hx0 hx 285 (by decide) w a sw
  have same:=Stack5.local_replace P (W.repairedTick base 285) L.wires.toFinset supports.1
    (W.repairedTick_support base 285 (by decide) base_pool_nodup) original w a a agree old
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have reference:=Rolling1588.Integer.repaired_eq base d base_pool_nodup x p 285 hp0 hx0 hpo hp gap hx cop (by decide) original a b stage
  exact Stack5.local_replace P canonical L.wires.toFinset supports.1
    (W.compactSkywalkTick_support base 285 (by decide) base_pool_nodup) actual original a b read (same.trans reference)

theorem compact_undo (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 285 original.basis) (a b:List Bool) :
    run Q b (run canonical a actual)=actual:=by
  obtain ⟨ref,stock,agree⟩:=local_reference 285 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  exact undo_on_domain base base_pool_nodup x p 285 (by decide) hp0 hx0 hpo hp gap hx cop actual ref a b stock
    (fun q h=>(read _ (List.mem_toFinset.mpr h)).trans (agree _ (List.mem_toFinset.mpr h)))


open EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem physical (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State)
    (read:Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 285 original.basis)
    (hist:raw.basis (base (1028+285))=false) (swapSlot:raw.basis (base (2053-285))=false)
    (m:List Bool) :
    let start:=ParkEndpoint285.stash tags (pullState (OB5.sig 284) raw)
    let out:=run physP m start
    out=ParkEndpoint285.stash tags (pullState (OB5.sig 285) (run canonical [] raw)) ∧
      ∀t,run physQ t out=start := by
  have pre:pullState (OB5.sig 284) raw=pullState (OB5.sig 285) raw:=
    OB5.pull_step 285 (by decide) raw hist (fun _=>swapSlot)
  have result:run physP m (ParkEndpoint285.stash tags (pullState (OB5.sig 284) raw))=
      ParkEndpoint285.stash tags (pullState (OB5.sig 285) (run canonical [] raw)):=by
    rw [ParkEndpoint285.commutes _ stashP,pre,physP,OB5.run_rename _ (by decide),apply_old d x hx0 hx raw original read stage m []]
  refine ⟨result,?_⟩
  intro t
  rw [result,ParkEndpoint285.commutes _ stashQ,physQ,OB5.run_rename _ (by decide),compact_undo d x hx0 hx raw original read stage,←pre]

open EndTick
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
def readOnly (q:Wire) := OB5.sig 285 q∉L.wires ∨ q=300
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
theorem observes (q:Wire) (h:readOnly q) (s:State) (m:List Bool) (prev:(run physP m s).basis 300=s.basis 300) : (run physP m s).basis q=s.basis q := by
  rcases h with h|rfl
  · exact run_preserves_outside _ _ _ _ (physical_free P supports.1 _ h)
  · exact prev
theorem oldPrefix : ∀i,readOnly (TerminalNative.history i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.Extension270.EndTick285.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem oldBank : ∀i:Fin 23,readOnly (Terminal285.rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by ((try unfold ECDSAAdd.Entrant.StairPacket.Extension270.EndTick285.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
open EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3500000
set_option maxRecDepth 18000
set_option exponentiation.threshold 1024

theorem after_reference (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 285 original.basis) :
    ∃ref:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 285 ref.basis ∧
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 286 (run canonical [] ref).basis ∧
      Reads raw ref ∧ Reads (run canonical [] raw) (run canonical [] ref) := by
  obtain ⟨ref,hs,agree⟩:=local_reference 285 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have r:Reads raw ref:=fun q h=>(read q h).trans (agree q h)
  exact ⟨ref,hs,(W.compactSkywalkStageStep base base_pool_nodup x p 285 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).2,r,
    canonical_reads 285 (by decide) ref raw r []⟩

open EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
theorem scratch_lanes : ∀k:Fin 134,1556+k.val∈L.carry ∧ 1556+k.val∈wireBlock base 1540 257 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem after_cells (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 285 original.basis) :
    (run canonical [] raw).basis 300=raw.basis 300 ∧
    ∀k:Fin 134,(run canonical [] raw).basis (1556+k.val)=false := by
  obtain ⟨ref,old,next,pre,post⟩:=after_reference d x hx0 hx raw original read stage
  have prev:300∈L.wires.toFinset:=previous_member 285
  have a:=pastG 285 284 (by decide) (by decide) _ _ old
  have b:=pastG 286 284 (by decide) (by decide) _ _ next
  exact ⟨(post _ prev).trans (b.trans (a.symm.trans (pre _ prev).symm)),
    fun k=>(post _ (carry_member 285 _ (scratch_lanes k).1)).trans (full_carry 286 (by decide) _ _ next _ (scratch_lanes k).2)⟩

open EndTick
open Arithmetic MappedCompressed Secp256k1 Terminal285 ParkEndpoint285
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
theorem no_phase (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 285 original.basis) : (run canonical [] raw).phase=raw.phase := by
  obtain ⟨ref,hs,ag⟩:=local_reference 285 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have step:=(W.compactSkywalkStageStep base base_pool_nodup x p 285 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).1
  have inc:=(run_local_increment canonical raw ref [] (fun q h=>by
    have mem:=(W.compactSkywalkTick_support base 285 (by decide) base_pool_nodup) h
    exact (read q mem).trans (ag q mem))).1
  change (run canonical [] ref).phase=ref.phase at step
  rw [step,Bool.xor_self] at inc
  cases h:(run canonical [] raw).phase <;> cases k:raw.phase <;> simp_all

theorem scratch_table : ∀i:Fin 157,23≤ i.val →
    rawPorts i∉dst ∧ OB5.sig 285 (rawPorts i)=1556+(i.val-23) ∧ ∀v:Fin 10,rawPorts i≠TerminalNative.history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem coordinate (s raw:State) : (stash s (pullState (OB5.sig 285) raw)).basis 300=raw.basis 300 ∧
    (stash s (pullState (OB5.sig 284) raw)).basis 300=raw.basis 300 := ⟨rfl,rfl⟩

theorem stash_slots (raw after tags:State) (phase:after.phase=raw.phase) (same:after.basis 300=raw.basis 300)
    (zero:∀k:Fin 134,after.basis (1556+k.val)=false) :
    let start:=stash tags (pullState (OB5.sig 284) raw)
    let out:=stash tags (pullState (OB5.sig 285) after)
    out.phase=start.phase ∧ out.basis 300=start.basis 300 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  refine ⟨phase,(coordinate _ _).1.trans (same.trans (coordinate _ _).2.symm),?_⟩
  intro i hi
  have ⟨off,eq,_⟩:=scratch_table i hi
  simp only [stash,if_neg off]
  exact (congrArg after.basis eq).trans (zero ⟨i.val-23,by have h:=i.isLt;omega⟩)

theorem exposed (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 285 original.basis)
    (hist:raw.basis (base (1028+285))=false) (swapSlot:raw.basis (base (2053-285))=false) (m:List Bool) :
    let start:=stash tags (pullState (OB5.sig 284) raw)
    let out:=run physP m start
    out.phase=start.phase ∧ out.basis 300=start.basis 300 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  have out:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).1
  have bits:=after_cells d x hx0 hx raw original read stage
  dsimp only
  rw [out]
  exact stash_slots raw (run canonical [] raw) tags (no_phase d x hx0 hx raw original read stage) bits.1 bits.2


open Arithmetic MappedCompressed Secp256k1
theorem observe_tick (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 285 original.basis)
    (hist:raw.basis (base (1028+285))=false) (swapSlot:raw.basis (base (2053-285))=false) (m:List Bool) :
    let start:=ParkEndpoint285.stash tags (pullState (OB5.sig 284) raw)
    TerminalNative.Transition physQ start (run physP m start) := by
  let s:=ParkEndpoint285.stash tags (pullState (OB5.sig 284) raw)
  have h:=exposed d x hx0 hx raw original tags read stage hist swapSlot m
  have u:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).2
  exact ⟨h.1,fun i=>observes _ (oldPrefix i) s m h.2.1,
    fun i=>observes _ (oldBank i) s m h.2.1,h.2.2,u⟩

end ECDSAAdd.Entrant.StairPacket.Extension270.EndTick285



namespace ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify
open StairArchiveRaw StairArchiveTrace SkywalkRails
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run routed
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
theorem pack_support (d:Bool) : wires (program d) ⊆ ((List.finRange 10).map history).toFinset := by cases d <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem outside (d:Bool) (q:Wire) (no:∀v:Fin 10,q≠history v) (m:List Bool) (s:State) :
    (run (program d) m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro mem
  obtain ⟨v,_,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp (pack_support d mem))
  exact no v eq.symm
theorem bank_out : ∀q:Fin 23,∀v:Fin 10,rawPorts ⟨q,Nat.lt_trans q.isLt (by decide : 23<157)⟩≠history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem scratch_out : ∀i:Fin 157,23 ≤ i.val → ∀v:Fin 10,rawPorts i≠history v := by decide +kernel
theorem archive_ready (d:Bool) (start tick:State) (m:List Bool) (past:SkywalkNat.State) (g sign cross:Bool)
    (odd:past.v%2=1) (small:min past.u past.v<2^121) (prior:PastFacts sourceIdx rawPorts 121 past g sign cross start)
    (keptFive:∀i,tick.basis (history i)=start.basis (history i))
    (bank:∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩))
    (scratch:∀i:Fin 157,23 ≤ i.val → tick.basis (rawPorts i)=false) :
    MeasuredCodec5.legalAt history tick.basis ∧ ∃row<63145,ArchivePortAction.Frame rawPorts raw row (run (program d) m tick) := by
  let cells:=physicalCells sourceIdx start
  let f:=decide (Shadow.far 121 15 past)
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
  have fresh (i:Fin 157) (hi:23 ≤ i.val) : out.basis (rawPorts i)=false :=
    (outside d _ (scratch_out i hi) m tick).trans (scratch i hi)
  obtain ⟨row,limit,matchRow⟩:=interrupted_row 121 past small odd g sign cross cells
    (prior.records.trans (true_records _ _ small odd _ _).symm)
  exact ⟨legal_prefix _ _ legal keptFive,row,limit,starting_frame rawPorts out row data matchRow hw fresh⟩


theorem finish_generic (p q : Program) (d : Bool) (s : State) (m : List Bool)
    (step : Transition q s (run p m s)) (past : SkywalkNat.State) (G S cross : Bool)
    (odd : past.v%2=1) (small : min past.u past.v<2^121)
    (prior : PastFacts sourceIdx rawPorts 121 past G S cross s) :
    let out := run (p ++ (program d ++ Terminal285.load d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (Terminal285.restore d ++ (reverse d ++ q)) n out=s := by
  let tick := run p m s
  let e := m.drop (measurementCount p)
  let pre := run (program d) e tick
  let f := e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩ := archive_ready d s tick e past G S cross odd small prior
    step.keptFive step.keptBank step.scratch
  have truth := row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i => (outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc := source_law d tick e legal
  have act := Terminal285.load_run d row limit pre f frame
  exact NativePack270.sequence_law p (program d) (Terminal285.load d) (Terminal285.restore d)
    (reverse d) q s m (fun out => ∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Terminal285.load d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n => Terminal285.roundtrip d row limit pre f n frame)

end ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative

namespace ECDSAAdd.Entrant.StairPacket.Extension270.ParkEndpoint285
open Arithmetic MappedCompressed IntegerPacket RailPair Portal285 TerminalNative
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def ordinary (q : Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1693 ∧ q≠1691 ∧ q≠1692 ∧ q∉sites hiPairs
instance (q : Wire) : Decidable (ordinary q) := by unfold ordinary;infer_instance

theorem past_sites : ∀r:Fin 15,
    ordinary (windowNet sourceIdx (ports (shape sourceIdx) r).a0) ∧
    ordinary (windowNet sourceIdx (ports (shape sourceIdx) r).history) := by
  unfold ordinary
  decide +kernel

theorem earlier (raw s : State) (n f u : Bool)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 n f u
      (pullState (OB5.sig 284) raw) (eraseSites src s)) (q : Wire) (clean : ordinary q) :
    (stash s (pullState (OB5.sig 284) raw)).basis q=s.basis q := by
  obtain ⟨hs,hd,hn,hf,hu,hh⟩ := clean
  have eq := cut.unchanged q hn hf hu hh
  simpa [stash,eraseSites,hs,hd] using eq.symm

theorem past_cells (raw s : State) (n f u : Bool)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 n f u
      (pullState (OB5.sig 284) raw) (eraseSites src s)) :
    physicalCells sourceIdx (stash s (pullState (OB5.sig 284) raw))=physicalCells sourceIdx s := by
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (earlier raw s n f u cut _ (past_sites r).1)
    (earlier raw s n f u cut _ (past_sites r).2)

theorem tag_address (s other : State) :
    (stash s other).basis (rawPorts 20)=s.basis 1694 ∧
    (stash s other).basis (rawPorts 21)=s.basis 1695 ∧
    (stash s other).basis (rawPorts 22)=s.basis 1696 := ⟨rfl,rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Extension270.ParkEndpoint285

namespace ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction
open ParkEndpoint285 Portal285 StairArchiveTrace SkywalkRails
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run

def endSlice (d : Bool) := EndTick285.physP ++ (program d ++ Terminal285.load d)
def endUndo (d : Bool) := Terminal285.restore d ++ (reverse d ++ EndTick285.physQ)
def lastWindow (d : Bool) := park285 ++ (portalInv285 ++ endSlice d)
def lastUnwind (d : Bool) := endUndo d ++ (portal285 ++ parkInv285)

theorem finish_slice (d : Bool) (s : State) (m : List Bool)
    (step : Transition EndTick285.physQ s (run EndTick285.physP m s))
    (past : SkywalkNat.State) (G S cross : Bool) (odd : past.v%2=1) (small : min past.u past.v<2^121)
    (prior : PastFacts sourceIdx rawPorts 121 past G S cross s) :
    let out := run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  finish_generic EndTick285.physP EndTick285.physQ d s m step past G S cross odd small prior

theorem after_park (raw s : State) (n f u : Bool)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 n f u
      (pullState (OB5.sig 284) raw) (eraseSites src s))
    (past : SkywalkNat.State) (G S cross : Bool)
    (records : physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode G S past.u past.v))
    (mode : s.basis 1694=decide (Shadow.far 121 15 past))
    (orientation : s.basis 1695=(decide (Shadow.far 121 15 past) &&
      afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped : s.basis 1696=(decide (Shadow.far 121 15 past) && cross)) :
    PastFacts sourceIdx rawPorts 121 past G S cross (stash s (pullState (OB5.sig 284) raw)) := by
  have cells := past_cells raw s n f u cut
  have tag := tag_address s (pullState (OB5.sig 284) raw)
  refine ⟨cells.trans records,tag.1.trans mode,?_,tag.2.2.trans flipped⟩
  rw [cells]
  exact tag.2.1.trans orientation

theorem empty_from_cut (raw s : State) (n f u : Bool)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 n f u
      (pullState (OB5.sig 284) raw) (eraseSites src s))
    (source : ∀q∈dst,(pullState (OB5.sig 284) raw).basis q=false) : ∀q∈dst,s.basis q=false := by
  have regular : ∀q∈dst,q∉src ∧ q≠1693 ∧ q≠1691 ∧ q≠1692 ∧ q∉RailPair.sites hiPairs := by decide +kernel
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩ := regular q member
  have eq := cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source q member)

theorem last_window (d : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (raw original s : State) (m : List Bool) (read : EndTick285.Reads raw original)
    (stage : Rolling1588.Integer.Stage base d x p 285 original.basis)
    (hist : raw.basis (base (1028+285))=false) (swapSlot : raw.basis (base (2053-285))=false)
    (z : SkywalkNat.State) (small : min z.u z.v<2^114) (G S : Bool)
    (input : SkywalkIntegerInput EndTick285.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 (PortalValues.negative S z.u)
      (decide (3*2^130 ≤ z.u+z.v)) (decide (3*2^130 ≤ z.u+z.v ∧ 2^114 ≤ z.u))
      (pullState (OB5.sig 284) raw) (eraseSites src s))
    (empty : ∀q∈dst,s.basis q=false) (past : SkywalkNat.State) (pg ps cross : Bool)
    (odd : past.v%2=1) (pm : min past.u past.v<2^121)
    (records : physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode : s.basis 1694=decide (Shadow.far 121 15 past))
    (angle : s.basis 1695=(decide (Shadow.far 121 15 past) &&
      afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped : s.basis 1696=(decide (Shadow.far 121 15 past) && cross)) :
    let out := run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n := m.drop (measurementCount park285)
  let one := run portalInv285 n (run park285 m s)
  let tape := n.drop (measurementCount portalInv285)
  have restored := parked_release z small raw s m n G S input cut empty
  have facts := after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick := EndTick285.observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne : one=stash s (pullState (OB5.sig 284) raw) := restored.1
  have A : PastFacts sourceIdx rawPorts 121 past pg ps cross one := by rw [eqOne];exact facts
  have B : Transition EndTick285.physQ one (run EndTick285.physP tape one) := by rw [eqOne];exact tick
  have body := finish_slice d one tape B past pg ps cross odd pm A
  have phase : one.phase=s.phase := (congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _

theorem from_domain (d : Bool) (x : Nat) (good : WideReference.Bounds x p)
    (raw s : State) (m : List Bool) (domain : WideReference.Domain 285 x p raw)
    (z : SkywalkNat.State) (small : min z.u z.v<2^114) (G S : Bool)
    (input : SkywalkIntegerInput EndTick285.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut : PackedCut loPairs hiPairs 300 1693 1691 1692 (PortalValues.negative S z.u)
      (decide (3*2^130 ≤ z.u+z.v)) (decide (3*2^130 ≤ z.u+z.v ∧ 2^114 ≤ z.u))
      (pullState (OB5.sig 284) raw) (eraseSites src s))
    (past : SkywalkNat.State) (pg ps cross : Bool) (odd : past.v%2=1) (pm : min past.u past.v<2^121)
    (records : physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode : s.basis 1694=decide (Shadow.far 121 15 past))
    (angle : s.basis 1695=(decide (Shadow.far 121 15 past) &&
      afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped : s.basis 1696=(decide (Shadow.far 121 15 past) && cross)) :
    let out := run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩ := Leave270Reference.terminal285 d x p good raw domain
  exact last_window d x good.nonzero good.small raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut raw s _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped

theorem terminal_eq (d : Bool) : terminal285 d=lastWindow d := by
  simp only [terminal285,lastWindow,endSlice,EndTick285.physP,EndTick285.P,program,List.append_assoc]

theorem unterminal_eq (d : Bool) : unterminal285 d=lastUnwind d := by
  simp only [unterminal285,lastUnwind,endUndo,EndTick285.physQ,EndTick285.Q,reverse,List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative


namespace ECDSAAdd.Entrant.StairPacket.Extension270
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails
open StockWindowTicket ArchivePortAction
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

/-- The existing three-block theorem stops before its old terminal portal. -/
theorem head45_shape (d : Bool) : head45 d =
    (NativePack225.firstWindow d ++ Partial.leave225) ++
      ((NativePack240.nextWindow d ++ Partial.leave240) ++
       (NativePack255.nextWindow d ++ Partial.leave255)) := by
  simp only [head45,NativePack225.firstWindow,NativePack240.nextWindow,NativePack255.nextWindow,
    NativePack225.window,NativePack240.window,NativePack255.window,body,
    NativePack225.program,NativePack240.withArchive,NativePack240.program,
    NativePack255.withArchive,NativePack255.program,NativePack225.idx,NativePack240.idx,
    NativePack255.idx,List.append_assoc]

theorem back45_shape (d : Bool) : back45 d =
    (Partial.leave255Inv ++ NativePack255.nextUnwind d) ++
      ((Partial.leave240Inv ++ NativePack240.nextUnwind d) ++
       (Partial.leave225Inv ++ NativePack225.firstUnwind d)) := by
  simp only [back45,NativePack225.firstUnwind,NativePack240.nextUnwind,NativePack255.nextUnwind,
    NativePack225.unwind,NativePack240.unwind,NativePack255.unwind,unbody,
    NativePack225.reverse,NativePack240.fromArchive,NativePack240.reverse,
    NativePack255.fromArchive,NativePack255.reverse,NativePack225.idx,NativePack240.idx,
    NativePack255.idx,List.append_assoc]

theorem head45_checked (d : Bool) (x p : Nat) (good : Bounds x p) :
    Checked (head45 d) (back45 d) (Before d x p) (Ready270 d x p) := by
  rw [head45_shape,back45_shape]
  simpa only [List.append_assoc] using
    composition (step225 d x p good) (composition (step240 d x p good) (step255 d x p good))

/-- The old Ready270 record already carries the three flags needed by the
internal codec; the old terminal park is not part of this conversion. -/
theorem past_at270 (d : Bool) (x p : Nat) (raw s : State) (g sg pg ps : Bool)
    (h : At270 d x p raw s g sg pg ps) :
    PastFacts 12 Internal270.rawPorts 129 (unsigned 255 x p) pg ps
      (HighBankSum.cross (Leave255TrueMiddle.d (unsigned 255 x p))) s := by
  constructor
  · exact h.records
  · change s.basis 1701=decide (Shadow.far 129 15 (unsigned 255 x p))
    exact h.mode
  · change s.basis 1702=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 255 x p).v<(unsigned 255 x p).u))
        ((physicalCells 12 s).take 5))
    exact h.side
  · change s.basis 1703=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      HighBankSum.cross (Leave255TrueMiddle.d (unsigned 255 x p)))
    exact h.cross

def lower285 := (List.range' 431 3).zip (List.range' 916 3)
def upper285 := (List.range' 434 95).zip (List.range' 919 95)
def pending285 : List Wire := [1694,1695,1696]

def digit270 (z : SkywalkNat.State) :=
  HighBankSum.total (SkywalkNat.step^[15] (Shadow.reduced 121 15 z)) / 2^122 /
    2^(if 2^121 ≤ z.u then 0 else IntegerHigh.wait 15 z.u)
def cross270 (z : SkywalkNat.State) := HighBankSum.cross (digit270 z)

/-- The fourth block has three old code banks and one new raw bank. -/
structure At285 (d : Bool) (x p : Nat) (raw s : State) (g sg pg ps : Bool) : Prop where
  domain : Domain 285 x p raw
  input : InputAt 285 (signedAt 285 x p g sg) raw
  cut : PackedCut lower285 upper285 300 1693 1691 1692 (flagNeg 285 x p sg)
    (decide (farAt 114 285 x p)) (decide (farAt 114 285 x p ∧ 2^114 ≤ (unsigned 285 x p).u))
    (pullState (OB5.sig 284) raw) (eraseSites pending285 s)
  records : physicalCells 13 s=SkywalkTrace.trace 15 (signedAt 270 x p pg ps)
  mode : s.basis 1694=decide (farAt 121 270 x p)
  side : s.basis 1695=(decide (farAt 121 270 x p) &&
    StairArchiveTrace.afterFlags (decide ((unsigned 270 x p).v<(unsigned 270 x p).u))
      ((physicalCells 13 s).take 5))
  crossed : s.basis 1696=(decide (farAt 121 270 x p) &&
    cross270 (unsigned 270 x p))
  pastCanonical : signedAt 270 x p pg ps=WideReference.canonical 270 x p
  saved225 : Saved 225 x p ArchiveBoundary240.codePorts d s
  saved240 : Saved 240 x p ArchiveBoundary255.codePorts d s
  saved255 : Saved 255 x p Internal270.codePorts d s

def Ready285 (d : Bool) (x p : Nat) (s : State) := ∃raw g sg pg ps,At285 d x p raw s g sg pg ps

def Final4 (d : Bool) (x p : Nat) (s : State) :=
  Saved 225 x p ArchiveBoundary240.codePorts d s ∧
  Saved 240 x p ArchiveBoundary255.codePorts d s ∧
  Saved 255 x p Internal270.codePorts d s ∧
  Saved 270 x p Terminal285.codePorts d s

/-- Composition is unconditional once the two new local contracts are supplied.
The local proofs must establish all fields of Ready285, including old banks. -/
theorem checked (d : Bool) (x p : Nat) (good : Bounds x p)
    (blockLaw : Checked (block270 d) (unblock270 d) (Ready270 d x p) (Ready285 d x p))
    (terminalLaw : Checked (terminal285 d) (unterminal285 d) (Ready285 d x p) (Final4 d x p)) :
    Checked (forward60plus1 d) (reverse60plus1 d) (Before d x p) (Final4 d x p) := by
  have h := composition (head45_checked d x p good) (composition blockLaw terminalLaw)
  simpa only [forward60plus1,reverse60plus1,List.append_assoc] using h

theorem result (d : Bool) (x p : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 225 raw.basis)
    (blockLaw : Checked (block270 d) (unblock270 d) (Ready270 d x p) (Ready285 d x p))
    (terminalLaw : Checked (terminal285 d) (unterminal285 d) (Ready285 d x p) (Final4 d x p)) :
    let start := pullState (OB5.sig 224) raw
    let out := run (forward60plus1 d) m start
    out.phase=raw.phase ∧ Final4 d x p out ∧ ∀n,run (reverse60plus1 d) n out=start := by
  exact checked d x p good blockLaw terminalLaw _ m ⟨raw,stage,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Extension270


namespace ECDSAAdd.Entrant.StairPacket.Extension270.Block270
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails StockWindowTicket ArchivePortAction
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000
attribute [local irreducible] run routed body SkywalkNat.step

theorem origin_phase (x p : Nat) (good : Bounds x p) (raw history : State)
    (domain : Domain 270 x p raw) : (Leave270Reference.origin raw history).phase=raw.phase := by
  change (run (span 270 15) [] raw).phase=raw.phase
  exact WideReference.origin_phase 270 x p (by decide) good raw history domain

theorem native_admitted (d : Bool) (x p : Nat) (good : Bounds x p)
    (raw s : State) (m : List Bool) (g sg pg ps : Bool)
    (pre : At270 d x p raw s g sg pg ps) :
    let v := run (Native.nextWindow d) m s
    Leave270Admission.Inputs v (unsigned 270 x p) g sg ∧ v.phase=s.phase ∧
      (∃row<63145,RowTruth (unsigned 255 x p) pg ps row ∧ Kept Internal270.codePorts d row v) ∧
      (∀k : Fin 3,v.basis (1701+k.val)=false) ∧ ∀n,run (Native.nextUnwind d) n v=s := by
  let z := unsigned 270 x p
  let v := run (Native.nextWindow d) m s
  let tape := m.drop (measurementCount enter270)
  have nums := Leave270Admission.actualNumbers x p good
  have old := Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have curr := readInput 270 x p raw g sg pre.input
  have prior := past_at270 d x p raw s g sg pg ps pre
  have tailZero := Enter270.tail_from_domain x p good raw pre.domain
  have native := Native.next_window d raw s m z g sg nums.odd nums.small pre.cut curr tailZero
    (unsigned 255 x p) pg ps _ old.odd old.small prior
  obtain ⟨row,limit,truth,code,popped⟩ := Native.matched_receipt d raw s m z g sg nums.odd nums.small
    pre.cut curr tailZero (unsigned 255 x p) pg ps _ old.odd old.small prior
  have saved := Native.saved_with_pending d raw s z g sg m tape nums.small pre.cut curr
  have tail := Native.tail_clean d raw s m tape _ _ _ _ _ _ pre.cut curr
  have split : v=run (body Native.idx (Native.withArchive d)) tape (run enter270 m s) := by
    simp only [v,tape,Native.nextWindow,Native.window,run_append,run_take]
  have ex : ∀q∈Leave270Admission.spare,v.basis q=false := by
    have geometry : ∀q∈Leave270Admission.spare,q=1701 ∨ q=1702 ∨ q∈Native.tailTemps := by decide +kernel
    intro q hit
    rcases geometry q hit with rfl|rfl|high
    · exact popped 0
    · exact popped 1
    · exact split.symm ▸ tail q high
  have stored : regValue Leave270High.ys v.basis=(if Shadow.far 121 15 z then Shadow.high 121 15 z else 0) ∧
      v.basis 1700=false ∧ v.basis 1698=decide (Shadow.far 121 15 z) ∧
      v.basis 1699=decide (Shadow.far 121 15 z ∧ 2^121 ≤ z.u) := by
    rw [split,show Leave270High.ys=Enter270.saved by decide +kernel]
    exact saved
  exact ⟨Leave270Admission.assemble v z g sg nums native.2.1 native.2.2.1 stored ex,
    native.1,⟨row,limit,truth,code⟩,popped,native.2.2.2⟩

theorem body_cut (d : Bool) (x p : Nat) (good : Bounds x p)
    (raw s : State) (m n : List Bool) (g sg pg ps : Bool)
    (pre : At270 d x p raw s g sg pg ps) :
    let v := run (Native.nextWindow d) m s
    let flags := Leave270Admission.flags (unsigned 270 x p) g sg
    PackedCut Enter285.lowerPairs Enter285.upperPairs 300 1693 1691 1692
      (PortalValues.negative flags.2 (unsigned 285 x p).u)
      (decide (Shadow.far 114 15 (unsigned 285 x p)))
      (decide (Shadow.far 114 15 (unsigned 285 x p) ∧ 2^114 ≤ (unsigned 285 x p).u))
      (pullState (OB5.sig 284) (Leave270Reference.endRaw raw v))
      (eraseSites Enter285.pending (run leave270 n v)) := by
  let v := run (Native.nextWindow d) m s
  let tape := m.drop (measurementCount enter270)
  have native := native_admitted d x p good raw s m g sg pg ps pre
  have h := native.1
  have curr := readInput 270 x p raw g sg pre.input
  have split : v=run (body Native.idx (Native.withArchive d)) tape (run enter270 m s) := by
    simp only [v,tape,Native.nextWindow,Native.window,run_append,run_take]
  have tail := Native.tail_clean d raw s m tape _ _ _ _ _ _ pre.cut curr
  have quiet : ∀q∈Leave270CoreCheckpoint.rawSites,v.basis q=false := by
    have geometry : ∀q∈Leave270CoreCheckpoint.rawSites,(1556 ≤ q ∧ q ≤ 1694) ∨ q=1703 ∨ q∈Native.tailTemps := by decide +kernel
    intro q hit
    rcases geometry q hit with ⟨lo,hi⟩|rfl|endSite
    · exact Leave270Reference.nativeCarry _ v h.ready q lo hi
    · exact native.2.2.2.1 2
    · exact split.symm ▸ tail q endSite
  have phase : v.phase=(Leave270Reference.origin raw v).phase :=
    native.2.1.trans ((cutPhase pre.cut).trans (origin_phase x p good raw v pre.domain).symm)
  have ext : ∀q,Exterior 270 528 q → v.basis q=(Leave270Reference.origin raw v).basis q := by
    apply Leave270Reference.exterior_origin x p good raw s v pre.domain _ _ _ pre.cut
    intro q outside notOld
    rw [Leave270Reference.historySites_shape] at notOld
    rw [split]
    exact Native.exterior_kept d s m tape q outside notOld
  have upper : ∀q : Nat,441 ≤ q → q ≤ 528 → v.basis q=false := by
    rw [split]
    exact Native.upper_clear d raw s x p pre.domain m tape _ _ _ pre.cut
  have released : ∀q,Leave270Reference.releasedInput q → v.basis q=false := by
    intro q site
    have member : q∈Native.releasedSites := by
      unfold Native.releasedSites
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
      unfold Leave270Reference.releasedInput at site
      simp only [Wire] at *
      omega
    rw [split]
    exact (Native.released_kept d s m tape q member).trans
      (Leave270Reference.released_input x p good raw s pre.domain _ _ _ pre.cut q site)
  exact Leave270CertifiedCut.result x p good raw v n g sg pre.domain pre.input h phase ext upper quiet released

theorem advance (d : Bool) (x p : Nat) (good : Bounds x p)
    (raw s : State) (m n : List Bool) (g sg pg ps : Bool)
    (pre : At270 d x p raw s g sg pg ps) :
    let v := run (Native.nextWindow d) m s
    let flags := Leave270Admission.flags (unsigned 270 x p) g sg
    At285 d x p (Leave270Reference.endRaw raw v) (run leave270 n v) flags.1 flags.2 g sg := by
  let v := run (Native.nextWindow d) m s
  let out := run leave270 n v
  let raw' := Leave270Reference.endRaw raw v
  let flags := Leave270Admission.flags (unsigned 270 x p) g sg
  have native := native_admitted d x p good raw s m g sg pg ps pre
  have cut := body_cut d x p good raw s m n g sg pg ps pre
  have facts := Leave270ArchiveCut.result v n (unsigned 270 x p) g sg native.1
  have carried := Leave270Reference.advance_signed x p good raw v pre.domain g sg pre.input native.1.small
  have same := unique_input pre.input (fixed_input 270 x p (by decide) good raw pre.domain)
  have older (ports : Ports) (mem : ∀q∈Persistence.bank ports,q∈Persistence.older)
      (saved : Saved 225 x p ports d s) : Saved 225 x p ports d out := by
    obtain ⟨r,lim,chron,kept⟩ := saved
    refine ⟨r,lim,chron,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hit
    have old := mem q hit
    exact (Persistence.leave_keeps q (List.mem_append_left _ old) v n).trans
      (Persistence.native_keeps_older d q old s m)
  obtain ⟨row,limit,truth,kept⟩ := native.2.2.1
  have chr : ArchiveStockRows.Chronology 255 x p row := by
    unfold ArchiveStockRows.Chronology
    rw [←pre.pastCanonical]
    exact truth
  refine ⟨Leave270Reference.advance x p good raw v pre.domain,carried,cut,facts.records,?_,?_,?_,same,?_,?_,?_⟩
  · exact facts.far
  · exact facts.suffix
  · exact facts.crossed
  · exact older ArchiveBoundary240.codePorts (fun q hit=>List.mem_append_left _ hit) pre.saved225
  · obtain ⟨r,lim,chron,old⟩ := pre.saved240
    refine ⟨r,lim,chron,ArchiveWindowPreserve.keep old ?_⟩
    intro q hit
    have member : q∈Persistence.older := List.mem_append_right _ hit
    exact (Persistence.leave_keeps q (List.mem_append_left _ member) v n).trans
      (Persistence.native_keeps_older d q member s m)
  · exact ⟨row,limit,chr,ArchiveWindowPreserve.keep kept (fun q hit=>
      Persistence.leave_keeps q (List.mem_append_right _ hit) v n)⟩

end ECDSAAdd.Entrant.StairPacket.Extension270.Block270


namespace ECDSAAdd.Entrant.StairPacket.Extension270
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails StockWindowTicket ArchivePortAction
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run measurementCount body

private theorem phase_link (raw before after mid : State)
    (first second : Wire → Wire) (startPorts endPorts : List Wire)
    (a : (eraseSites endPorts after).phase = (pullState second mid).phase)
    (b : (pullState second mid).phase = raw.phase)
    (c : (eraseSites startPorts before).phase = (pullState first raw).phase) :
    after.phase=before.phase := by
  exact a.trans (b.trans c.symm)

theorem block_checked (d : Bool) (x p : Nat) (good : Bounds x p) :
    Checked (block270 d) (unblock270 d) (Ready270 d x p) (Ready285 d x p) := by
  rw [Native.block_eq,Native.unblock_eq]
  apply pair
  rintro s m ⟨raw,g,sg,pg,ps,pre⟩
  let v := run (Native.nextWindow d) m s
  let n := m.drop (measurementCount (Native.nextWindow d))
  have native := Block270.native_admitted d x p good raw s m g sg pg ps pre
  have cut := Block270.body_cut d x p good raw s m n g sg pg ps pre
  have advance := Block270.advance d x p good raw s m n g sg pg ps pre
  have outPhase : (run leave270 n v).phase=s.phase :=
    phase_link raw s (run leave270 n v) (Leave270Reference.endRaw raw v)
      (OB5.sig 269) (OB5.sig 284) ParkEndpoint.src Enter285.pending
      cut.phase (Block270.origin_phase x p good raw v pre.domain) pre.cut.phase
  exact ⟨outPhase,⟨_,_,_,g,sg,advance⟩,native.1.roundtrip n,native.2.2.2.2⟩

open Secp256k1 in
theorem terminal_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (terminal285 d) (unterminal285 d) (Ready285 d x p) (Final4 d x p) := by
  rintro s m ⟨raw,g,sg,pg,ps,pre⟩
  let z := unsigned 285 x p
  have short : min z.u z.v<2^114 := true_small x p 285 (lt_trans good.small good.cap) good.cap (by decide)
  have old := Leave270Admission.actualNumbers x p good
  have eq : farAt 114 285 x p=(3*2^130 ≤ z.u+z.v) := by
    apply propext
    unfold farAt Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have last := TerminalNative.from_domain d x good raw s m pre.domain z short g sg
    (readInput 285 x p raw g sg pre.input) (by simpa only [eq] using pre.cut)
    (unsigned 270 x p) pg ps (cross270 (unsigned 270 x p)) old.odd old.small
    pre.records pre.mode pre.side pre.crossed
  rw [←TerminalNative.terminal_eq] at last
  rw [←TerminalNative.unterminal_eq] at last
  obtain ⟨r,lim,truth,frame⟩ := last.2.1
  have chr : ArchiveStockRows.Chronology 270 x p r := by
    unfold ArchiveStockRows.Chronology
    rw [←pre.pastCanonical]
    exact truth
  refine ⟨last.1,?_,last.2.2⟩
  refine ⟨?_,?_,?_,⟨r,lim,chr,fun i=>frame ⟨i.val,by omega⟩⟩⟩
  · obtain ⟨r,lim,chr,kept⟩ := pre.saved225
    exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hit=>Persistence.terminal_keeps d q
      (List.mem_append_left _ (List.mem_append_left _ hit)) s m)⟩
  · obtain ⟨r,lim,chr,kept⟩ := pre.saved240
    exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hit=>Persistence.terminal_keeps d q
      (List.mem_append_left _ (List.mem_append_right _ hit)) s m)⟩
  · obtain ⟨r,lim,chr,kept⟩ := pre.saved255
    exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hit=>Persistence.terminal_keeps d q
      (List.mem_append_right _ hit) s m)⟩

open Secp256k1 in
theorem full_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (forward60plus1 d) (reverse60plus1 d) (Before d x p) (Final4 d x p) :=
  checked d x p good (block_checked d x p good) (terminal_checked d x good)

open Secp256k1 in
theorem forward_phase (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    (run (forward60plus1 d) m (pullState (OB5.sig 224) raw)).phase=raw.phase :=
  (full_checked d x good _ m ⟨raw,stage,rfl⟩).1

open Secp256k1 in
theorem roundtrip_any (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m n : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    run (reverse60plus1 d) n (run (forward60plus1 d) m (pullState (OB5.sig 224) raw))=
      pullState (OB5.sig 224) raw :=
  (full_checked d x good _ m ⟨raw,stage,rfl⟩).2.2 n

open Secp256k1 in
theorem roundtrip (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    run (reverse60plus1 d) m (run (forward60plus1 d) [] (pullState (OB5.sig 224) raw))=
      pullState (OB5.sig 224) raw :=
  roundtrip_any d x good raw [] m stage

end ECDSAAdd.Entrant.StairPacket.Extension270


namespace ECDSAAdd.Entrant.StairPacket.Extension270.Native
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction SkywalkRails StockCanonicalRow
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run routed body onRails
theorem selected_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^121)
    (cut:PackedCut Enter270.lowerPairs Enter270.upperPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (Shadow.far 121 15 z)) (decide (Shadow.far 121 15 z ∧ 2^121 ≤ z.u))
      (pullState (OB5.sig 269) raw) (eraseSites Enter270.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (tailZero:∀q∈Enter270.tailScratch,raw.basis q=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    let v:=key 129 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept codePorts d (select v) out:=by
  let pre:=run enter270 m s
  let tape:=m.drop (measurementCount enter270)
  let T:=Shadow.reduced 121 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 121 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter270.ready_pending raw s z G S m small cut input tailZero
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have held:=bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1
  have all:=frame_key sourceIdx rawPorts chronological row 129 past pg ps cross s _ prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt d pre tape _ spec.1 (reframe limit all rawPorts _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.Native

namespace ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction StockCanonicalRow
open ParkEndpoint285 Portal285 SkywalkRails StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
attribute [local irreducible] run
theorem selected_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^121)
    (prior:PastFacts sourceIdx rawPorts 121 past G S cross s) :
    let out:=run (p ++ (program d ++ Terminal285.load d)) m s
    out.phase=s.phase ∧ (let v:=key 121 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (Terminal285.restore d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=frame_key sourceIdx rawPorts chronological row 121 past G S cross s pre prior
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have spec:=select_spec ⟨row,limit,truth⟩
  have fresh:=reframe limit truth rawPorts pre frame
  have enc:=source_law d tick e legal
  have act:=Terminal285.load_run d _ spec.1 pre f fresh
  exact NativePack270.sequence_law p (program d) (Terminal285.load d) (Terminal285.restore d)
    (reverse d) q s m (fun out=>let v:=key 121 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Terminal285.load d) f pre) rfl act.1
    ⟨spec.1,spec.2,act.2.1⟩ (fun n=>Terminal285.roundtrip d _ spec.1 pre f n fresh)

theorem selected_slice (d:Bool) (s:State) (m:List Bool) (step:Transition EndTick285.physQ s (run EndTick285.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^121)
    (prior:PastFacts sourceIdx rawPorts 121 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (let v:=key 121 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (endUndo d) n out=s :=
  selected_generic EndTick285.physP EndTick285.physQ d s m step past G S cross odd small prior
theorem selected_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick285.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 285 original.basis)
    (hist:raw.basis (base (1028+285))=false) (swapSlot:raw.basis (base (2053-285))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^114) (G S:Bool)
    (input:SkywalkIntegerInput EndTick285.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 300 1693 1691 1692 (PortalValues.negative S z.u)
      (decide (3*2^130 ≤ z.u+z.v)) (decide (3*2^130 ≤ z.u+z.v ∧ 2^114 ≤ z.u)) (pullState (OB5.sig 284) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^121)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1694=decide (Shadow.far 121 15 past))
    (angle:s.basis 1695=(decide (Shadow.far 121 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1696=(decide (Shadow.far 121 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 121 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount park285)
  let one:=run portalInv285 n (run park285 m s)
  let tape:=n.drop (measurementCount portalInv285)
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=EndTick285.observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 284) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 121 past pg ps cross one :=by rw [eqOne];exact facts
  have B:Transition EndTick285.physQ one (run EndTick285.physP tape one):=by rw [eqOne];exact tick
  have body:=selected_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem selected_from_domain (d:Bool) (x:Nat) (good:WideReference.Bounds x p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 285 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^114) (G S:Bool)
    (input:SkywalkIntegerInput EndTick285.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 300 1693 1691 1692 (PortalValues.negative S z.u)
      (decide (3*2^130 ≤ z.u+z.v)) (decide (3*2^130 ≤ z.u+z.v ∧ 2^114 ≤ z.u)) (pullState (OB5.sig 284) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^121)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1694=decide (Shadow.far 121 15 past))
    (angle:s.basis 1695=(decide (Shadow.far 121 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1696=(decide (Shadow.far 121 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 121 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=Leave270Reference.terminal285 d x p good raw domain
  exact selected_last d x good.nonzero good.small raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.Extension270.TerminalNative


namespace ECDSAAdd.Entrant.StairPacket.Extension270.ConcreteRows
open Arithmetic Secp256k1 StockCanonicalRow StockStrongChain

noncomputable def keys (x : Nat) (b : Fin 4) : Nat → Bool :=
  if b=0 then value x p 225 144 cross225
  else if b=1 then value x p 240 136 cross240
  else if b=2 then value x p 255 129 cross255
  else value x p 270 121 cross270

noncomputable def rows (x : Nat) (b : Fin 4) : Nat := select (keys x b)

theorem rows_zero (x : Nat) : rows x 0=select (value x p 225 144 cross225) := by rfl
theorem rows_one (x : Nat) : rows x 1=select (value x p 240 136 cross240) := by rfl
theorem rows_two (x : Nat) : rows x 2=select (value x p 255 129 cross255) := by rfl
theorem rows_three (x : Nat) : rows x 3=select (value x p 270 121 cross270) := by rfl

end ECDSAAdd.Entrant.StairPacket.Extension270.ConcreteRows


namespace ECDSAAdd.Entrant.StairPacket.Extension270.StrongChain
open Arithmetic MappedCompressed Secp256k1 IntegerPacket WideReference SkywalkRails
open StockWindowTicket StockCanonicalRow StockStrongChain ArchivePortAction
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000
attribute [local irreducible] run measurementCount body

def Ready270Keys (d : Bool) (x : Nat) (s : State) : Prop :=
  Ready270 d x p s ∧ SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧
    SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s

def Ready285Keys (d : Bool) (x : Nat) (s : State) : Prop :=
  Ready285 d x p s ∧ SavedKey (value x p 255 129 cross255) Internal270.codePorts d s ∧
    SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧
    SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s

def Final (d : Bool) (x : Nat) (s : State) : Prop :=
  SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s ∧
  SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧
  SavedKey (value x p 255 129 cross255) Internal270.codePorts d s ∧
  SavedKey (value x p 270 121 cross270) Terminal285.codePorts d s

theorem head_selected (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (head45 d) (back45 d) (Before d x p) (Ready270Keys d x) := by
  rw [head45_shape,back45_shape]
  simpa only [List.append_assoc] using composition (step225 d x p good)
    (composition (StockStrongChain.selected240 d x p good) (StockStrongChain.selected255 d x p good))

theorem block_selected (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (block270 d) (unblock270 d) (Ready270Keys d x) (Ready285Keys d x) := by
  intro s m h
  have h0 := block_checked d x p good s m h.1
  obtain ⟨raw,g,sg,pg,ps,pre⟩ := h.1
  let v := run (Native.nextWindow d) m s
  let n := m.drop (measurementCount (Native.nextWindow d))
  have nums := Leave270Admission.actualNumbers x p good
  have old := Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have cert := Native.selected_receipt d raw s m (unsigned 270 x p) g sg nums.odd nums.small pre.cut
    (readInput 270 x p raw g sg pre.input) (Enter270.tail_from_domain x p good raw pre.domain)
    (unsigned 255 x p) pg ps _ old.odd old.small (past_at270 d x p raw s g sg pg ps pre)
  have canon := pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  refine ⟨h0.1,⟨h0.2.1,?_,?_,?_⟩,h0.2.2⟩
  · rw [Native.block_eq,run_append,run_take]
    exact ⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2
      (fun q hit=>Persistence.leave_keeps q (List.mem_append_right _ hit) v n)⟩
  · refine ⟨h.2.1.1,h.2.1.2.1,ArchiveWindowPreserve.keep h.2.1.2.2 ?_⟩
    intro q hit
    rw [Native.block_eq,run_append,run_take]
    have member : q∈Persistence.older := List.mem_append_right _ hit
    exact (Persistence.leave_keeps q (List.mem_append_left _ member) v n).trans
      (Persistence.native_keeps_older d q member s m)
  · refine ⟨h.2.2.1,h.2.2.2.1,ArchiveWindowPreserve.keep h.2.2.2.2 ?_⟩
    intro q hit
    rw [Native.block_eq,run_append,run_take]
    have member : q∈Persistence.older := List.mem_append_left _ hit
    exact (Persistence.leave_keeps q (List.mem_append_left _ member) v n).trans
      (Persistence.native_keeps_older d q member s m)

theorem terminal_selected (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (terminal285 d) (unterminal285 d) (Ready285Keys d x) (Final d x) := by
  intro s m h
  have h0 := terminal_checked d x good s m h.1
  obtain ⟨raw,g,sg,pg,ps,pre⟩ := h.1
  let z := unsigned 285 x p
  have short : min z.u z.v<2^114 := true_small x p 285 (lt_trans good.small good.cap) good.cap (by decide)
  have old := Leave270Admission.actualNumbers x p good
  have eq : farAt 114 285 x p=(3*2^130 ≤ z.u+z.v) := by
    apply propext
    unfold farAt Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have cert := TerminalNative.selected_from_domain d x good raw s m pre.domain z short g sg
    (readInput 285 x p raw g sg pre.input) (by simpa only [eq] using pre.cut)
    (unsigned 270 x p) pg ps (cross270 (unsigned 270 x p)) old.odd old.small
    pre.records pre.mode pre.side pre.crossed
  have canon := pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  rw [←TerminalNative.terminal_eq] at cert
  refine ⟨h0.1,?_,h0.2.2⟩
  refine ⟨?_,?_,?_,cert.2.1.1,cert.2.1.2.1,fun i=>cert.2.1.2.2 ⟨i.val,by omega⟩⟩
  · exact ⟨h.2.2.2.1,h.2.2.2.2.1,ArchiveWindowPreserve.keep h.2.2.2.2.2
      (fun q hit=>Persistence.terminal_keeps d q (List.mem_append_left _ (List.mem_append_left _ hit)) s m)⟩
  · exact ⟨h.2.2.1.1,h.2.2.1.2.1,ArchiveWindowPreserve.keep h.2.2.1.2.2
      (fun q hit=>Persistence.terminal_keeps d q (List.mem_append_left _ (List.mem_append_right _ hit)) s m)⟩
  · exact ⟨h.2.1.1,h.2.1.2.1,ArchiveWindowPreserve.keep h.2.1.2.2
      (fun q hit=>Persistence.terminal_keeps d q (List.mem_append_right _ hit) s m)⟩

theorem checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (forward60plus1 d) (reverse60plus1 d) (Before d x p) (Final d x) := by
  have law := composition (head_selected d x good)
    (composition (block_selected d x good) (terminal_selected d x good))
  simpa only [forward60plus1,reverse60plus1,List.append_assoc] using law

theorem result (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    Final d x (run (forward60plus1 d) m (pullState (OB5.sig 224) raw)) :=
  (checked d x good _ m ⟨raw,stage,rfl⟩).2.1

end ECDSAAdd.Entrant.StairPacket.Extension270.StrongChain


-- Append after selected Main, Extension270Arithmetic, GroupsBanks,
-- the checked physical overlay, Native/Block270, and TerminalNative.
-- The result has only Bounds and the original Stage225 input.

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Internal270
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
theorem load_cover (d:Bool) : wires (load d) ⊆ rawPortsList.toFinset := by
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
end ECDSAAdd.Entrant.StairPacket.Extension270.Internal270
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Terminal285
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
theorem load_cover (d:Bool) : wires (load d) ⊆ rawPortsList.toFinset := by
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
end ECDSAAdd.Entrant.StairPacket.Extension270.Terminal285
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.Local270
open Arithmetic MappedCompressed IntegerPacket WideReference Native
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
attribute [local irreducible] run body routed measurementCount

private theorem bins:∀i:Fin 10,∃r:Fin 270,(History5.historyMap base 255) i=base r.val ∨ (History5.historyMap base 255) i=base (1028+r.val) := by decide +kernel

private theorem old:∀i:Fin 10,oldRange (start idx+1) (windowNet idx (history i)) := by decide +kernel

private theorem injected:Function.Injective (History5.historyMap base 255):=by decide +kernel

private theorem kept (j:Fin 23) (admin:Program) (m:List Bool) (s:State) (q:Wire)
    (early:oldRange (start j+1) (windowNet j q)) :
    (run (body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s)).basis q := by
  simp only [body,run_append,run_take]
  exact route_outside j 1 14 (by decide) q (old_clear (by decide) early) _ _

private theorem pastInput (x p:Nat) (good:Bounds x p) (raw:State) (dom:Domain 270 x p raw) (i:Fin 10) :
    raw.basis (History5.historyMap base 255 i)=(run (span 270 15) [] raw).basis (History5.historyMap base 255 i) := by
  obtain ⟨r,h|h⟩:=bins i
  · rw [h];exact (preservePast 270 15 x p r.val (by decide) good raw dom r.isLt []).1.symm
  · rw [h];exact (preservePast 270 15 x p r.val (by decide) good raw dom r.isLt []).2.symm

private theorem encode (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (history i)=b.basis (History5.historyMap base 255 i)) (i:Fin 10) :
    (run (program d) tape a).basis (history i)=(run (Rolling1588.encodeAt base d 255) [] b).basis (History5.historyMap base 255 i) := by
  rw [Native.program,(NativePack270.equals d).1]
  exact ArchiveOrdinaryFive.stock_relocated d history _ NativePack270.histInj injected a b tape [] agree i

private theorem readback (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (history i)=raw.basis (History5.historyMap base 255 i))
    (stable:∀i,raw.basis (History5.historyMap base 255 i)=wide.basis (History5.historyMap base 255 i))
    (last:∀i,out.basis (history i)=(run (withArchive d) tape pre).basis (history i)) (i:Fin 10) :
    out.basis (history i)=(run (Rolling1588.encodeAt base d 255) [] wide).basis (History5.historyMap base 255 i) := by
  apply (last i).trans
  rw [withArchive,run_append,run_take]
  have off:∀q:Fin 10,history q∉Internal270.rawPortsList:=by decide +kernel
  rw [run_preserves_outside (Internal270.load d) _ _ _ (fun h=>(off i) (List.mem_toFinset.mp (Internal270.load_cover d h)))]
  exact encode d pre wide tape (fun j=>(input j).trans (stable j)) i

theorem result (d:Bool) (raw s:State) (m:List Bool) (x p:Nat) (good:Bounds x p) (dom:Domain 270 x p raw)
    (input:∀i,(run (routed idx 0 1) m s).basis (history i)=raw.basis (History5.historyMap base 255 i)) :
    ∀i,(run (body idx (withArchive d)) m s).basis (history i)=
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw)).basis (History5.historyMap base 255 i) := by
  exact readback d raw (run (routed idx 0 1) m s) (run (span 270 15) [] raw)
    _ _ input (pastInput x p good raw dom) (fun i=>kept idx _ m s _ (old i))
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.Local270
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.Logical270
open Arithmetic MappedCompressed WideReference Native
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
def newBank : List Wire := (List.range' 260 10).flatMap (fun r=>[base r,base (1028+r)])
def oldFive := (List.finRange 10).map (History5.historyMap base 255)
theorem inside (raw history : State) (q : Wire) (h:q∈sites 270) :
    (Leave270Reference.endRaw raw history).basis q=history.basis (OB5.sig 284 q) := by
  simp only [Leave270Reference.endRaw,Leave270Reference.reframe,if_pos h]
theorem outside (raw history : State) (q : Wire) (h:q∉sites 270) :
    (Leave270Reference.endRaw raw history).basis q=(run (span 270 15) [] raw).basis q := by
  simp only [Leave270Reference.endRaw,Leave270Reference.reframe,if_neg h]
theorem window (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (history i)=
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw)).basis (History5.historyMap base 255 i)) :
    ArchiveHistoryCompare.Except newBank (Leave270Reference.endRaw raw historyState)
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw)) := by
  have locations : ∀q∈sites 270,q∈oldFive ∨ q∈newBank := by decide +kernel
  have port : ∀i:Fin 10,history i=OB5.sig 284 (History5.historyMap base 255 i) := by decide +kernel
  have own:∀q∈oldFive,q∈sites 270:=by decide +kernel
  intro q ordinarySite
  by_cases old:q∈sites 270
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp ((locations q old).resolve_right ordinarySite)
    rw [inside raw historyState _ old,←port i]
    exact ordinaryBits i
  · have cover:wires (Rolling1588.encodeAt base d 255)⊆oldFive.toFinset:=by cases d <;> decide +kernel
    rw [outside raw historyState q old]
    exact (run_preserves_outside _ _ _ q (fun used=>old (own q (List.mem_toFinset.mp (cover used))))).symm
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.Logical270
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.LocalNative270
open Arithmetic MappedCompressed IntegerPacket WideReference Native
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body routed
theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (domain:Domain 270 x p raw)
    (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter270.lowerPairs Enter270.upperPairs 285 1700 1698 1699 neg far long
      (pullState (OB5.sig 269) raw) (eraseSites Enter270.pending s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run enter270 a s).basis) :
    let historyState:=run (body idx (withArchive d)) b (run enter270 a s)
    ArchiveHistoryCompare.Except Logical270.newBank (Leave270Reference.endRaw raw historyState)
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw)) := by
  let e:=run enter270 a s
  have input:∀i,(run (routed idx 0 1) b e).basis (history i)=raw.basis (History5.historyMap base 255 i) := by
    intro i
    have kept:=prefix_kept s a b z odd active i
    have geom:∀i:Fin 10,history i∉Enter270.pending ∧ history i≠1700 ∧ history i≠1698 ∧ history i≠1699 ∧
      history i∉RailPair.sites Enter270.upperPairs ∧ OB5.sig 269 (history i)=History5.historyMap base 255 i:=by decide +kernel
    obtain ⟨notTag,hn,hf,hu,hi,same⟩:=geom i
    exact kept.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact Logical270.window d raw _ (Local270.result d raw e b x p good domain input)
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.LocalNative270
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails StockWindowTicket Native
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
attribute [local irreducible] run body routed measurementCount

theorem ordinary270 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:At270 d x p raw s g sg pg ps) :
    ArchiveHistoryCompare.Except Logical270.newBank
      (Leave270Reference.endRaw raw (run (Native.nextWindow d) m s))
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw)) := by
  let z:=unsigned 270 x p
  let T:=Shadow.reduced 121 15 z
  have nums:=Leave270Admission.actualNumbers x p good
  have input:=readInput 270 x p raw g sg pre.input
  have tailZero:=Enter270.tail_from_domain x p good raw pre.domain
  have ready:=Enter270.ready_pending raw s z g sg m nums.small pre.cut input tailZero
  have odd:T.v%2=1:=shadow_odd 121 z nums.small nums.odd
  have parity:((encode g sg T.u T.v).a+(encode g sg T.u T.v).b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have h:=LocalNative270.result d x p good raw s pre.domain m (m.drop (measurementCount enter270))
    _ _ _ pre.cut _ parity ready.2.1
  simpa only [Native.nextWindow,Native.window,run_append,run_take] using h

def fourthHoles : List Wire := [1306,1308,1311,1313]

theorem holes270 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:At270 d x p raw s g sg pg ps) :
    ∀q∈fourthHoles,(Leave270Reference.endRaw raw (run (Native.nextWindow d) m s)).basis q=false := by
  let z:=unsigned 270 x p
  let prior:=past_at270 d x p raw s g sg pg ps pre
  let tape:=m.drop (measurementCount enter270)
  let T:=Shadow.reduced 121 15 z
  let Z:=encode g sg T.u T.v
  have nums:=Leave270Admission.actualNumbers x p good
  have old:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have input:=readInput 270 x p raw g sg pre.input
  have ready:=Enter270.ready_pending raw s z g sg m nums.small pre.cut input (Enter270.tail_from_domain x p good raw pre.domain)
  have to':T.v%2=1:=shadow_odd 121 z nums.small nums.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  obtain ⟨_,row,limit,frame⟩:=Native.admits d s m tape (tape.drop (measurementCount (routed Native.idx 0 1)))
    Z parity ready.2.1 (unsigned 255 x p) pg ps _ old.odd old.small prior
  have final:=Native.archive_result d row limit _ _ frame
  have slots:∀q∈fourthHoles,q∈sites 270 ∧ ∃i:Fin 157,16 ≤ i.val ∧
      Internal270.codePorts i=OB5.sig 284 q ∧ ¬MayTouch Native.idx (windowNet Native.idx (OB5.sig 284 q)):=by decide +kernel
  intro q hq
  obtain ⟨inside,i,hi,slot,absent⟩:=slots q hq
  rw [Logical270.inside raw _ q inside,Native.nextWindow,run_append,run_take]
  exact after_encoded Native.idx (Native.withArchive d) Internal270.codePorts d row
    (run enter270 m s) tape final i hi _ slot absent

theorem carry270 (raw history:State) (clear:∀q∈OrdinaryChain.older,raw.basis q=false) :
    ∀q∈OrdinaryChain.older,(Leave270Reference.endRaw raw history).basis q=false := by
  have old:∀q∈OrdinaryChain.older,oldRange 270 q:=by decide +kernel
  have away:∀q∈OrdinaryChain.older,q∉sites 270:=by decide +kernel
  intro q hit
  rw [Logical270.outside raw history q (away q hit),run_preserves_outside _ _ _ _
    (pastOffSpan _ _ _ (by decide) (OrdinaryChain.early 270 q (old q hit)))]
  exact clear q hit
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
open Arithmetic MappedCompressed WideReference IntegerPacket ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
attribute [local irreducible] run
def mask270:=OrdinaryChain.mask255++Logical270.newBank
def prog270 (d:Bool):=OrdinaryChain.prog255 d++Rolling1588.encodeAt base d 255
def lastBank:List Wire:=(List.range' 275 10).flatMap (fun r=>[base r,base (1028+r)])
def mask285:=mask270++lastBank

theorem add270 (d:Bool) (raw initial out:State)
    (old:Except OrdinaryChain.mask255 raw (run (OrdinaryChain.prog255 d) [] (run (span 225 45) [] initial)))
    (step:Except Logical270.newBank out (run (Rolling1588.encodeAt base d 255) [] (run (span 270 15) [] raw))) :
    Except mask270 out (run (prog270 d) [] (run (span 225 60) [] initial)) := by
  have maskEarly:∀q∈OrdinaryChain.mask255,oldRange 270 q:=by decide +kernel
  have progEarly:∀q∈wires (OrdinaryChain.prog255 d),oldRange 270 q:=by cases d <;> decide +kernel
  have apart:∀q∈OrdinaryChain.mask255,q∉wires (Rolling1588.encodeAt base d 255):=by cases d <;> decide +kernel
  have h:=extend 270 15 (by decide) _ _ _ _ raw (run (span 225 45) [] initial) out old step
    (fun q hit=>OrdinaryChain.early _ _ (maskEarly q hit))
    (fun q hit=>OrdinaryChain.early _ _ (progEarly q hit)) apart
  have chronology:run (span 225 60) [] initial=run (span 270 15) [] (run (span 225 45) [] initial):=by
    rw [spanAppend 225 45 15,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

theorem add285 (d:Bool) (raw initial out:State)
    (old:Except mask270 raw (run (prog270 d) [] (run (span 225 60) [] initial)))
    (step:Except lastBank out (run (Rolling1588.encodeAt base d 270) [] (run (span 285 1) [] raw))) :
    Except mask285 out (run (Reference.ordinary d) [] (run (span 225 61) [] initial)) := by
  have maskEarly:∀q∈mask270,oldRange 285 q:=by decide +kernel
  have progEarly:∀q∈wires (prog270 d),oldRange 285 q:=by cases d <;> decide +kernel
  have apart:∀q∈mask270,q∉wires (Rolling1588.encodeAt base d 270):=by cases d <;> decide +kernel
  have h:=extend 285 1 (by decide) _ _ _ _ raw (run (span 225 60) [] initial) out old step
    (fun q hit=>OrdinaryChain.early _ _ (maskEarly q hit))
    (fun q hit=>OrdinaryChain.early _ _ (progEarly q hit)) apart
  have chronology:run (span 225 61) [] initial=run (span 285 1) [] (run (span 225 60) [] initial):=by
    rw [spanAppend 225 60 1,run_append,run_take,List.drop_nil]
  rw [chronology]
  rw [show Reference.ordinary d=prog270 d++Rolling1588.encodeAt base d 270 from by
    simp only [Reference.ordinary,prog270,OrdinaryChain.prog255,OrdinaryChain.prog240,
      OrdinaryChain.prog225,List.append_assoc]]
  exact h
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.TerminalBasis
open Arithmetic MappedCompressed TerminalNative ArchivePortAction Terminal285 ParkEndpoint285 CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
def newBank := (List.range' 275 10).flatMap (fun r=>[OB5.sig 285 (base r), OB5.sig 285 (base (1028+r))])
def ordinary := (List.finRange 10).map history
def zeros:=List.range' 1556 134++dst

theorem basis (d:Bool) (raw payload:State) (m n:List Bool)
    (row:Nat)
    (clear:∀q∈zeros,raw.basis (OB5.sig 285 q)=false)
    (frame:Frame Terminal285.codePorts (code d) row (run (Terminal285.load d) n
      (run (program d) m (stash payload (pullState (OB5.sig 285) raw))))) :
    let out:=run (Terminal285.load d) n (run (program d) m (stash payload (pullState (OB5.sig 285) raw)))
    let wide:=run (Rolling1588.encodeAt base d 270) [] raw
    ∀q∉newBank,out.basis q=wide.basis (OB5.sig 285 q) := by
  let inp:=stash payload (pullState (OB5.sig 285) raw)
  let mid:=run (program d) m inp
  let wide:=run (Rolling1588.encodeAt base d 270) [] raw
  let coords:=History5.historyMap base 270
  have geom:∀i:Fin 10,history i∉dst ∧ OB5.sig 285 (history i)=coords i ∧ history i∉rawPortsList := by dsimp only [coords];decide +kernel
  have agree (i:Fin 10):inp.basis (history i)=raw.basis (coords i):=by
    simp only [inp,stash,if_neg (geom i).1,pullState,(geom i).2.1]
  have injected:Function.Injective coords:=by dsimp only [coords];decide +kernel
  have keep (q:Wire) (no:q∉ordinary) : wide.basis (OB5.sig 285 q)=raw.basis (OB5.sig 285 q) := by
    have cover:wires (Rolling1588.encodeAt base d 270) ⊆ ((List.finRange 10).map coords).toFinset:=by dsimp only [coords];cases d <;> decide +kernel
    apply run_preserves_outside
    intro h
    obtain ⟨i,_,e⟩:=List.mem_map.mp (List.mem_toFinset.mp (cover h))
    have e':OB5.sig 285 (history i)=OB5.sig 285 q:=(geom i).2.1.trans e
    have unique:history i=q:=by simpa only [OB5.sig_invol 285 (by decide)] using congrArg (OB5.sig 285) e'
    exact no (List.mem_map.mpr ⟨i,List.mem_finRange i,unique⟩)
  dsimp only
  intro q outside
  by_cases normal:q∈ordinary
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp normal
    rw [run_preserves_outside (Terminal285.load d) _ _ _ (fun h=>(geom i).2.2 (List.mem_toFinset.mp (load_cover d h))), (geom i).2.1]
    have encoded:=ArchiveOrdinaryFive.stock_relocated d history coords histInj injected inp raw m [] agree i
    rw [←(equals d).1] at encoded
    exact encoded
  rw [keep q normal]
  by_cases touched:q∈rawPortsList
  · have mask:∀q∈rawPortsList,q∈newBank ∨ (q∈zeros ∧ ∃i:Fin 157,16≤ i.val ∧ Terminal285.codePorts i=q) := by decide +kernel
    obtain ⟨blank,i,hi,slot⟩:=(mask q touched).resolve_left outside
    rw [clear q blank,←slot,frame,archive_blank _ _ hi,Nat.zero_testBit]
  · have no:q∉wires (Terminal285.load d):=fun h=>touched (List.mem_toFinset.mp (load_cover d h))
    have mask:∀q∈dst,q∈rawPortsList:=by decide +kernel
    have notDst:q∉dst:=fun h=>touched (mask q h)
    rw [run_preserves_outside _ _ _ _ no]
    exact (TerminalNative.outside d q (fun i e=>normal (List.mem_map.mpr ⟨i,List.mem_finRange i,e.symm⟩)) _ _).trans
      (by simp only [stash,if_neg notDst,pullState])
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized.TerminalBasis
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails StockWindowTicket
open TerminalNative ParkEndpoint285 ArchiveHistoryCompare
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
attribute [local irreducible] run

theorem terminal_direct (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:At285 d x p raw s g sg pg ps) :
    Except TerminalBasis.newBank (run (terminal285 d) m s)
      (pullState (OB5.sig 285) (run (Rolling1588.encodeAt base d 270) [] (run EndTick285.canonical [] raw))) := by
  obtain ⟨ref,stage,read,hist,spare,spaces⟩:=Leave270Reference.terminal285 d x p good raw pre.domain
  let z:=unsigned 285 x p
  let v:=run EndTick285.canonical [] raw
  let p1:=m.drop (measurementCount park285)
  let p2:=p1.drop (measurementCount portalInv285)
  let p3:=p2.drop (measurementCount EndTick285.physP)
  let p4:=p3.drop (measurementCount (TerminalNative.program d))
  have lim:min z.u z.v<2^114:=true_small x p 285 (lt_trans good.small good.cap) good.cap (by decide)
  have mode:farAt 114 285 x p=(3*2^130≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have first:=parked_release z lim raw s m p1 g sg (readInput 285 x p raw g sg pre.input)
    (by simpa only [mode] using pre.cut) (empty_from_cut _ _ _ _ _ pre.cut spaces)
  have tick:=EndTick285.physical d x good.nonzero good.small raw ref s read stage hist spare p2
  let loaded:=run (Terminal285.load d) p4 (run (TerminalNative.program d) p3 (stash s (pullState (OB5.sig 285) v)))
  have actual:run (terminal285 d) m s=loaded:=by
    rw [TerminalNative.terminal_eq]
    simp only [TerminalNative.lastWindow,TerminalNative.endSlice,run_append,run_take]
    change run (Terminal285.load d) p4 (run (TerminalNative.program d) p3
      (run EndTick285.physP p2 (run portalInv285 p1 (run park285 m s))))=_
    rw [first.1,tick.1]
  have old:=Leave270Admission.actualNumbers x p good
  have receipt:=TerminalNative.from_domain d x good raw s m pre.domain z lim g sg
    (readInput 285 x p raw g sg pre.input) (by simpa only [mode] using pre.cut)
    (unsigned 270 x p) pg ps _ old.odd old.small pre.records pre.mode pre.side pre.crossed
  obtain ⟨row,_,_,frame⟩:=receipt.2.1
  rw [←TerminalNative.terminal_eq,actual] at frame
  have zeros (q:Wire) (h:q∈TerminalBasis.zeros) : v.basis (OB5.sig 285 q)=false:=by
    rcases List.mem_append.mp h with carryLane|tag
    · have table:∀q∈List.range' 1556 134,∃k:Fin 134,OB5.sig 285 q=1556+k.val:=by decide +kernel
      obtain ⟨k,eq⟩:=table q carryLane
      rw [eq]
      exact (EndTick285.after_cells d x good.nonzero good.small raw ref read stage).2 k
    · have coords:∀q∈dst,OB5.sig 285 q=OB5.sig 284 q:=by decide +kernel
      have nocell:=EndTick285.spared q tag
      have cover:=W.compactSkywalkTick_support base 285 (by decide) base_pool_nodup
      have no:OB5.sig 285 q∉wires EndTick285.canonical:=fun used=>nocell (List.mem_toFinset.mp (cover used))
      exact (run_preserves_outside _ _ _ _ no).trans (by rw [coords q tag];exact spaces q tag)
  rw [actual]
  exact TerminalBasis.basis d v s p3 p4 row zeros frame

def older:=OrdinaryChain.older++fourthHoles
def finalHoles:List Wire:=[1321,1323,1326,1328]

private theorem project (d:Bool) (raw out:State)
    (direct:Except TerminalBasis.newBank out (pullState (OB5.sig 285)
      (run (Rolling1588.encodeAt base d 270) [] (run EndTick285.canonical [] raw)))) :
    Except lastBank (pullState (OB5.sig 285) out)
      (run (Rolling1588.encodeAt base d 270) [] (run (span 285 1) [] raw)) := by
  have one:span 285 1=EndTick285.canonical:=by simp [span,EndTick285.canonical]
  rw [one]
  intro q absent
  have map:∀w∈TerminalBasis.newBank,OB5.sig 285 w∈lastBank:=by decide +kernel
  have away:OB5.sig 285 q∉TerminalBasis.newBank:=fun hit=>absent
    (by simpa only [OB5.sig_invol 285 (by decide)] using map _ hit)
  simpa only [pullState,OB5.sig_invol 285 (by decide)] using direct _ away

private theorem readOld (d:Bool) (raw out:State)
    (direct:Except TerminalBasis.newBank out (pullState (OB5.sig 285)
      (run (Rolling1588.encodeAt base d 270) [] (run EndTick285.canonical [] raw))))
    (clear:∀q∈older,raw.basis q=false) : ∀q∈older,out.basis (OB5.sig 285 q)=false := by
  have away:∀q∈older,OB5.sig 285 q∉TerminalBasis.newBank:=by decide +kernel
  have old:∀q∈older,oldRange 285 q:=by decide +kernel
  have encodeOff:∀q∈older,q∉wires (Rolling1588.encodeAt base d 270):=by cases d <;> decide +kernel
  intro q hit
  have h:=direct _ (away q hit)
  change out.basis (OB5.sig 285 q)=
    (run (Rolling1588.encodeAt base d 270) [] (run EndTick285.canonical [] raw)).basis (OB5.sig 285 (OB5.sig 285 q)) at h
  rw [OB5.sig_invol 285 (by decide),run_preserves_outside _ _ _ _ (encodeOff q hit)] at h
  have one:span 285 1=EndTick285.canonical:=by simp [span,EndTick285.canonical]
  rw [←one,run_preserves_outside _ _ _ _
    (pastOffSpan _ _ _ (by decide) (OrdinaryChain.early _ _ (old q hit)))] at h
  exact h.trans (clear q hit)

private theorem finish (d:Bool) (out initial:State)
    (all:Except mask285 (pullState (OB5.sig 285) out)
      (run (Reference.ordinary d) [] (run (span 225 61) [] initial)))
    (saved:∀q∈older,out.basis (OB5.sig 285 q)=false)
    (last:∀q∈finalHoles,out.basis (OB5.sig 285 q)=false) :
    ∀q∉Suffix.archives,out.basis q=(Reference.common d initial).basis q := by
  intro q away
  let y:=OB5.sig 285 q
  have inv:OB5.sig 285 y=q:=OB5.sig_invol 285 (by decide) q
  change out.basis q=(eraseSites Reference.holes
    (run (Reference.ordinary d) [] (run (span 225 61) [] initial))).basis y
  by_cases hole:y∈Reference.holes
  · have which:∀w∈Reference.holes,w∈older ∨ w∈finalHoles:=by decide +kernel
    have h:=which y hole
    simp only [eraseSites,if_pos hole]
    rw [←inv]
    exact h.elim (saved y) (last y)
  · have census:∀w∈mask285,w∈Reference.holes ∨ OB5.sig 285 w∈Suffix.archives:=by decide +kernel
    have free:y∉mask285:=fun hit=>away (inv ▸ (census y hit).resolve_left hole)
    have value:=all y free
    change out.basis (OB5.sig 285 y)=_ at value
    rw [inv] at value
    simpa only [eraseSites,if_neg hole] using value

theorem terminal (d:Bool) (x:Nat) (good:Bounds x p) (raw s initial:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:At285 d x p raw s g sg pg ps)
    (prior:Except mask270 raw (run (prog270 d) [] (run (span 225 60) [] initial)))
    (clear:∀q∈older,raw.basis q=false) :
    let out:=run (terminal285 d) m s
    ∀q∉Suffix.archives,out.basis q=(Reference.common d initial).basis q := by
  let out:=run (terminal285 d) m s
  have direct:=terminal_direct d x good raw s g sg pg ps m pre
  have nums:=Leave270Admission.actualNumbers x p good
  have now:min (unsigned 285 x p).u (unsigned 285 x p).v<2^114:=
    true_small x p 285 (lt_trans good.small good.cap) good.cap (by decide)
  have mode:farAt 114 285 x p=(3*2^130≤(unsigned 285 x p).u+(unsigned 285 x p).v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have receipt:=TerminalNative.from_domain d x good raw s m pre.domain (unsigned 285 x p) now g sg
    (readInput 285 x p raw g sg pre.input) (by simpa only [mode] using pre.cut)
    (unsigned 270 x p) pg ps _ nums.odd nums.small pre.records pre.mode pre.side pre.crossed
  obtain ⟨row,_,_,frame⟩:=receipt.2.1
  rw [←TerminalNative.terminal_eq] at frame
  have blanks:∀q∈finalHoles,∃i:Fin 157,16 ≤ i.val ∧ Terminal285.codePorts i=OB5.sig 285 q:=by decide +kernel
  have zero:∀q∈finalHoles,out.basis (OB5.sig 285 q)=false:=by
    intro q hit
    obtain ⟨i,hi,eq⟩:=blanks q hit
    rw [←eq,frame,archive_blank d i hi,Nat.zero_testBit]
  exact finish d out initial (add285 d raw initial _ prior (project d raw out direct))
    (readOld d raw out direct clear) zero
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
open Arithmetic MappedCompressed WideReference IntegerPacket SkywalkRails StockWindowTicket ArchiveHistoryCompare Secp256k1
set_option maxRecDepth 40000
set_option maxHeartbeats 6000000
attribute [local irreducible] run measurementCount

def Ref285 (d:Bool) (x:Nat) (initial s:State):Prop:=
  ∃raw g sg pg ps,At285 d x p raw s g sg pg ps ∧
    Except mask270 raw (run (prog270 d) [] (run (span 225 60) [] initial)) ∧
    ∀q∈older,raw.basis q=false

theorem next270 (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (m n:List Bool)
    (h:OrdinaryChain.Ref270 d x initial s) :
    Ref285 d x initial (run leave270 n (run (Native.nextWindow d) m s)) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  let v:=run (Native.nextWindow d) m s
  let flags:=Leave270Admission.flags (unsigned 270 x p) g sg
  have pre':=Block270.advance d x p good raw s m n g sg pg ps pre
  have values:=add270 d raw initial _ old (ordinary270 d x p good raw s g sg pg ps m pre)
  have fresh:=holes270 d x p good raw s g sg pg ps m pre
  exact ⟨Leave270Reference.endRaw raw v,flags.1,flags.2,g,sg,pre',values,
    fun q hit=>(List.mem_append.mp hit).elim (carry270 raw v zeros q) (fresh q)⟩

theorem head (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    OrdinaryChain.Ref270 d x raw (run (head45 d) m (pullState (OB5.sig 224) raw)) := by
  rw [head45_shape]
  simp only [run_append,run_take]
  exact OrdinaryChain.next255 d x good raw _ _ _
    (OrdinaryChain.next240 d x good raw _ _ _ (OrdinaryChain.begin225 d x good raw _ _ stage))

theorem wires (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    ∀q∉Suffix.archives,(run (forward60plus1 d) m (pullState (OB5.sig 224) raw)).basis q=
      (Reference.common d raw).basis q := by
  have start:=head d x good raw m stage
  let tape:=m.drop (measurementCount (head45 d))
  let after:=tape.drop (measurementCount (Native.nextWindow d))
  have mid:=next270 d x good raw _ tape after start
  obtain ⟨r,g,sg,pg,ps,pre,old,clear⟩:=mid
  have finish:=terminal d x good r _ raw g sg pg ps
    (after.drop (measurementCount leave270)) pre old clear
  simpa only [forward60plus1,Native.block_eq,List.append_assoc,run_append,run_take,
    measurementCount_append,List.drop_drop,Nat.add_assoc,tape,after] using finish

theorem common_phase (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    (Reference.common d raw).phase=raw.phase := by
  let wide:=run (span 225 61) [] raw
  have stock:=congrArg State.phase (Banks.stock_state d x good raw [] stage)
  have encoded:(run (Groups.batch d Groups.all) [] wide).phase=wide.phase:=Groups.phase_batch d _ wide
  have phase:wide.phase=raw.phase:=by
    change (run (Rolling1588TickGap.forward d 225 61) [] (pullState (OB5.sig 224) raw)).phase=
      (run (Groups.batch d Groups.all) [] wide).phase at stock
    exact encoded.symm.trans (stock.symm.trans (StockBaseline.forward_phase d x good 225 61 (by decide) (by decide) raw [] stage))
  change (run (Reference.ordinary d) [] wide).phase=raw.phase
  rw [Groups.ordinaryEq]
  exact (Groups.phase_batch d Groups.plain wide).trans phase

theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    Suffix.Same (run (forward60plus1 d) m (pullState (OB5.sig 224) raw)) (Reference.common d raw) :=
  ⟨(Extension270.forward_phase d x good raw m stage).trans (common_phase d x good raw stage).symm,
    wires d x good raw m stage⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.Normalized
end


namespace ECDSAAdd.Entrant.StairPacket.Extension270.ConcreteRows
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain WideReference ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
attribute [local irreducible] run measurementCount

theorem fields (d : Bool) (x : Nat) (s : State) (h : StrongChain.Final d x s) (b : Banks.Bank) :
    SavedKey (keys x b) (Banks.ports b) d s := by
  fin_cases b
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem historical (b i x p : Nat) (c : SkywalkNat.State→Bool) (r : Nat)
    (labels : Encodes (value x p i b c) r) : ArchiveStockRows.Chronology i x p r := by
  intro j
  have bit := labels ⟨j,by omega⟩
  simpa only [value,key,StairArchiveRaw.rawBit,j.isLt,if_true] using bit

theorem trace {d x s} (h : StrongChain.Final d x s) (b : Banks.Bank) :
    ArchiveStockRows.Chronology (Banks.tick b) x p (rows x b) := by
  fin_cases b
  · exact historical 144 225 x p cross225 _ h.1.2.1
  · exact historical 136 240 x p cross240 _ h.2.1.2.1
  · exact historical 129 255 x p cross255 _ h.2.2.1.2.1
  · exact historical 121 270 x p cross270 _ h.2.2.2.2.1

theorem binding : WalkForward.Binding rows := by
  intro d x good raw m stage
  let out := run (forward60plus1 d) m (pullState (OB5.sig 224) raw)
  have stored := StrongChain.result d x good raw m stage
  have res : Banks.Final d x p out := by
    have facts := (full_checked d x good _ m ⟨raw,stage,rfl⟩).2.1
    intro b
    fin_cases b
    · exact facts.1
    · exact facts.2.1
    · exact facts.2.2.1
    · exact facts.2.2.2
  have normal := Normalized.result d x good raw m stage
  have compare := Groups.comparison d x good raw out m stage res
  refine ⟨⟨normal.1.trans compare.1.symm,fun q off=>(normal.2 q off).trans (compare.2 q off).symm⟩,
    fun b=>⟨(fields d x out stored b).1,trace stored b⟩,
    fun b=>(fields d x out stored b).2.2,?_⟩
  intro b
  exact Banks.stored d x good raw m stage b (rows x b) (fields d x out stored b).1 (trace stored b)

end ECDSAAdd.Entrant.StairPacket.Extension270.ConcreteRows

namespace ECDSAAdd.Entrant.StairPacket.Extension270.InverseReplay
open Arithmetic MappedCompressed Secp256k1 WideReference Suffix Banks StockWalkWindow WalkForward
set_option maxRecDepth 11000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Rolling1588.Integer.regularReverse Extension270.forward60plus1 Extension270.reverse60plus1
abbrev pool := (skywalkPoolWires base).toFinset
def poolEq (a b:State):Prop:=∀q∈pool,a.basis q=b.basis q

theorem reverse_forward (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512) (raw:State) (m r:List Bool)
    (st:Rolling1588.Integer.Stage base d x p i raw.basis):
    let start:=pullState (OB5.sig (i-1)) raw
    run (Rolling1588.reverse d i n) r (run (Rolling1588TickGap.forward d i n) m start)=start:=by
  dsimp only
  let v:=run (Rolling1588.Integer.regularForward base d i n) m raw
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have one:=Rolling1588TickGap.forward_gen d x good.nonzero good.small n i lo hi raw m st
  have two:=(Rolling1588.Integer.reverse_gen d x good.nonzero good.small n i lo hi raw m v r st (fun _ _=>rfl)).1
  rw [Rolling1588.Integer.reverse_eq_packets] at two
  have undo:=Rolling1588.Integer.regularReverse_roundtrip base d base_pool_nodup StackOB5.historyAbove x p hp0 good.nonzero odd cap (by norm_num [p]) good.small cop n i hi raw m r st
  exact (congrArg (run (Rolling1588.reverse d i n) r) one).trans (two.trans (congrArg (pullState (OB5.sig (i-1))) undo))

theorem bank_rep (q:Wire) (hit:q∈Suffix.archives) : ∃(b:Banks.Bank)(j:Fin 16),Banks.siteAt b j=q:=by
  simp only [Suffix.archives,Suffix.bank,Finset.mem_union,List.mem_toFinset,List.mem_map,List.mem_finRange,true_and] at hit
  rcases hit with ((⟨j,rfl⟩|⟨j,rfl⟩)|⟨j,rfl⟩)|⟨j,rfl⟩
  · exact ⟨0,j,congrArg ArchiveBoundary240.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
  · exact ⟨1,j,congrArg ArchiveBoundary255.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
  · exact ⟨2,j,congrArg Internal270.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
  · exact ⟨3,j,congrArg Terminal285.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩

theorem paired_pool {d x rows a ref b old} (actual:Paired d x a ref rows) (ghost:Paired d x b old rows)
    (agree:poolEq ref old):poolEq a b:=by
  intro q hq
  by_cases h:q∈archives
  · obtain ⟨k,j,rfl⟩:=bank_rep q h
    exact (actual.custom k j).trans (ghost.custom k j).symm
  · exact (actual.equality.2 q h).trans ((agree q hq).trans (ghost.equality.2 q h).symm)

theorem replay (P Q:Program) (m:List Bool) (a ref b old origin:State) (A:wires P⊆pool) (B:wires Q⊆pool)
    (outside:∀q∉pool,a.basis q=ref.basis q) (phase:a.phase=ref.phase) (gp:b.phase=old.phase)
    (h1:poolEq a b) (h2:poolEq ref old) (one:run P m b=origin) (two:run Q m old=origin):
    run P m a=run Q m ref:=by
  have frame (h:poolEq a b):∀q∈wires P,a.basis q=b.basis q:=fun q hq=>h q (A hq)
  have left:=run_local_increment P a b m (frame h1)
  have right:=run_local_increment Q ref old m (fun q hq=>h2 q (B hq))
  rw [one] at left
  rw [two] at right
  apply State.extensionality
  · have h:=(left.1.trans (congrArg (fun v:Bool=>origin.phase ^^ v) gp)).trans right.1.symm
    rw [phase] at h
    cases ref.phase <;> simpa using h
  · funext q
    by_cases u:q∈pool
    · have output (C:Program) (ac gh:State) (g:poolEq ac gh) (h:run C m gh=origin)
          (eq:∀q∈wires C,(run C m ac).basis q=origin.basis q):
          (run C m ac).basis q=origin.basis q:=by
        by_cases use:q∈wires C
        · exact eq q use
        · rw [←h,run_preserves_outside C m ac q use,run_preserves_outside C m gh q use]
          exact g q u
      exact (output P a b h1 one left.2).trans (output Q ref old h2 two right.2).symm
    · rw [run_preserves_outside P m a q (fun hit=>u (A hit)),run_preserves_outside Q m ref q (fun hit=>u (B hit))]
      exact outside q u

theorem archives_pool (q:Wire) (hit:q∈archives):q∈pool:=by
  obtain ⟨b,j,rfl⟩:=bank_rep q hit
  have good:∀(b:Bank)(j:Fin 16),16≤siteAt b j ∧ siteAt b j≤1812:=by decide +kernel
  exact List.mem_toFinset.mpr (PartialSites.range_pool _ (good b j).1 (good b j).2)

end ECDSAAdd.Entrant.StairPacket.Extension270.InverseReplay

namespace ECDSAAdd.Entrant.StairPacket.Extension270.BackWindow
open Arithmetic MappedCompressed Secp256k1 WideReference Banks StockWalkWindow Suffix InverseReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Extension270.forward60plus1 Extension270.reverse60plus1

def real (d:Bool) (raw:State):State:=run (Extension270.forward60plus1 d) [] (pullState (OB5.sig 224) raw)
def stock (d:Bool) (raw:State):State:=run (Rolling1588TickGap.forward d 225 61) [] (pullState (OB5.sig 224) raw)
def Roundtrip : Prop := ∀(d:Bool)(x:Nat)(_:Bounds x p)(raw:State)(m:List Bool),
  Rolling1588.Integer.Stage base d x p 225 raw.basis →
    run (Extension270.reverse60plus1 d) m (real d raw)=pullState (OB5.sig 224) raw

theorem shadow (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    Paired d x (real d raw) (stock d raw) (rows x):=law d x good raw [] stage
theorem candidate_undo (undo:Roundtrip) (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    run (Extension270.reverse60plus1 d) m (real d raw)=pullState (OB5.sig 224) raw:=undo d x good raw m stage

theorem pool_of_check (P:Program)
    (check:P.all (fun i=>(ECDSAAdd.Entrant.WSlimMain.instrList i).all (fun q=>decide (16≤q ∧ q≤1812)))=true):
    wires P⊆pool:=by
  have bound:∀q∈wires P,decide (16≤q ∧ q≤1812)=true:=by
    apply ECDSAAdd.Entrant.WSlimMain.forall_mem_wires_of_all
    exact check
  intro q hq
  have h:16≤q ∧ q≤1812:=of_decide_eq_true (bound q hq)
  exact List.mem_toFinset.mpr (PartialSites.range_pool q h.1 h.2)

theorem unroute_sites (j:Fin 23) (a n:Nat) (lim:a+n≤15) (q:Wire) (used:q∈wires (unrouted j a n)):
    q∈spanSites j a n:=by
  induction n generalizing a with
  | zero=>simp [unrouted,wires] at used
  | succ n ih=>
    rw [unrouted,wires_append,Finset.mem_union] at used
    rw [spanSites,List.range'_succ,List.flatMap_cons,List.mem_append]
    rcases used with tail|now
    · exact Or.inr (ih (a+1) (by omega) tail)
    · rw [renameProgram_support,Finset.mem_image] at now
      obtain ⟨t,hit,eq⟩:=now
      have lt:a<15:=by omega
      have inside:=List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape j) ⟨a,lt⟩)).2 hit)
      exact Or.inl (List.mem_map.mpr ⟨t,inside,(StairPacket.stable lt inside).symm.trans eq⟩)

theorem unrouted_pool (j:Fin 23) (member:j∈([10,11,12,13]:List (Fin 23))) (a n:Nat) (lim:a+n≤15):
    wires (unrouted j a n)⊆pool:=by
  have bounds:∀j∈([10,11,12,13]:List (Fin 23)),∀r:Fin 15,∀q∈(IntegerPacket.ports (shape j) r.val).wires,
      16≤windowNet j q ∧ windowNet j q≤1812:=by decide +kernel
  intro q hit
  obtain ⟨r,range,inside⟩:=List.mem_flatMap.mp (unroute_sites j a n lim q hit)
  have limits:=List.mem_range'_1.mp range
  have small:r<15:=by omega
  change q∈(IntegerPacket.ports (shape j) r).wires.map (windowNet j) at inside
  obtain ⟨w,mem,eq⟩:=List.mem_map.mp inside
  have h:=bounds j member ⟨r,small⟩ w mem
  rw [eq] at h
  exact List.mem_toFinset.mpr (PartialSites.range_pool q h.1 h.2)

attribute [local irreducible] unrouted
theorem candidate_pool (d:Bool):wires (Extension270.reverse60plus1 d)⊆pool:=by
  simp only [Extension270.reverse60plus1,Extension270.unterminal285,Extension270.unblock270,
    Extension270.back45,wires_append,Finset.union_subset_iff]
  repeat' apply And.intro
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 13 (by decide) 1 14 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 13 (by decide) 0 1 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 12 (by decide) 1 14 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 12 (by decide) 0 1 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 11 (by decide) 1 14 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 11 (by decide) 0 1 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 10 (by decide) 1 14 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · exact unrouted_pool 10 (by decide) 0 1 (by decide)
  · apply pool_of_check;cases d <;> decide +kernel
  · apply pool_of_check;cases d <;> decide +kernel
theorem stock_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    run (Rolling1588.reverse d 225 61) m (stock d raw)=pullState (OB5.sig 224) raw:=
  reverse_forward d x good 225 61 (by decide) (by decide) raw [] m stage
attribute [local irreducible] real stock poolEq
theorem inner (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows) (undo:Roundtrip) (d:Bool) (x:Nat) (good:Bounds x p) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis)
    (pair:Paired d x a ref (rows x))
    (agree:poolEq ref (stock d raw)):
    run (Extension270.reverse60plus1 d) m a=run (Rolling1588.reverse d 225 61) m ref:=by
  have ghost:=shadow rows law d x good raw stage
  exact replay _ _ m a ref (real d raw) (stock d raw) _ (candidate_pool d) (PartialSites.pool_old d 225 61 (by decide) (by decide))
    (fun q off=>pair.equality.2 q (fun h=>off (archives_pool q h))) pair.equality.1 ghost.equality.1
    (paired_pool pair ghost agree) agree (candidate_undo undo d x good raw m stage) (stock_undo d x good raw m stage)

theorem pool_run {C:Program} (cover:wires C⊆pool) {a b} (h:poolEq a b) (m:List Bool):poolEq (run C m a) (run C m b):=by
  unfold poolEq at h ⊢
  have use:=run_local_increment C a b m (fun q hq=>h q (cover hq))
  intro q hq
  by_cases hit:q∈wires C
  · exact use.2 q hit
  · rw [run_preserves_outside C m a q hit,run_preserves_outside C m b q hit]
    exact h q hq

private theorem transport (F R:Program) (m:List Bool) (a b:State) (eq:a=b) (inv:run R m (run F [] b)=b):
    run R m (run F [] a)=a:=eq ▸ inv
theorem stageAt (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (hi:i+n≤512) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p i raw.basis):
    Rolling1588.Integer.Stage base d x p (i+n) (run (Rolling1588.Integer.regularForward base d i n) m raw).basis:=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  exact (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p i n hp0 good.nonzero odd cap (by norm_num [p]) good.small cop hi raw m stage).2
theorem tail_cancel (d:Bool) (x i h n:Nat) (good:Bounds x p) (lo:1 ≤ i) (bound:i+h+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p i raw.basis) (m:List Bool):
    let s:=pullState (OB5.sig (i-1)) raw
    let old:=run (Rolling1588TickGap.forward d i h) [] s
    run (Rolling1588.reverse d (i+h) n) m (run (Rolling1588TickGap.forward d (i+h) n) [] old)=old:=by
  let t:=run (Rolling1588.Integer.regularForward base d i h) [] raw
  have cut:i+h≤512:=by omega
  have st:=stageAt d x good i h cut raw [] stage
  have eq:=Rolling1588TickGap.forward_gen d x good.nonzero good.small h i lo cut raw [] stage
  exact transport _ _ _ _ _ eq (reverse_forward d x good (i+h) n (by omega) bound t [] m st)

def backwards (d:Bool) (n:Nat):Program:=Rolling1588.reverse d 286 n++Extension270.reverse60plus1 d

theorem result (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows) (undo:Roundtrip) (d:Bool) (n x:Nat) (good:Bounds x p) (bound:286+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis)
    (pair:Paired d x a ref (rows x))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 225 (61+n)) [] (pullState (OB5.sig 224) raw))):
    run (backwards d n) m a=run (Rolling1588.reverse d 225 (61+n)) m ref:=by
  have h:=pair.through (Rolling1588.reverse d 286 n) (fun q hq=>(safe d 286 n (by decide) bound q hq).2) m
  have pools:=pool_run (PartialSites.pool_old d 286 n (by decide) bound) agree m
  simp only [StairRestSupport.forward_append d 61 225 n,run_append,run_take,List.drop_nil] at pools
  rw [tail_cancel d x 225 61 n good (by decide) bound raw stage m] at pools
  simp only [backwards,StairRestSupport.reverse_append d 61 225 n,run_append,run_take]
  apply inner rows law undo d x good raw _ _ _ stage h
  unfold stock
  exact pools

end ECDSAAdd.Entrant.StairPacket.Extension270.BackWindow

namespace ECDSAAdd.Entrant.StairPacket.Extension270.PlacedBack
open Arithmetic MappedCompressed Secp256k1 WideReference Banks Suffix StockWalkWindow InverseReplay FlagEntry
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Extension270.reverse60plus1
theorem pull {d x a s rows} (h:Paired d x a s rows):
    Paired d x (pullState Stair44WalkMap.rest a) (pullState Stair44WalkMap.rest s) rows:=by
  refine ⟨⟨h.equality.1,?_⟩,h.labels,?_,?_⟩
  · intro q off
    apply h.equality.2
    intro hit
    obtain ⟨b,j,atSite⟩:=WalkForward.bank_rep _ hit
    have eq:siteAt b j=q:=Stair44WalkMap.rest.injective ((WalkForward.bank_fixed b j).trans atSite)
    exact off (eq ▸ (chart b j).2.2.2)
  · intro b j
    change a.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [WalkForward.bank_fixed]
    exact h.custom b j
  · intro b j
    change s.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [WalkForward.bank_fixed]
    exact h.stock b j
def R (P:Program):Program:=renameProgram Stair44WalkMap.rest P
def remaining (d:Bool):Program:=R (Rolling1588.reverse d 16 209)++renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)
theorem split (d:Bool) (n:Nat):Caller.backward d n=R (BackWindow.backwards d n)++remaining d:=by
  simp only [Caller.backward,BackWindow.backwards,R,remaining,renameProgram,List.map_append,List.append_assoc]
theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.backward d (270+n)=R (Rolling1588.reverse d 225 (61+n))++remaining d:=by
  have e:=StairRestSupport.reverse_append d 209 16 (61+n)
  change Rolling1588.reverse d 16 (209+(61+n))=Rolling1588.reverse d 225 (61+n)++Rolling1588.reverse d 16 209 at e
  rw [show 270+n=209+(61+n) by omega]
  simp only [remaining,Stair44WalkRun.backward,e,R,renameProgram,List.map_append,List.append_assoc]

theorem backward (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows) (undo:BackWindow.Roundtrip) (d:Bool) (n x:Nat) (good:Bounds x p) (bound:286+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis)
    (pair:Paired d x a ref (rows x))
    (agree:poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 225 (61+n)) [] (pullState (OB5.sig 224) raw))):
    ∃old,run (Caller.backward d n) m a=run (Stair44WalkRun.backward d (270+n)) old ref:=by
  let A:=R (BackWindow.backwards d n)
  let B:=R (Rolling1588.reverse d 225 (61+n))
  let tail:=m.drop (measurementCount A)
  have eq:run A m a=run B m ref:=by
    apply MappedCompressed.pullState_perm_injective Stair44WalkMap.rest
    simp only [A,B,R,run_rename _ Stair44WalkMap.rest.injective]
    exact BackWindow.result rows law undo d n x good bound raw _ _ m stage (pull pair) agree
  refine ⟨pfx (measurementCount B) m++tail,?_⟩
  rw [split,old_split,Stair44PointSecond.joinRecords]
  rw [run_append,run_take]
  exact congrArg (run (remaining d) tail) eq

end ECDSAAdd.Entrant.StairPacket.Extension270.PlacedBack

namespace ECDSAAdd.Entrant.StairPacket.Extension270.WalkEndpoints
open Arithmetic MappedCompressed Secp256k1 WideReference Banks WalkForward InverseReplay StockWalkPrefix
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Rolling1588.Integer.regularForward

theorem bounds (x:Nat) (nz:0 < x) (lt:x<p):Bounds x p:=by
  obtain ⟨h,odd,cap,cop⟩:=StackOB5.prime_facts x nz lt
  exact ⟨h,nz,odd,cap,by norm_num [p],lt,cop⟩
theorem opened (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows) (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (bound:286+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Paired d x (run (Caller.forward d n) m a) (run (Stair44WalkRun.forward d (270+n)) m a) (rows x):=
  WalkForward.forward rows law d n x (bounds x nz lt) bound s a m stage input

theorem rest_pool (q:Wire) (h:q∈pool):Stair44WalkMap.rest q∈pool:=by
  simp only [Stair44WalkMap.rest,Stair44WalkMap.shared,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | exact h | exact List.mem_toFinset.mpr (OB5.base_pool _ (by decide))
theorem fixed_old (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:286+n∈[425,505,506]) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (m:List Bool):
    let v:=run (Rolling1588TickGap.forward d 1 (285+n)) m s
    pullState Stair44WalkMap.rest v=v:=by
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have num:15+(270+n)=285+n:=by omega
  have cut:1+(15+(270+n))∈[425,505,506]:=by simpa only [show 1+(15+(270+n))=286+n by omega] using atCut
  have one:=Stair44WalkRun.forward_run d (270+n) x good.nonzero good.small s a m stage input
  have two:=Stair44WalkCuts.forward_done d (270+n) x cut good.nonzero good.small s a m stage input
  rw [two,num] at one
  exact one

theorem decompose (d:Bool) (x n:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:286+n≤512):
    let raw:=regular d s []
    run (Rolling1588TickGap.forward d 1 (285+n)) m s=
      run (Rolling1588TickGap.forward d 225 (61+n)) [] (pullState (OB5.sig 224) raw):=by
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  have same:=StockWalkWindow.steady d x good 1 (285+n) (by decide) (by omega) s m [] stage
  rw [show 1-1=0 from rfl,init] at same
  have cut:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 224 1 (by decide) (by decide) s [] stage
  rw [show 1-1=0 from rfl,init] at cut
  have shape:285+n=224+(61+n):=by omega
  rw [same,shape,StairRestSupport.forward_append d 224 1 (61+n),run_append,run_take,List.drop_nil,cut]
  rfl

theorem move {f:Wire→Wire} (a b c:State) (mem:∀q∈pool,f q∈pool) (eq:poolEq a b)
    (fixed:pullState f b=b) (next:b=c):poolEq (pullState f a) c:=by
  intro q hq
  exact (eq _ (mem q hq)).trans ((congrArg (fun s:State=>s.basis q) fixed).trans (congrArg (fun s:State=>s.basis q) next))
theorem endpoint_stage (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (stage:Rolling1588.Integer.Stage base d x p 1 s.basis):
    Rolling1588.Integer.Stage base d x p 225 (regular d s []).basis:=BackWindow.stageAt d x good 1 224 (by decide) s [] stage
theorem endpoint_pool (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:286+n∈[425,505,506]) (s ref:State) (enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:286+n≤512)
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (285+n)) enc s)):
    poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 225 (61+n)) [] (pullState (OB5.sig 224) (regular d s []))):=
  move _ _ _ rest_pool agree (fixed_old d n x good atCut s stage enc) (decompose d x n good s enc stage bound)
theorem closed_of_laws (rows:Nat→Banks.Bank→Nat) (law:WalkForward.Binding rows) (undo:BackWindow.Roundtrip) (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:286+n∈[425,505,506]) (one a ref:State) (m enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (pair:Paired d x a ref (rows x))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (285+n)) enc one)):
    ∃old,run (Caller.backward d n) m a=run (Stair44WalkRun.backward d (270+n)) old ref:=by
  have good:=bounds x nz lt
  have bound:286+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  exact PlacedBack.backward rows law undo d n x good bound (regular d one []) a ref m (endpoint_stage d x good one stage)
    pair (endpoint_pool d n x good atCut one ref enc stage bound agree)

end ECDSAAdd.Entrant.StairPacket.Extension270.WalkEndpoints


-- Append after selected Main, the four-bank Field fragment, the concrete row
-- binding and roundtrip, the backward replay, StartStates, and CallerSupport.
-- No final caller assumption is introduced here.

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Banks Suffix StairArchiveRelease FieldMask CodecBitSliceVerify ArchivePortAction FieldJourney
set_option maxRecDepth 25000
set_option maxHeartbeats 3200000
def Fixed (f:Wire→Wire):Prop:=∀b i,f (siteAt b i)=siteAt b i
theorem archive_pre {f:Wire→Wire} (inj:Function.Injective f) (fix:Fixed f) (q:Wire) (off:q∉archives):f q∉archives:=by
  intro hit
  obtain ⟨b,i,e⟩:=WalkForward.bank_rep _ hit
  have eq:=inj ((fix b i).trans e)
  exact off (eq ▸ (chart b i).2.2.2)
theorem pairPull (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) {d x rows a r}
    (pair:Paired d x a r rows):Paired d x (pullState f a) (pullState f r) rows:=by
  refine ⟨⟨pair.equality.1,fun q h=>pair.equality.2 _ (archive_pre inj fix q h)⟩,pair.labels,?_,?_⟩
  · intro b i
    change a.basis (f (siteAt b i))=_
    rw [fix];exact pair.custom b i
  · intro b i
    change r.basis (f (siteAt b i))=_
    rw [fix];exact pair.stock b i
theorem fitsPull (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) {rows cs a r}
    (ff:Fits rows cs a r):Fits rows cs (pullState f a) (pullState f r):=by
  refine ⟨ff.phase,?_,?_⟩
  · intro q off
    exact ff.outside _ (by rw [whole] at off ⊢;exact archive_pre inj fix q off)
  · intro j hj q hq
    obtain ⟨b,rfl⟩:=idAt _ hj
    let i:Fin 16:=⟨q,Finset.mem_range.mp hq⟩
    have fx:f (fieldPort (groupId b) q)=fieldPort (groupId b) q:=by change f (fieldPort (groupId b) i.val)=_;rw [field_ports,fix]
    change a.basis (f (fieldPort (groupId b) q))=_
    rw [fx];exact ff.bytes _ hj _ hq

theorem completeCode (d:Bool) (b:Bank):
    (finalCode d (plan d) (initialCode d) (groupId b)).take 16=(code (!d)).take 16:=by
  have toward:∀(d:Bool)(b:Bank),(finalCode d (plan d) (initialCode d) (groupId b)).take 16=
      (outputCols (StairArchiveNativeCut.leave (!d))).take 16:=by decide +kernel
  rw [toward]
  cases d
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.2.trans ((enterCode true (groupId b)).symm)
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.1.trans ((enterCode false (groupId b)).symm)

theorem pairFinished {d x rows a r} (ff:Fits (fieldRows rows) (finalCode d (plan d) (initialCode d)) a r)
    (labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b))
    (old:∀b,nativeAt (!d) b (rows b) r):Paired (!d) x a r rows:=by
  refine ⟨⟨ff.phase,fun q h=>ff.outside q (whole.symm ▸ h)⟩,labels,?_,old⟩
  intro b i
  have pick:∀b:Bank,groupId b∈bankIds:=by decide +kernel
  have v:=ff.bytes _ (pick b) i.val (Finset.mem_range.mpr i.isLt)
  rw [field_ports b i,rowsAt] at v
  exact v.trans (StairArchiveHandoff.wires_eq _ _ 16 (completeCode d b) i.val _ i.isLt)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Banks Suffix FieldMask CodecBitSliceVerify
open StairOuterPlacement StairField2V3Seg
set_option maxRecDepth 25000
set_option maxHeartbeats 1800000
attribute [local irreducible] run
def fieldEquiv:Equiv.Perm Wire:=⟨fieldPlace,fieldPlaceInv,inv_fieldPlace,fieldPlace_inv⟩
theorem fieldFix:Fixed fieldEquiv:=by unfold Fixed; decide +kernel
theorem phaseFix:Fixed Rolling1588Lifetime.phaseHost:=host_ports
theorem inverseFix {f:Equiv.Perm Wire} (fixed:Fixed f):Fixed f.symm:=by
  intro b i
  exact f.injective (by rw [Equiv.apply_symm_apply,fixed b i])
theorem pairUnpull (f:Equiv.Perm Wire) (fix:Fixed f) {d x rows a r}
    (pair:Paired d x (pullState f a) (pullState f r) rows):Paired d x a r rows:=by
  have h:=pairPull f.symm f.symm.injective (inverseFix fix) pair
  rwa [Stair44PlacedHead.unpull,Stair44PlacedHead.unpull] at h
theorem fitsUnpull (f:Equiv.Perm Wire) (fix:Fixed f) {rows cs a r}
    (ff:Fits rows cs (pullState f a) (pullState f r)):Fits rows cs a r:=by
  have h:=fitsPull f.symm f.symm.injective (inverseFix fix) ff
  rwa [Stair44PlacedHead.unpull,Stair44PlacedHead.unpull] at h
theorem hosted {rows cs A B a r m n}
    (ff:Fits rows cs (run A m (pullState fieldEquiv a)) (run B n (pullState fieldEquiv r))):
    Fits rows cs (run (renameProgram fieldEquiv A) m a) (run (renameProgram fieldEquiv B) n r):=by
  apply fitsUnpull fieldEquiv fieldFix
  rwa [run_rename _ fieldEquiv.injective,run_rename _ fieldEquiv.injective]
theorem placedShape (A:Program):StairSchedule.fieldRename (renameProgram Prefix1590.borrow A)=renameProgram fieldEquiv A:=by
  simp only [StairSchedule.fieldRename,StairSchedule.parityRename,renameProgram_comp]
  rfl
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed FieldMask
set_option maxRecDepth 6000
attribute [local irreducible] run measurementCount
/-- Change reference tapes separately at the field window and reuse the actual measurement suffix. -/
def Relates (A B:Program) (start finish:State→State→Prop):Prop:=
  ∀a r,start a r→∀m,∃n,finish (run A m a) (run B n r)
theorem compose {A B C D:Program} {src mid finish:State→State→Prop}
    (p:Relates A B src mid) (q:Relates C D mid finish):Relates (A++C) (B++D) src finish:=by
  intro a r h m
  obtain ⟨u,hm⟩:=p a r h m
  obtain ⟨v,hf⟩:=q _ _ hm (m.drop (measurementCount A))
  refine ⟨FieldJourney.joinTapes B u v,?_⟩
  rw [FieldJourney.joined,run_append,run_take]
  exact hf

theorem pass {rows cs P} (clear:avoids P allBanks):Relates P P (Fits rows cs) (Fits rows cs):=by
  intro a r h m
  exact ⟨m,plain P rows cs m a r h clear⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.MiddleContract
open Arithmetic MappedCompressed Rolling1588Lifetime Secp256k1 StairConcreteAssembly
open KernelPrograms Banks
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

def divHead:=divBefore++renameProgram phaseHost Stair44Outer.reverseEnd
def oldDivHead:=(Stair44Kernel.divLead++Stair44Kernel.fieldD)++renameProgram phaseHost Stair44Outer.reverseEnd
def mulHead:=mulBefore
def oldMulHead:=Stair44Kernel.beforeX

def entry:Prop:=∀{t:State} (F:EntryFrame t) (m:List Bool),
  ∃old,Paired false F.x (pullState phaseHost (run divHead m t))
    (pullState phaseHost (run oldDivHead old t)) (ConcreteRows.rows F.x)
def exit:Prop:=∀(k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool),
  ∃old,Paired true F.x (pullState phaseHost (run mulHead m t))
    (pullState phaseHost (run oldMulHead old t)) (ConcreteRows.rows F.x)

theorem div_head_split:KernelPrograms.division=divHead++renameProgram phaseHost
    (Caller.backward false 220++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [KernelPrograms.division,divAfter,divHead,Six505.rename_append,List.append_assoc]
theorem old_div_head_split:Stair44Kernel.division=oldDivHead++renameProgram phaseHost
    (Stair44WalkRun.backward false 490++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [Stair44Kernel.division,oldDivHead,Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,Six505.rename_append,List.append_assoc]
theorem mul_head_split (k:Nat):KernelPrograms.multiplication k=mulHead++renameProgram phaseHost
    (Caller.backward true 139++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
theorem old_mul_head_split (k:Nat):Stair44Kernel.multiplication k=oldMulHead++renameProgram phaseHost
    (Stair44WalkRun.backward true 409++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
end ECDSAAdd.Entrant.StairPacket.Extension270.MiddleContract
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.StockHead
open Arithmetic MappedCompressed Secp256k1 WideReference Stair44Kernel Rolling1588Lifetime StairConcreteAssembly
open InverseReplay MiddleContract
set_option maxRecDepth 17000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount renameProgram Rolling1588TickGap.forward Rolling1588.Integer.regularForward

theorem shapeD:StairSchedule.firstPhase checkpointPrimitives=openS true 409++checkpointPrimitives.firstPack:=by
  simp only [openS,StairSchedule.firstPhase,StairSchedule.stackForward6,List.append_assoc]
theorem shapeM:Rolling1588TickGap.firstPhase false=openS false 489++finishM:=by
  simp only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,openS,finishM,List.append_assoc]

theorem leadD {t:State} (F:EntryFrame t) (m:List Bool):
    run divLead m t=run (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) m t:=by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_entry F,shapeD]
  exact with_tail true 409 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t (StairField13V3Clean.entryInput F) _ m
theorem leadM (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    run mulLead m t=run StairField2V3Replay.exitReferenceOpening m t:=by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [mulLead,StairField2V3Replay.exitReferenceOpening,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,
    StairField13V3Clean.pull_phaseHost_exit F,shapeM]
  exact with_tail false 489 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t F.input _ m

theorem beforeD {t:State} (F:EntryFrame t) (m:List Bool):
    run (divLead++fieldD) m t=run (Stair44DivisionCut.beforeClose checkpointPrimitives hostPlan) m t:=by
  have cnt:measurementCount divLead=measurementCount (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)):=by
    rw [shapeD,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]
  change run (_++_) m t=run (_++_) m t
  rw [run_append,run_append,leadD F,cnt]
theorem roundHead (A B V W:Program) (s:State) (m:List Bool) (cnt:measurementCount A=measurementCount B)
    (same:∀u,run A u s=run B u s):run ((A++V)++W) m s=run ((B++V)++W) m s:=by
  simp only [run_append,measurementCount_append,cnt,same]
theorem countM:measurementCount mulLead=measurementCount StairField2V3Replay.exitReferenceOpening:=by
  rw [StairField2V3Replay.exitReferenceOpening,shapeM,mulLead,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]
theorem beforeM (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):run beforeX m t=run stockBeforeX m t:=
  roundHead mulLead StairField2V3Replay.exitReferenceOpening (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (renameProgram phaseHost checkpointPrimitives.firstUnpack) t m countM (leadM k F)

def Endpoint (d:Bool) (x n:Nat) (ref:State):Prop:=
  ∃s enc,Rolling1588.Integer.Stage base d x p 1 s.basis ∧ poolEq ref (run (Rolling1588TickGap.forward d 1 n) enc s)
theorem mul_endpoint (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):Endpoint true F.x 424 (pullState phaseHost (run oldMulHead m t)):=by
  change Endpoint true F.x 424 (pullState phaseHost (run beforeX m t))
  rw [beforeM k F,stockBeforeX,run_append]
  obtain ⟨s,enc,st,eq⟩:=Stair44MultiplyCut.pool k F _ _
  exact ⟨s,enc,Rolling1588.Integer.stage_one base true F.x p s st,fun q _=>congrArg (fun u:State=>u.basis q) eq⟩

private theorem transfer {v old target:State} (e:pullState phaseHost old=target)
    (h:v.phase=old.phase ∧ ∀q∈skywalkPoolWires base,v.basis q=old.basis q):
    (pullState phaseHost v).phase=target.phase ∧ ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=target.basis q:=by
  subst target
  exact ⟨h.1,fun q hq=>h.2 _ (Stair44DivTerm.host_pool q hq)⟩
theorem div_pool {t:State} (F:EntryFrame t) (m:List Bool):
    let v:=run (divLead++fieldD) m t
    let want:=run (Rolling1588TickGap.firstPhase false) [] t
    (pullState phaseHost v).phase=want.phase ∧ ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=want.basis q:=by
  dsimp only
  rw [beforeD F]
  have first:=StairLoanField7Values.first_phase_hosted false F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt t [] (StairField13V3Clean.entryInput F)
  have before:=run_rename phaseHost phaseHost.injective (Rolling1588TickGap.firstPhase false) [] t
  change pullState phaseHost (run (renameProgram phaseHost (Rolling1588TickGap.firstPhase false)) [] t)=_ at before
  rw [first,StairField13V3Clean.pull_phaseHost_entry F] at before
  exact transfer before (Stair44DivisionCut.pool F m)

theorem regular_endpoint (d:Bool) (x i:Nat) (nz:0 < x) (lt:x<p) (bound:1+i≤512) (one raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (same:∀q∈skywalkPoolWires base,raw.basis q=(run (Rolling1588.Integer.regularForward base d 1 i) [] one).basis q):
    Endpoint d x i (pullState (OB5.sig i) raw):=by
  have eq:=Rolling1588TickGap.forward_gen d x nz lt i 1 (by decide) bound one [] stage
  have init:pullState (OB5.sig 0) one=one:=by
    apply State.extensionality _ one
    · rfl
    · funext q;exact congrArg one.basis (OB5.sig_zero q)
  rw [show 1-1=0 from rfl,init,show 1+i-1=i by omega] at eq
  refine ⟨one,[],stage,?_⟩
  rw [eq]
  intro q hq
  exact same _ (Stair44DivTerm.sig_pool i (by omega) q (List.mem_toFinset.mp hq))

def beforeDiv:Program:=divLead++fieldD
theorem reverseShape:Stair44Outer.reverseEnd=skywalkArithmeticClear base++Stair44DivTerm.head:=by
  simp only [Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,List.append_assoc]
attribute [local irreducible] Endpoint Stair44Outer.reverseEnd SkywalkArithmeticInput FrontierEntry1591Native.forward
private theorem gather (d:Bool) (x i:Nat) (nz:0 < x) (lt:x<p) (bound:1+i≤512) (one out:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (result:∃r:State,out=pullState (OB5.sig i) r ∧ ∀q∈skywalkPoolWires base,r.basis q=(run (Rolling1588.Integer.regularForward base d 1 i) [] one).basis q):
    Endpoint d x i out:=by
  obtain ⟨r,rfl,eq⟩:=result
  exact regular_endpoint d x i nz lt bound one r stage eq
private theorem afterTick (d:Bool) (x y:Nat) (nz:0 < x) (lt:x<p) (hn:(skywalkSharedWires base).Nodup)
    (s:State) (input:SkywalkArithmeticInput base x y s.basis):
    Rolling1588.Integer.Stage base d x p 1 (run (FrontierEntry1591Native.forward base) [] s).basis:=
  Rolling1588.Integer.stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y nz lt s [] input)
theorem reverseRaw (x y:Nat) (nz:0 < x) (lt:x<p) (hn:(skywalkSharedWires base).Nodup) (s z:State)
    (input:SkywalkArithmeticInput base x y s.basis) (m:List Bool)
    (hp:z.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (hb:∀q∈skywalkPoolWires base,z.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q):
    Endpoint false x 505 (run Stair44Outer.reverseEnd m z):=by
  rw [reverseShape]
  exact gather false x 505 nz lt (by decide) _ _ (afterTick false x y nz lt hn s input)
    (Stair44DivTerm.reverse_input x y nz lt hn s z input hp hb m)

theorem divState (t:State) (m:List Bool):pullState phaseHost (run oldDivHead m t)=
    run Stair44Outer.reverseEnd (m.drop (measurementCount beforeDiv)) (pullState phaseHost (run beforeDiv (m.take (measurementCount beforeDiv)) t)):=by
  rw [oldDivHead,run_append,run_rename _ phaseHost.injective]
  rfl
theorem div_endpoint {t:State} (F:EntryFrame t) (m:List Bool):Endpoint false F.x 505 (pullState phaseHost (run oldDivHead m t)):=by
  rw [divState]
  have h:=div_pool F (m.take (measurementCount beforeDiv))
  exact reverseRaw F.x _ F.x_pos F.x_lt F.sharedNodup t _ (StairField13V3Clean.entryInput F) _ h.1 h.2

end ECDSAAdd.Entrant.StairPacket.Extension270.StockHead
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.EndBytes
open Arithmetic MappedCompressed Secp256k1 WideReference Banks InverseReplay StockHead MiddleContract
open Rolling1588Lifetime
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward

structure Native (d:Bool) (x:Nat) (ref:State):Prop where
  ids:∀b,ConcreteRows.rows x b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (ConcreteRows.rows x b)
  bytes:∀b,nativeAt d b (ConcreteRows.rows x b) ref

theorem ofEndpoint (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:286+n∈[425,505,506]) (ref:State)
    (h:Endpoint d x (285+n) ref):Native d x ref:=by
  obtain ⟨s,enc,stage,eq⟩:=h
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have bound:286+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  have pair:=WalkEndpoints.opened ConcreteRows.rows ConcreteRows.binding d n x nz lt bound s a enc stage input
  have cut:1+(15+(270+n))∈[425,505,506]:=by simpa only [show 1+(15+(270+n))=286+n by omega] using atCut
  have same:=Stair44WalkCuts.forward_done d (270+n) x cut nz lt s a enc stage input
  rw [show 15+(270+n)=285+n by omega] at same
  refine ⟨pair.labels,?_⟩
  intro b j
  have loc:siteAt b j∈pool:=archives_pool _ (chart b j).2.2.2
  exact (eq _ loc).trans ((congrArg (fun s:State=>s.basis (siteAt b j)) same.symm).trans (pair.stock b j))

theorem div_native {s:State} (F:StairConcreteAssembly.EntryFrame s) (m:List Bool):
    Native false F.x (pullState phaseHost (run oldDivHead m s)):=
  ofEndpoint false 220 F.x F.x_pos F.x_lt (by decide) _ (div_endpoint F m)
theorem mul_native (k:Nat) {s:State} (F:StairConcreteAssembly.ExitFrame k s) (m:List Bool):
    Native true F.x (pullState phaseHost (run oldMulHead m s)):=
  ofEndpoint true 139 F.x F.x_pos F.x_lt (by decide) _ (mul_endpoint k F m)

theorem Native.pair {d x a ref} (old:Native d x ref) (eq:Suffix.Same a ref)
    (bytes:∀b,Kept (ports b) d (ConcreteRows.rows x b) a):Paired d x a ref (ConcreteRows.rows x):=
  ⟨eq,old.ids,bytes,old.bytes⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.EndBytes
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.MiddlePieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime FlagEntry Banks
open MiddleContract StartStates
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount renameProgram

def divSpan:=renameProgram phaseHost checkpointPrimitives.firstPack++
    Caller.entryFieldHosted checkpointPrimitives++renameProgram phaseHost Stair44Outer.reverseEnd
def oldDivSpan:=renameProgram phaseHost checkpointPrimitives.firstPack++
    StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan++renameProgram phaseHost Stair44Outer.reverseEnd
def mulSpan:=renameProgram phaseHost Stair44Outer.forwardEnd++
    Caller.exitFieldHosted checkpointPrimitives++renameProgram phaseHost checkpointPrimitives.firstUnpack
def oldMulSpan:=renameProgram phaseHost Stair44Outer.forwardEnd++
    StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan++renameProgram phaseHost checkpointPrimitives.firstUnpack

theorem divisionShape:divHead=opening true 139++divSpan ∧ oldDivHead=original true 139++oldDivSpan:=by
  simp only [divHead,KernelPrograms.divBefore,divSpan,opening,oldDivHead,Stair44Kernel.divLead,Stair44Kernel.fieldD,original,oldDivSpan,Six505.rename_append,List.append_assoc]
  constructor <;> trivial
theorem multiplicationShape:mulHead=opening false 219++mulSpan ∧ oldMulHead=original false 219++oldMulSpan:=by
  simp only [mulHead,KernelPrograms.mulBefore,mulSpan,opening,oldMulHead,Stair44Kernel.beforeX,Stair44Kernel.mulLead,original,oldMulSpan,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]
  constructor <;> trivial

def Related (d:Bool) (x:Nat) (a ref:State):Prop:=Paired d x (pullState phaseHost a) (pullState phaseHost ref) (ConcreteRows.rows x)

theorem division (H:∀{s:State} (F:EntryFrame s) (m t:List Bool),
    let a:=run (opening true 139) m s
    let b:=run (original true 139) m s
    Related true F.x a b → ∃old, Related false F.x (run divSpan t a) (run oldDivSpan old b)):
    MiddleContract.entry:=by
  intro s F m
  let A:=opening true 139
  let B:=original true 139
  obtain ⟨old,rel⟩:=H F m (m.drop (measurementCount A)) (StartStates.division ConcreteRows.rows ConcreteRows.binding F m)
  refine ⟨pfx (measurementCount B) m++old,?_⟩
  rw [divisionShape.1,divisionShape.2,Stair44PointSecond.joinRecords,run_append,run_take]
  exact rel

theorem multiplication (H:∀k {s:State} (F:ExitFrame k s) (m t:List Bool),
    let a:=run (opening false 219) m s
    let b:=run (original false 219) m s
    Related false F.x a b → ∃old, Related true F.x (run mulSpan t a) (run oldMulSpan old b)):
    MiddleContract.exit:=by
  intro k s F m
  let A:=opening false 219
  let B:=original false 219
  obtain ⟨old,rel⟩:=H k F m (m.drop (measurementCount A)) (StartStates.multiplication ConcreteRows.rows ConcreteRows.binding k F m)
  refine ⟨pfx (measurementCount B) m++old,?_⟩
  rw [multiplicationShape.1,multiplicationShape.2,Stair44PointSecond.joinRecords,run_append,run_take]
  exact rel
end ECDSAAdd.Entrant.StairPacket.Extension270.MiddlePieces
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.KernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly Banks
open MiddleContract StockHead
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount wires renameProgram

theorem tail (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (cut:286+n∈[425,505,506])
    (a ref:State) (P:Program) (m:List Bool)
    (pair:Paired d x (pullState phaseHost a) (pullState phaseHost ref) (ConcreteRows.rows x))
    (known:Endpoint d x (285+n) (pullState phaseHost ref)):
    ∃old,run (renameProgram phaseHost (Caller.backward d n++P)) m a=
      run (renameProgram phaseHost (Stair44WalkRun.backward d (270+n)++P)) old ref:=by
  obtain ⟨s,enc,stage,ag⟩:=known
  obtain ⟨old,eq⟩:=WalkEndpoints.closed_of_laws ConcreteRows.rows ConcreteRows.binding Extension270.roundtrip d n x nz lt cut s _ _ m enc stage pair ag
  let A:=Caller.backward d n
  let B:=Stair44WalkRun.backward d (270+n)
  let suffix:=m.drop (measurementCount A)
  refine ⟨pfx (measurementCount B) old++suffix,?_⟩
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,Stair44PointSecond.joinRecords]
  rw [run_append,run_take]
  exact congrArg (run P suffix) eq

theorem compose {A B P Q:Program} {s:State} {m old:List Bool}
    (h:∃r,run P (m.drop (measurementCount A)) (run A m s)=run Q r (run B old s)):
    ∃r,run (A++P) m s=run (B++Q) r s:=by
  obtain ⟨post,close⟩:=h
  refine ⟨pfx (measurementCount B) old++post,?_⟩
  rw [Stair44PointSecond.joinRecords,run_append,run_take]
  exact close
theorem div_run (geometry:MiddleContract.entry) {t:State} (F:EntryFrame t) (m:List Bool):
    ∃old,run KernelPrograms.division m t=run Stair44Kernel.division old t:=by
  obtain ⟨head,v⟩:=geometry F m
  rw [div_head_split,old_div_head_split]
  exact compose (old:=head) (tail false 220 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (div_endpoint F head))

theorem mul_run (geometry:MiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    ∃old,run (KernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) old t:=by
  obtain ⟨head,v⟩:=geometry k F m
  rw [mul_head_split,old_mul_head_split]
  exact compose (old:=head) (tail true 139 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (mul_endpoint k F head))

theorem division_correct (geometry:MiddleContract.entry):
    FrontierEntry1591Callers.EntryCorrect KernelPrograms.division:=by
  intro hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  let F:EntryFrame t:=⟨hn,hl,ho,hf,x,Y,hx0,hx,s,input,hg,hs,phase,eq,val⟩
  obtain ⟨old,same⟩:=div_run geometry F m
  dsimp only
  rw [same]
  exact Stair44Kernel.division_correct hn hl ho hf x Y hx0 hx s t old input hg hs phase eq val

private theorem afterPull (f : Wire → Wire) (s t : State) (h : s=pullState f t) : s.phase=t.phase := by
  subst s
  rfl

private theorem afterPut (s t : State) (q : Wire) (v : Bool) (h : s=ParityEven.put t q v) : s.phase=t.phase := by
  subst s
  rfl

private theorem correctPhase {K : Program} {k : Nat} (law : ParityXExitInverse23Kernel.ExitNegCorrect K k)
    {s : State} (F : ExitFrame k s) (m : List Bool) : (run K m s).phase=s.phase :=
  (law F.sharedNodup F.historyAbove F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s m F.input
    F.selectorG_zero F.selectorS_zero).1

theorem old_phase (k:Nat) {s:State} (F:ExitFrame k s) (m:List Bool):
    (run (Stair44Kernel.multiplication k) m s).phase=s.phase:=by
  have a := afterPull _ _ _ (Stair44Kernel.mul_run k F m)
  have b := afterPut _ _ _ _ (StairCallerReplay.hostedExit_pw Stair44Kernel.hostReplay k F.k_lt F.sharedNodup F.historyAbove
    F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s m F.input F.selectorG_zero F.selectorS_zero)
  exact a.trans (b.trans (correctPhase (ParityXExitInverse23Kernel.kernelX_correct k F.k_lt) F m))

theorem multiplication_eq (geometry:MiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    run (KernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) m t:=by
  obtain ⟨other,eq⟩:=mul_run geometry k F m
  rw [eq]
  exact State.extensionality _ _ ((old_phase k F other).trans (old_phase k F m).symm)
    (Arithmetic.run_basis_records _ _ _ _ _ rfl)
end ECDSAAdd.Entrant.StairPacket.Extension270.KernelReplay
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Suffix StairConcreteAssembly Stair44Outer Banks StairV3Primitives StairPhysicalPhase
def free (q:Wire):Bool:=!(61304553888254649221186043367116264163574295502870197045477682531254557239346288044673967228446303335126061819412774951191528261618320058797382826273299243283053287646687737827279467305426785812332843039671568512641759838052520687022316127463824971843713001623497922600531427864713580965425310541252615346411548690742068329955507580400495121606640675950961059036368214457561070879432118701921238097850656651587276429976979879311695654980509272396907364073503366391236892738398892701285401846405918087330916539961217681402406217018152876047859712:Nat).testBit q
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
theorem occupied:∀(b:Bank)(i:Fin 16),free (siteAt b i)=false:=by decide +kernel
def check (P:Program):Bool:=StairWireCheck.allSites free P
theorem checked {P:Program} (h:check P=true):∀q∈archives,q∉wires P:=by
  intro q hq used
  obtain ⟨b,j,rfl⟩:=WalkForward.bank_rep q hq
  have safe:=StairWireCheck.allSites_sound free P h _ used
  rw [occupied] at safe
  contradiction
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitFrame
open Arithmetic MappedCompressed Secp256k1 StairField13V3 StairField13V3Clean
open StairConcreteAssembly StairField2V3Replay StairField2V3Delta StairField2V3Couple
open StairField2V3ExitPlanR StairField2V3LastRecX StairPhysicalLayout StairOuterPlacement
open StairLoanExitReachX
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires renameProgram

def stockPrefix (k : Nat) : Program := (((exitPieces cp hostPlan k).take 21).map Piece.H).flatten

def Pinned (x : Nat) (ref : State) : Prop := ∃ record, FrameAt x 85 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem ofMiddle (k x : Nat) (u : State) (hu : ExitMiddleX k x u) (m : List Bool) :
    Pinned x (run XS21 m u) := by
  obtain ⟨Q, link⟩ := rch21 k x (StairOpenWiring.exitPlans k x) StairOpenWiring.half760
  obtain ⟨old,rel,reachable⟩ := link u u ⟨hu,rfl⟩ m
  exact ⟨_,FieldView.exitFrame 85 x _
    (StairField2V3ExitRec.reach_YE k x _ (reachX_E StairOpenWiring.half760 k x _ reachable)),rel.1⟩

private theorem logicalPinned (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (cut (xps k) 21) m s) := by
  rw [xcut21,run_append]
  exact ofMiddle k F.x _ ⟨s,F,rfl,_,rfl⟩ _

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) := by
  rw [hp_group false 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (k : Nat) (parts : StairField13V3Fresh.ExitClean k) :
    CutClean (ExitPre k) (cut (xps k) 21) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) :=
  parts.groupsBefore (21,0,1,84) (by simp)

private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)

private theorem logicalLoan (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Loan (run (cut (xps k) 21) m s) :=
  cutLoan (fullCutClean k (exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k)) s ⟨F⟩ m

theorem at_cut (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (stockPrefix k) m s) ∧ Loan (run (stockPrefix k) m s) := by
  have eq := Stair44HostedCut.exit k 21 s ⟨F⟩ m
  change run (stockPrefix k) m s = run (cut (xps k) 21) m s at eq
  rw [eq]
  exact ⟨logicalPinned k F m,logicalLoan k F m⟩

end ECDSAAdd.Entrant.StairPacket.Extension270.ExitFrame
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Suffix StairConcreteAssembly Stair44Outer Banks
open StairV3Primitives StairPhysicalPhase StairPhysicalLayout
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
attribute [local irreducible] wires
def Clear (P:Program):Prop:=∀q∈archives,q∉wires P
theorem both {A B:Program} (a:Clear A) (b:Clear B):Clear (A++B):=by
  intro q h
  rw [wires_append,Finset.mem_union]
  exact fun hit=>hit.elim (a q h) (b q h)
private theorem rows87 {P:Program} (sub:∀q∈wires P,q∈StairPhysicalPrimitives.rowSitesL 87):
    Clear (renameProgram phaseRelabel P):=by
  have rowFree:∀q∈StairPhysicalPrimitives.rowSitesL 87,free (phaseRelabel q)=true:=by decide +kernel
  intro q h used
  obtain ⟨b,i,rfl⟩:=WalkForward.bank_rep _ h
  rw [renameProgram_support] at used
  obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp used
  have ok:=rowFree w (sub w hw)
  rw [eq,occupied] at ok
  contradiction
private theorem orientOK:Clear (renameProgram xRelabel (StairV3Primitives.orient 425)):=checked (by decide +kernel)
private theorem packetOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.Integer.packFirst base true 425)):=checked (by decide +kernel)
private theorem unpacketOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)):=checked (by decide +kernel)
private theorem moveOK:Clear (phaseBMove):=checked (by decide +kernel)
private theorem restoreOK:Clear (phaseBReturn):=checked (by decide +kernel)
theorem firstPack_free:Clear checkpointPrimitives.firstPack:=by
  exact both (both (both orientOK packetOK) moveOK) (rows87 (StairPhysicalPrimitives.pack_rows 87 (by decide)))
theorem firstUnpack_free:Clear checkpointPrimitives.firstUnpack:=by
  exact both (both (both (rows87 (StairPhysicalPrimitives.unpack_rows 87 (by decide))) restoreOK) unpacketOK) orientOK
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def beforeParity := StairSchedule.hostedX ++ StairSchedule.fieldRename (exitLowPrefix hostPlan)
def beforeGroup := StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++ hostedGroup hostPlan false 42 98 2 ++
    StairSchedule.reverseSegment cp 22 12 490 500 ++ hostedGroup hostPlan false 37 96 2 ++
    StairSchedule.reverseSegment cp 32 22 480 490 ++ hostedGroup hostPlan false 31 93 3 ++
    StairSchedule.reverseSegment cp 47 32 465 480 ++ hostedGroup hostPlan false 23 90 3 ++
    StairSchedule.reverseSegment cp 62 47 450 465 ++ hostedGroup hostPlan false 14 85 5 ++
    StairSchedule.reverseSegment cp 87 62 425 450))
def afterGroup := StairSchedule.fieldRename (FourScratchWindow.unprefix ++
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false) (Rolling1588.placedFirstPacket false))
def leading (setup : Program) := setup ++ beforeParity ++ setup ++ beforeGroup
def field (setup group : Program) := leading setup ++ renameProgram fieldEquiv group ++ afterGroup

theorem ordinary : StairHostsSchedule.exitFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (FieldCosts.group false 1 84) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,StairHostsSchedule.exitFieldHosted,
    exitLowSuffix,exitHeadSuffix,FieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : Caller.exitFieldHosted cp =
    field FieldParity.setup (FieldCosts.group84 false) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,FieldParity.setup_eq,FieldCosts.caller_eq,Caller.exitFieldHosted,
    Caller.exitLowSuffix,Caller.exitHeadSuffix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem prefix_shape (k : Nat) : ExitFrame.stockPrefix k =
    exitReferenceOpening ++ leading StairSchedule.paritySetup := by
  simp only [ExitFrame.stockPrefix,leading,beforeParity,beforeGroup,exitPieces,List.take_succ_cons,
    List.take_zero,groupSlot,lowCommon,common,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,exitReferenceOpening,exitLowPrefix,exitHeadPrefix,
    hostedEndpoint,fieldRename_append,rename_append,List.append_assoc]

theorem cutAfter (k : Nat) {s : State} (F : ExitFrame k s) (m n : List Bool) :
    let ref := run (leading StairSchedule.paritySetup) n (run exitReferenceOpening m s)
    ExitFrame.Pinned F.x ref ∧ ExitFrame.Loan ref := by
  have h := ExitFrame.at_cut k F (FieldJourney.joinTapes exitReferenceOpening m n)
  rwa [prefix_shape,FieldJourney.joined] at h

theorem hostedGroup (x : Nat) (a r : State) (m : List Bool)
    (rows : Banks.Bank → Nat)
    (labels : ∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (Banks.tick b) x p (rows b))
    (initial : FieldMask.Fits (fieldRows rows) (FieldJourney.initialCode false) a r)
    (pinned : ExitFrame.Pinned x r) (loan : ExitFrame.Loan r) :
    FieldMask.Fits (fieldRows rows)
      (FieldJourney.finalCode false (FieldJourney.plan false) (FieldJourney.initialCode false))
      (run (renameProgram fieldEquiv (FieldCosts.group84 false)) m a)
      (run (renameProgram fieldEquiv (FieldCosts.group false 1 84))
        (FieldJourney.referenceTape false (FieldJourney.plan false) m) r) := by
  obtain ⟨record,pin,agreement⟩ := pinned
  have ids : ∀j∈FieldMask.bankIds,fieldRows rows j<63145 := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    exact (labels b).1
  have chronological : ∀j∈FieldMask.bankIds, ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j) := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    have times : ∀k : Banks.Bank, 5*groupId k-5=Banks.tick k := by decide +kernel
    rw [times]
    exact (labels b).2
  apply hosted
  exact FieldView.caller false x (fieldRows rows) ids chronological (pullState fieldEquiv a) r record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix initial) pin agreement loan
end ECDSAAdd.Entrant.StairPacket.Extension270.ExitPieces
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem clearSafe:Clear (FourScratchWindow.clearProgram):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem unprefixSafe:Clear (FourScratchWindow.unprefix):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
private theorem wipeOK:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem tickOK:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem lastBackOK:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
private theorem mergedOK:Clear (Six505.merged6):=checked (by decide +kernel)
private theorem packedOK:Clear (Six505.packP false):=checked (by decide +kernel)
private theorem afterOK:Clear (ForwardSixPlacement.after false):=checked (by decide +kernel)
theorem reverseEnd_free:Clear reverseEnd:=both (both wipeOK tickOK) lastBackOK
theorem forwardEnd_free:Clear forwardEnd:=both (both (both mergedOK packedOK) afterOK) wipeOK
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Banks Suffix StairOuterPlacement
theorem mapped {P:Program} (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) (clear:Clear P):Clear (renameProgram f P):=by
  intro q hit used
  rw [renameProgram_support] at used
  obtain ⟨v,use,eq⟩:=Finset.mem_image.mp used
  obtain ⟨b,i,rfl⟩:=WalkForward.bank_rep q hit
  have same:=inj (eq.trans (fix b i).symm)
  exact clear _ ((chart b i).2.2.2) (same ▸ use)
theorem fieldMapped {P:Program} (c:Clear P):Clear (renameProgram fieldEquiv P):=mapped _ fieldEquiv.injective fieldFix c
def noBorrow:Equiv.Perm Wire:=⟨fun q=>Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host (HostOB5.hostSwap q),
  fun q=>HostOB5.hostSwap (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host q),
  fun q=>by simp only [Equiv.swap_apply_self,HostOB5.hostSwap_invol],fun q=>by simp only [HostOB5.hostSwap_invol,Equiv.swap_apply_self]⟩
theorem noBorrowFixed:Fixed noBorrow:=by unfold Fixed;decide +kernel
theorem fieldRename_free {P:Program} (c:Clear P):Clear (StairSchedule.fieldRename P):=by
  unfold StairSchedule.fieldRename StairSchedule.parityRename
  rw [renameProgram_comp]
  exact mapped _ noBorrow.injective noBorrowFixed c
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Banks Suffix StairPhysicalLayout StairPhysicalPrimitives
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem live_rows (B:Nat) (h:B∈budgets):∀q∈rowSitesL B,free q=true:=by
  have ok:budgets.all (fun b=>(rowSitesL b).all free)=true:=by decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp ok B h)
theorem of_rows {B:Nat} (h:B∈budgets) {P:Program} (sub:∀q∈wires P,q∈rowSitesL B):Clear P:=by
  intro q hit used
  obtain ⟨b,i,rfl⟩:=WalkForward.bank_rep q hit
  have pass:=live_rows B h _ (sub _ used)
  rw [occupied] at pass
  contradiction
theorem packFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.pack B):=of_rows h (pack_rows B h)
theorem unpackFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.unpack B):=of_rows h (unpack_rows B h)
theorem tfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickForward (startFor B)):=of_rows h (tickForward_rows B h)
theorem trFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickReverse (startFor B)):=of_rows h (tickReverse_rows B h)
theorem mfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleForward (startFor B+1) (endFor B-startFor B-1)):=of_rows h (middleForward_rows B h)
theorem mrFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleReverse (startFor B+1) (StairPhysicalPrimitivesFix505.reverseEnd B-startFor B-1)):=
  of_rows h (StairPhysicalPrimitivesFix505.middleReverseFix_rows B h)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 Suffix Banks StairArchiveInactive
open StairConcreteAssembly StairHostsSchedule StairPhysicalLayout StairLoanGroupSupport
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] wires renameProgram
def src (j:Nat) (b:Bank) (i:Fin 16):Wire:=(shifted (Placement5.pi j)).symm (OB5.sig 511 (siteAt b i))
private def past (q:Wire):Bool:=((List.finRange 4).flatMap (fun b=>(List.finRange 16).map (src 85 b))).contains q
private theorem fixedSources:∀j∈List.range' 85 17,∀(b:Bank)(i:Fin 16),src j b i=src 85 b i:=by decide +kernel
private theorem tagged:∀(b:Bank)(i:Fin 16),past (src 85 b i)=true:=by decide +kernel
private theorem globals:∀q∈[base 2400,base 2409,base 2410]++Q6EndpointCell.ids.map base,past q=false:=by decide +kernel
private theorem recent:∀j∈List.range' 85 17,∀i:Fin 10,past (History5.historyMap base (5*j) i)=false:=by decide +kernel
private theorem miss (j:Nat) (hj:j∈List.range' 85 17) (b:Bank) (i:Fin 16):src j b i∉cover j:=by
  intro hit
  have yes:=tagged b i
  rw [←fixedSources j hj b i] at yes
  rcases List.mem_append.mp hit with g|hist
  · rw [globals _ g] at yes;contradiction
  · obtain ⟨k,_,eq⟩:=List.mem_map.mp hist
    rw [←eq,recent j hj k] at yes;contradiction

private theorem packetFree (d:Bool) (j:Nat) (lo:85≤j) (hi:j<102):Clear (renameProgram (OB5.sig 511) (Rolling1588.packet d j)):=by
  intro q hit use
  obtain ⟨b,i,rfl⟩:=WalkForward.bank_rep q hit
  rw [renameProgram_support] at use
  obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp use
  rw [Rolling1588.packet,renameProgram_support] at hv
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
  have geom:src j b i=w:=by simp only [src,←eq,OB5.sig_invol 511 (by decide),Equiv.symm_apply_apply]
  apply miss j (List.mem_range'_1.mpr (by omega)) b i
  rw [geom]
  exact cover_read j (Rolling1588.basePacket_readSites_support d j hi hw)

private theorem regular (d:Bool) (j n:Nat) (lo:85≤j) (hi:j+n≤102):Clear (renameProgram (OB5.sig 511) (Rolling1588.groups d j n)):=by
  induction n generalizing j with
  | zero=>intro q _;simp [Rolling1588.groups,PacketSequence.program,renameProgram,wires]
  | succ n ih=>
    have a:=packetFree d j lo (by omega)
    have b:=ih (j+1) (by omega) (by omega)
    cases d <;> simp only [Rolling1588.groups,PacketSequence.program,if_true,if_false,Bool.false_eq_true,Six505.rename_append]
    · exact both b a
    · exact both a b

theorem groups (d:Bool) (k j n:Nat) (lo:85≤j) (hi:j+n≤102) (dk:k≤68)
    (safe:∀q∈hostPlan.group d k j n,free q=true):Clear (hostedGroup hostPlan d k j n):=by
  have roles:∀q∈StairSchedule.exclusiveRoles,free q=true:=by decide +kernel
  intro q hit used
  obtain ⟨b,i,rfl⟩:=WalkForward.bank_rep q hit
  obtain host|role|inner:=StairWireCheck.rebindMany_support _ _ _ _ used
  · have ok:=safe _ host;rw [occupied] at ok;contradiction
  · have ok:=roles _ (List.mem_of_mem_drop role);rw [occupied] at ok;contradiction
  · exact regular d j n lo hi _ ((chart b i).2.2.2) (placedGroups_sub d k dk j n inner)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment425Ori:Clear (checkpointPrimitives.orient 450):=checked (by decide +kernel)
private theorem segment425P:Clear (renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450)):=checked (by decide +kernel)
private theorem segment425U:Clear (renameProgram (OB5.sig 450) (Rolling1588.unpackAtTick true 450)):=checked (by decide +kernel)
theorem forward425:Clear (StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 87 (by decide)) (tfFree 87 (by decide))) (mfFree 87 (by decide))) segment425Ori) segment425P) (packFree 62 (by decide))
theorem reverse425:Clear (StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 62 (by decide)) segment425U) segment425Ori) (mrFree 87 (by decide))) (trFree 87 (by decide))) (packFree 87 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment450Ori:Clear (checkpointPrimitives.orient 465):=checked (by decide +kernel)
private theorem segment450P:Clear (renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465)):=checked (by decide +kernel)
private theorem segment450U:Clear (renameProgram (OB5.sig 465) (Rolling1588.unpackAtTick true 465)):=checked (by decide +kernel)
theorem forward450:Clear (StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 62 (by decide)) (tfFree 62 (by decide))) (mfFree 62 (by decide))) segment450Ori) segment450P) (packFree 47 (by decide))
theorem reverse450:Clear (StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 47 (by decide)) segment450U) segment450Ori) (mrFree 62 (by decide))) (trFree 62 (by decide))) (packFree 62 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment465Ori:Clear (checkpointPrimitives.orient 480):=checked (by decide +kernel)
private theorem segment465P:Clear (renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480)):=checked (by decide +kernel)
private theorem segment465U:Clear (renameProgram (OB5.sig 480) (Rolling1588.unpackAtTick true 480)):=checked (by decide +kernel)
theorem forward465:Clear (StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 47 (by decide)) (tfFree 47 (by decide))) (mfFree 47 (by decide))) segment465Ori) segment465P) (packFree 32 (by decide))
theorem reverse465:Clear (StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 32 (by decide)) segment465U) segment465Ori) (mrFree 47 (by decide))) (trFree 47 (by decide))) (packFree 47 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment480Ori:Clear (checkpointPrimitives.orient 490):=checked (by decide +kernel)
private theorem segment480P:Clear (renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490)):=checked (by decide +kernel)
private theorem segment480U:Clear (renameProgram (OB5.sig 490) (Rolling1588.unpackAtTick true 490)):=checked (by decide +kernel)
theorem forward480:Clear (StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 32 (by decide)) (tfFree 32 (by decide))) (mfFree 32 (by decide))) segment480Ori) segment480P) (packFree 22 (by decide))
theorem reverse480:Clear (StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 22 (by decide)) segment480U) segment480Ori) (mrFree 32 (by decide))) (trFree 32 (by decide))) (packFree 32 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment490Ori:Clear (checkpointPrimitives.orient 500):=checked (by decide +kernel)
private theorem segment490P:Clear (renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500)):=checked (by decide +kernel)
private theorem segment490U:Clear (renameProgram (OB5.sig 500) (Rolling1588.unpackAtTick true 500)):=checked (by decide +kernel)
theorem forward490:Clear (StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 22 (by decide)) (tfFree 22 (by decide))) (mfFree 22 (by decide))) segment490Ori) segment490P) (packFree 12 (by decide))
theorem reverse490:Clear (StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 12 (by decide)) segment490U) segment490Ori) (mrFree 22 (by decide))) (trFree 22 (by decide))) (packFree 22 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
open StairPhysicalLayout StairTerminalV3
set_option maxRecDepth 80000
set_option maxHeartbeats 4800000
attribute [local irreducible] wires renameProgram
theorem terminalFixed:Fixed terminalPerm:=by unfold Fixed;decide +kernel
private theorem w:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem f:Clear Six505.merged6:=checked (by decide +kernel)
private theorem pk:Clear (Six505.packP true):=checked (by decide +kernel)
private theorem a:Clear (ForwardSixPlacement.after true):=checked (by decide +kernel)
private theorem t:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem k:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
theorem forwardTerm:Clear checkpointPrimitives.forwardTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both (both (both f pk) a) w)
theorem reverseTerm:Clear checkpointPrimitives.reverseTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both w (both t k))
theorem forwardLast:Clear (StairSchedule.forwardLast checkpointPrimitives):=
  both (both (both (unpackFree 12 (by decide)) (tfFree 12 (by decide))) (mfFree 12 (by decide))) forwardTerm
theorem reverseLast:Clear (StairSchedule.reverseLast checkpointPrimitives):=
  both (both (both reverseTerm (mrFree 12 (by decide))) (trFree 12 (by decide))) (packFree 12 (by decide))
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorPorts
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitStages
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open Banks StartStates MiddlePieces ExteriorPorts ExitPieces
open FieldMask FieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount

def endF := renameProgram phaseHost Stair44Outer.forwardEnd
def unpack := renameProgram phaseHost checkpointPrimitives.firstUnpack
def beginW := opening false 219 ++ endF
def beginR := original false 219 ++ endF

theorem refBegin : beginR = Stair44Kernel.mulLead := by
  simp only [beginR,original,endF,Stair44Kernel.mulLead,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]

theorem begin_pair (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃n, Paired false F.x (run beginW m s) (run beginR n s) (ConcreteRows.rows F.x) := by
  let A := opening false 219
  let B := original false 219
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [endF,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (StartStates.multiplication ConcreteRows.rows ConcreteRows.binding k F m).through _ forwardEnd_free _

theorem begin_record (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run beginR m s = run StairField2V3Replay.exitReferenceOpening m s := by
  rw [refBegin]
  exact StockHead.leadM k F m

def newP := (beginW ++ Caller.exitFieldHosted checkpointPrimitives) ++ unpack
def oldP := (beginR ++ StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++ unpack

theorem newShape : MiddleContract.mulHead = newP := by
  simp only [MiddleContract.mulHead,KernelPrograms.mulBefore,newP,beginW,opening,endF,unpack,
    KernelPrograms.openWalk,StartStates.openWalk,Six505.rename_append,List.append_assoc]
theorem oldShape : MiddleContract.oldMulHead = oldP := by
  rw [oldP,refBegin]
  rfl

end ECDSAAdd.Entrant.StairPacket.Extension270.ExitStages
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem viaFree {P : Program} (touch : ∀q∈wires P,free q=true) : Clear P := by
  intro q h used
  obtain ⟨b,i,rfl⟩ := WalkForward.bank_rep q h
  exact Bool.noConfusion ((occupied b i).symm.trans (touch _ used))

end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitReplay
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open Banks StartStates MiddlePieces ExteriorPorts ExitPieces
open FieldMask FieldJourney ExitStages
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount wires

def leadingOK : Prop := ∀ (x : Nat) (rows : Banks.Bank → Nat) (a r : State) (m : List Bool),
  Paired false x a r rows → ∃n, Paired false x (run (leading FieldParity.setup) m a)
    (run (leading StairSchedule.paritySetup) n r) rows

abbrev C0 := initialCode false
abbrev C1 := finalCode false (plan false) C0
def gW := renameProgram fieldEquiv (FieldCosts.group84 false)
def gR := renameProgram fieldEquiv (FieldCosts.group false 1 84)

def RStart (x : Nat) (rows : Banks.Bank → Nat) (s : State) (a r : State) : Prop :=
  Paired false x a r rows ∧ ∃m, r = run StairField2V3Replay.exitReferenceOpening m s
def RCut (x : Nat) (rows : Banks.Bank → Nat) (a r : State) : Prop :=
  Paired false x a r rows ∧ ExitFrame.Pinned x r ∧ ExitFrame.Loan r

private theorem beginRel (k : Nat) {s : State} (F : ExitFrame k s) :
    Relates beginW beginR (fun a r=>a=s ∧ r=s) (RStart F.x (ConcreteRows.rows F.x) s) := by
  rintro a r ⟨rfl,eq⟩ m
  subst r
  obtain ⟨n,rel⟩ := begin_pair k F m
  exact ⟨n,rel,n,begin_record k F n⟩

private theorem leadingRel (ok : leadingOK) (k : Nat) {s : State} (F : ExitFrame k s) (rows : Banks.Bank → Nat) :
    Relates (leading FieldParity.setup) (leading StairSchedule.paritySetup)
      (RStart F.x rows s) (RCut F.x rows) := by
  rintro a r ⟨pair,u,rfl⟩ m
  obtain ⟨n,h⟩ := ok _ _ _ _ m pair
  exact ⟨n,h,cutAfter k F u n⟩

private theorem windowRel (x : Nat) (rows : Banks.Bank → Nat) :
    Relates gW gR (RCut x rows) (Fits (fieldRows rows) C1) := by
  rintro a r ⟨pair,pin,loan⟩ m
  exact ⟨_,hostedGroup x a r m rows pair.labels (fits pair) pin loan⟩

private theorem template (A P G T U : Program) :
    (A ++ ((P ++ G) ++ T)) ++ U = (((A ++ P) ++ G) ++ (T ++ U)) := by
  simp only [List.append_assoc]

private theorem newPath : MiddleContract.mulHead =
    (((beginW ++ leading FieldParity.setup) ++ gW) ++ (afterGroup ++ unpack)) := by
  rw [newShape,newP,corrected]
  exact template _ _ _ _ _
private theorem oldPath : MiddleContract.oldMulHead =
    (((beginR ++ leading StairSchedule.paritySetup) ++ gR) ++ (afterGroup ++ unpack)) := by
  rw [oldShape,oldP,ordinary]
  exact template _ _ _ _ _

theorem exit (leadingLaw : leadingOK) (endClear : Clear (afterGroup ++ unpack)) : MiddleContract.exit := by
  intro k s F m
  have keep := pass (rows:=fieldRows (ConcreteRows.rows F.x)) (cs:=C1) (P:=afterGroup ++ unpack) (fun q h=>endClear q (whole ▸ h))
  have total := compose (compose (compose (beginRel k F) (leadingRel leadingLaw k F _)) (windowRel _ _)) keep
  obtain ⟨n,out⟩ := total s s ⟨rfl,rfl⟩ m
  rw [←newPath,←oldPath] at out
  have paired := fitsPull phaseHost phaseHost.injective phaseFix out
  have native := EndBytes.mul_native k F n
  exact ⟨n,pairFinished paired native.ids native.bytes⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.ExitReplay
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem convert {P Q : Program}
    (env : wires P ⊆ wires Q ∪ StairBoundaryLoan.converterHosts.toFinset)
    (rec : wires Q ⊆ StairBoundaryLoan.converterLayout760.wires.toFinset) : Clear P := by
  have ok : (StairBoundaryLoan.converterLayout760.wires ++ StairBoundaryLoan.converterHosts).all free=true := by decide +kernel
  apply viaFree
  intro q hq
  apply List.all_eq_true.mp ok
  rcases Finset.mem_union.mp (env hq) with l|r
  · exact List.mem_append_left _ (List.mem_toFinset.mp (rec l))
  · exact List.mem_append_right _ (List.mem_toFinset.mp r)

theorem canon : Clear StairConcrete.bestLoans.canon :=
  convert StairBoundaryLoan.canon760Loan_envelope (by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).2)
theorem center : Clear StairConcrete.bestLoans.center :=
  convert StairBoundaryLoan.center760Loan_envelope (by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).1)

theorem copy : Clear HalfFieldOB5.copyN := ExteriorPorts.checked (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem mulEndpoint : Clear (hostedEndpoint hostPlan false 68) := by
  have ok : StairSiteEasy.multEndL.all (fun q=>free (OB5.sig 511 q))=true := by decide +kernel
  apply viaFree
  intro q h
  have e : StairConcrete.bestLoans.endPacket false 68=StairEndpointLoan44.endPacket760Loan44 false := by
    simp only [StairConcrete.bestLoans,StairConcrete.endPacket,Bool.false_eq_true,if_false,if_true]
  rw [hostedEndpoint,StairSchedule.placedEndPacket,e,renameProgram_support] at h
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
  exact List.all_eq_true.mp ok q (StairSiteEasy.endPacket760_false_mem q (StairEndpointLoan44.endPacket760Loan44_support hq))

private def outward (q : Wire) := OB5.sig 511 (Equiv.swap (base 760) (base 717) (shifted Placement5.pi0 q))
private def inner (q : Wire) := Equiv.swap (base 719) (base 510) q

theorem divEndpoint : Clear (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) := by
  have ok : DecoderBiasReuse.fixedLayout.wires.all (fun q=>free (outward (inner q)))=true := by decide +kernel
  apply viaFree
  intro q h
  rw [renameProgram_support,StairConcrete.bestLoans_divEndpoint] at h
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
  unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
  rw [renameProgram_support] at hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h|h
  · rw [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl <;> decide +kernel
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    rw [wires_append,Finset.mem_union] at hz
    rcases hz with hz|hz
    · exact List.all_eq_true.mp ok z (List.mem_toFinset.mp (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz)))
    · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
      rw [Finset.mem_singleton] at hc
      rw [hc]
      decide +kernel

end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem firstNo : ∀(b : Bank)(i : Fin 16), fpSup (siteAt b i)=false := by decide +kernel
theorem noRole : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairSchedule.exclusiveRoles := by decide +kernel
theorem noHost : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairPhysicalLayout.hosts 87 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitClear
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime StairConcreteAssembly
open Banks ExitPieces ExitStages ExteriorPorts StairField13V3
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run measurementCount

theorem renameClear (fn : Wire → Wire) (inj : Function.Injective fn) (fixed : Fixed fn) {P : Program}
    (clear : Clear P) : Clear (renameProgram fn P) := by
  intro q hq used
  rw [renameProgram_support] at used
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp used
  by_cases orig : r∈Suffix.archives
  · exact clear r orig hr
  · exact archive_pre inj fixed r orig hq

theorem fieldClear {P : Program} (clear : Clear P) : Clear (StairSchedule.fieldRename P) := by
  rw [fieldRename_eq]
  exact renameClear fieldMap fieldMap_injective (by unfold Fixed; decide +kernel) clear

theorem after (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : Clear (afterGroup ++ unpack) :=
  both (fieldClear (both f g)) (renameClear phaseHost phaseHost.injective phaseFix firstUnpack_free)

private theorem pass {d x rows P} (clear : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P clear m⟩

private theorem parity {d x rows} : Relates FieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,FieldParity.setup_through pair m m⟩

theorem leading (pre : Clear beforeParity) (next : Clear beforeGroup) : ExitReplay.leadingOK := by
  intro x rows a r m pair
  exact compose (compose (compose parity (pass pre)) parity) (pass next) a r pair m

theorem exit (a : Clear beforeParity) (b : Clear beforeGroup) (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : MiddleContract.exit :=
  ExitReplay.exit (leading a b) (after f g)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExitClear
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem table (d : Bool) : allSites fpSup (Rolling1588.placedFirstPacket d)=true := by
  cases d
  · exact passSup_false
  · exact passSup_true

private theorem exclude (q : Wire) (h : q∈Suffix.archives) :
    q∉StairPhysicalLayout.hosts 87 ∧ q∉StairSchedule.exclusiveRoles ∧ fpSup q=false := by
  obtain ⟨b,i,rfl⟩ := WalkForward.bank_rep q h
  exact ⟨noHost b i,noRole b i,firstNo b i⟩

private theorem rebind {P : Program} (hs : List Wire) (eq : hs=StairPhysicalLayout.hosts 87)
    (ok : allSites fpSup P=true) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles hs P) := by
  intro q h used
  have neg := exclude q h
  rcases rebindMany_support StairSchedule.exclusiveRoles hs P q used with host | role | orig
  · exact neg.1 (eq ▸ host)
  · exact neg.2.1 role
  · exact Bool.noConfusion (neg.2.2.symm.trans (allSites_sound fpSup P ok q orig))

theorem first (d : Bool) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (Rolling1588.placedFirstPacket d)) :=
  rebind (hostPlan.firstPacket d) rfl (table d)

end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open Banks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem tail (other : Clear (hostedGroup hostPlan true 44 100 2)) : Clear (entryTailSuffix hostPlan) :=
  both (both (both other divEndpoint) copy) canon
theorem head (other : Clear (hostedGroup hostPlan false 44 100 2)) : Clear (exitHeadPrefix hostPlan) :=
  both (both (both center copy) mulEndpoint) other
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorFixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitOuter
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts ExitPieces
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires

theorem hostedX : Clear StairSchedule.hostedX := ExteriorPorts.checked (by decide +kernel)

theorem ordinaryGroup (d : Bool) (k j n : Nat) (start : 85≤j) (bound : j+n≤102) (budget : k≤68)
    (tab : (hostPlan.group d k j n).all free=true) : Clear (hostedGroup hostPlan d k j n) :=
  groups d k j n start bound budget (List.all_eq_true.mp tab)

theorem other (d : Bool) : Clear (hostedGroup hostPlan d 44 100 2) :=
  ordinaryGroup d 44 100 2 (by decide) (by decide) (by decide) (by cases d <;> decide +kernel)

theorem pre : Clear beforeParity := by
  apply both hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  -- The outer field placement is applied once more by the caller.
  exact ExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (ExteriorFixed.head (other false))

theorem endPart : Clear (afterGroup ++ ExitStages.unpack) :=
  ExitClear.after unprefixSafe (ExteriorFixed.first false)
end ECDSAAdd.Entrant.StairPacket.Extension270.ExitOuter
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExitReady
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts ExitPieces ExitOuter
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem before : Clear beforeGroup := by
  apply both (both hostedX (fieldRename_free clearSafe))
  rw [placedShape]
  apply fieldMapped
  apply both _ reverse425
  apply both _ (ordinaryGroup false 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse450
  apply both _ (ordinaryGroup false 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse465
  apply both _ (ordinaryGroup false 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse480
  apply both _ (ordinaryGroup false 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse490
  apply both _ (ordinaryGroup false 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  exact reverseLast

theorem exit : MiddleContract.exit :=
  ExitReplay.exit (ExitClear.leading pre before) endPart
end ECDSAAdd.Entrant.StairPacket.Extension270.ExitReady
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Seg StairField2V3LastRecX StairField2V3Delta
open StairField2V3EntryPlanR StairOpenWiring StairOuterPlacement StairPhysicalLayout
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount

private theorem pin (x:Nat) (r record:State) (h:RowRelEn x 87 (R0++firstPkt) r record):
    FrameAt x 1 record ∧ AgreeOutside (Δv 87) r record:=by
  obtain ⟨rel,root,tape,⟨F,fx⟩,reach⟩:=h
  have pinned:=g_first root F tape
  rw [fx] at pinned
  exact ⟨reach.symm ▸ pinned.1,rel.1⟩

def stockPrefix:Program:=(((entryPieces cp hostPlan).take 3).map Piece.H).flatten
def Pinned (x:Nat) (ref:State):Prop:=∃record,FrameAt x 1 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap) := by
  rw [hp_group true 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (parts:StairField13V3Fresh.EntryClean):
    CutClean EntryPre (cut eps 3) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap):=
  parts.groupsBefore (3,0,1,84) (by simp)
private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)


theorem at_cut {s:State} (F:EntryFrame s) (m:List Bool):Pinned F.x (run stockPrefix m s) ∧ Loan (run stockPrefix m s):=by
  have eq:=Stair44HostedCut.entry 3 s ⟨F⟩ m
  change run stockPrefix m s=run (cut eps 3) m s at eq
  rw [eq]
  refine ⟨?_,cutLoan (fullCutClean (entryClean_of_planR entryPlans half760)) s ⟨F⟩ m⟩
  obtain ⟨Q,step⟩:=ern3 F.x (entryPlans F.x)
  obtain ⟨n,h⟩:=step s s ⟨⟨F,rfl⟩,rfl⟩ m
  rw [ecut3]
  exact ⟨_,pin _ _ _ h⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorEntryCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ReturningBytes
open Arithmetic MappedCompressed Secp256k1 FrontierEntry1591Field Banks ExteriorPorts
open WindowParityDirty FieldParity
set_option maxRecDepth 6000
attribute [local irreducible] run measurementCount wires
def Keeps (P : Program) : Prop := ∀(s : State) (m : List Bool) (b : Bank) (i : Fin 16),
  (run P m s).basis (siteAt b i) = s.basis (siteAt b i)

theorem untouched {P : Program} (clear : Clear P) : Keeps P :=
  fun s m b i=>run_preserves_outside P m s _ (clear _ (chart b i).2.2.2)

theorem both {P Q : Program} (hp : Keeps P) (hq : Keeps Q) : Keeps (P ++ Q) := by
  intro s m b i
  rw [run_append]
  exact (hq _ _ _ _).trans (hp _ _ _ _)

theorem parity : Keeps StairSchedule.paritySetup := by
  intro s m b i
  have outside : ∀(v : Bank)(j : Fin 16), siteAt v j≠host := by decide +kernel
  have eq : run StairSchedule.paritySetup m s = flip host (stockParity s) s :=
    ParityHost5.setup_run controls host s m host_not_controls
  rw [eq]
  exact at_other _ _ _ _ (outside b i)

theorem nativeBack {d : Bool} {rows : Bank → Nat} {r m P} (hp : Keeps P)
    (old : ∀b,nativeAt d b (rows b) (run P m r)) : ∀b,nativeAt d b (rows b) r :=
  fun b i=>(hp r m b i).symm.trans (old b i)

theorem nativeUnpull {d : Bool} {rows : Bank → Nat} {r} (old : ∀b,nativeAt d b (rows b) (pullState Rolling1588Lifetime.phaseHost r)) :
    ∀b,nativeAt d b (rows b) r := by
  intro b i
  have v := old b i
  change r.basis (Rolling1588Lifetime.phaseHost (siteAt b i))=_ at v
  rwa [host_ports] at v
end ECDSAAdd.Entrant.StairPacket.Extension270.ReturningBytes
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField2V3Seg
open FieldMask FieldJourney FieldCosts ExteriorPorts Banks
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
attribute [local irreducible] run measurementCount
theorem history {x rows} (labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)):
    (∀j∈bankIds,fieldRows rows j<63145) ∧
    (∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j)):=by
  have times:∀b:Bank,5*ExteriorPorts.groupId b-5=tick b:=by decide +kernel
  constructor <;> intro j hj <;> obtain ⟨b,rfl⟩:=idAt _ hj <;> rw [rowsAt]
  · exact (labels b).1
  · rw [times];exact (labels b).2

private theorem entered (x:Nat) (rows:Bank→Nat) (a ref:State) (m:List Bool)
    (same:Paired true x a ref rows) (pin:Pinned x ref) (loans:Loan ref):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) ref):=by
  obtain ⟨record,frame,agree⟩:=pin
  obtain ⟨bound,trace⟩:=history same.labels
  apply hosted
  exact FieldView.caller true x _ bound trace (pullState fieldEquiv a) ref record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix (fits same)) frame agree loans

theorem group_run {s:State} (F:EntryFrame s) (before m:List Bool) (a:State) (rows:Bank→Nat)
    (same:Paired true F.x a (run stockPrefix before s) rows):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) (run stockPrefix before s)):=by
  have h:=at_cut F before
  exact entered F.x rows a _ m same h.1 h.2
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorEntryCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ReturningTail
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Banks
open ReturningBytes FieldMask FieldJourney ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
attribute [local irreducible] run measurementCount wires

def program (pre between post setup : Program) := (((pre ++ setup) ++ between) ++ setup) ++ post
private theorem keepTail {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post) :
    Keeps (program pre between post StairSchedule.paritySetup) :=
  ReturningBytes.both (ReturningBytes.both (ReturningBytes.both
    (ReturningBytes.both (untouched hp) ReturningBytes.parity) (untouched hb)) ReturningBytes.parity) (untouched ht)

private theorem stable {d x rows P} (c : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P c m⟩

private theorem switchParity {d x rows} : Relates FieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,FieldParity.setup_through pair m m⟩

theorem carry {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    {d x rows} : Relates (program pre between post FieldParity.setup) (program pre between post StairSchedule.paritySetup)
      (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) :=
  compose (compose (compose (compose (stable hp) switchParity) (stable hb)) switchParity) (stable ht)

theorem runTail {pre between post oldPrefix : Program} {s : State} (F : EntryFrame s)
    (shape : MiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post) (a : State) (old m : List Bool)
    (ff : Fits (fieldRows (ConcreteRows.rows F.x)) (finalCode true (plan true) (initialCode true)) a (run oldPrefix old s)) :
    ∃n, Paired false F.x (run (program pre between post FieldParity.setup) m a)
      (run (program pre between post StairSchedule.paritySetup) n (run oldPrefix old s)) (ConcreteRows.rows F.x) := by
  let tape := joinTapes oldPrefix old []
  have native := EndBytes.div_native F tape
  have known := nativeUnpull native.bytes
  unfold tape at known
  rw [shape,joined] at known
  have here := nativeBack (keepTail hp hb ht) known
  have source : Paired false F.x a (run oldPrefix old s) (ConcreteRows.rows F.x) := pairFinished ff native.ids here
  exact carry hp hb ht _ _ source m

theorem entryOfPrefix {pre between post newPrefix oldPrefix : Program}
    (newShape : MiddleContract.divHead=newPrefix ++ program pre between post FieldParity.setup)
    (oldShape : MiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    (starts : ∀ {s : State} (F : EntryFrame s) (m : List Bool), ∃old,
      Fits (fieldRows (ConcreteRows.rows F.x)) (finalCode true (plan true) (initialCode true))
        (run newPrefix m s) (run oldPrefix old s)) : MiddleContract.entry := by
  intro s F m
  obtain ⟨old,ff⟩ := starts F m
  obtain ⟨n,pair⟩ := runTail F oldShape hp hb ht _ old (m.drop (measurementCount newPrefix)) ff
  refine ⟨joinTapes oldPrefix old n,?_⟩
  rw [newShape,oldShape,joined,run_append,run_take]
  exact pairPull Rolling1588Lifetime.phaseHost Rolling1588Lifetime.phaseHost.injective phaseFix pair
end ECDSAAdd.Entrant.StairPacket.Extension270.ReturningTail
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount wires

def beforeGroup := StairSchedule.fieldRename (StairLoan.rebindMany StairSchedule.exclusiveRoles
  (hostPlan.firstPacket true) (Rolling1588.placedFirstPacket true) ++ FourScratchWindow.clearProgram)
def rawTail := StairSchedule.forwardSegment cp 87 62 425 450 ++ hostedGroup hostPlan true 14 85 5 ++
    StairSchedule.forwardSegment cp 62 47 450 465 ++ hostedGroup hostPlan true 23 90 3 ++
    StairSchedule.forwardSegment cp 47 32 465 480 ++ hostedGroup hostPlan true 31 93 3 ++
    StairSchedule.forwardSegment cp 32 22 480 490 ++ hostedGroup hostPlan true 37 96 2 ++
    StairSchedule.forwardSegment cp 22 12 490 500 ++ hostedGroup hostPlan true 42 98 2 ++ StairSchedule.forwardLast cp
def pre := renameProgram fieldEquiv rawTail ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def between := StairSchedule.hostedX ++ StairSchedule.fieldRename (entryLowSuffix hostPlan) ++ StairSchedule.hostedX
def post := renameProgram phaseHost Stair44Outer.reverseEnd
def field (S G : Program) := (((beforeGroup ++ renameProgram fieldEquiv G) ++ pre) ++ S) ++ between ++ S

theorem ordinary : StairHostsSchedule.entryFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (FieldCosts.group true 1 84) := by
  simp only [field,beforeGroup,pre,between,rawTail,StairHostsSchedule.entryFieldHosted,
    entryLowPrefix,entryTailPrefix,FieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : Caller.entryFieldHosted cp =
    field FieldParity.setup (FieldCosts.group84 true) := by
  simp only [field,beforeGroup,pre,between,rawTail,FieldParity.setup_eq,FieldCosts.caller_eq,Caller.entryFieldHosted,
    Caller.entryLowPrefix,Caller.entryTailPrefix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

def stockBegin := renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)
theorem cutShape : ExteriorEntryCut.stockPrefix = stockBegin ++ beforeGroup := by
  simp only [ExteriorEntryCut.stockPrefix,stockBegin,beforeGroup,entryPieces,List.take_succ_cons,
    List.take_zero,common,firstSlot,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,fieldRename_append,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivPieces
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivPieces
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires
theorem beforeFree : Clear beforeGroup := fieldRename_free (both (ExteriorFixed.first true) clearSafe)
theorem preFree : Clear pre := by
  apply both _ (fieldRename_free unprefixSafe)
  apply fieldMapped
  apply both _ forwardLast
  apply both _ (ExitOuter.ordinaryGroup true 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward490
  apply both _ (ExitOuter.ordinaryGroup true 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward480
  apply both _ (ExitOuter.ordinaryGroup true 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward465
  apply both _ (ExitOuter.ordinaryGroup true 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward450
  exact both forward425 (ExitOuter.ordinaryGroup true 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
theorem betweenFree : Clear between := by
  apply both _ ExitOuter.hostedX
  apply both ExitOuter.hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  exact ExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (ExteriorFixed.tail (ExitOuter.other true))
theorem postFree : Clear post := mapped _ phaseHost.injective phaseFix reverseEnd_free
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivPieces
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivReady
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open Banks StartStates ExteriorPorts ExteriorDivPieces FieldMask FieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount wires

def pack := renameProgram phaseHost checkpointPrimitives.firstPack
def beginW := opening true 139 ++ pack
def beginR := original true 139 ++ pack
def prefixW := (beginW ++ beforeGroup) ++ renameProgram fieldEquiv (FieldCosts.group84 true)
def prefixR := (beginR ++ beforeGroup) ++ renameProgram fieldEquiv (FieldCosts.group true 1 84)

theorem refBegin : beginR = Stair44Kernel.divLead := by
  simp only [beginR,original,pack,Stair44Kernel.divLead,Six505.rename_append]

theorem begin_pair {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃n, Paired true F.x (run beginW m s) (run beginR n s) (ConcreteRows.rows F.x) := by
  let A := opening true 139
  let B := original true 139
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [pack,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (StartStates.division ConcreteRows.rows ConcreteRows.binding F m).through _ firstPack_free _

theorem cut {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old rec, Paired true F.x (run (beginW ++ beforeGroup) m s) (run (beginR ++ beforeGroup) old s)
        (ConcreteRows.rows F.x) ∧ run (beginR ++ beforeGroup) old s = run ExteriorEntryCut.stockPrefix rec s := by
  obtain ⟨n,pair⟩ := begin_pair F m
  let t := m.drop (measurementCount beginW)
  refine ⟨joinTapes beginR n t,joinTapes stockBegin n t,?_,?_⟩
  · rw [joined,run_append,run_take]
    exact pair.through _ beforeFree _
  · rw [cutShape,joined,joined,refBegin,StockHead.leadD F]
    rfl

theorem starts {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old, Fits (fieldRows (ConcreteRows.rows F.x)) (finalCode true (plan true) (initialCode true))
      (run prefixW m s) (run prefixR old s) := by
  obtain ⟨n,k,pair,eq⟩ := cut F m
  let t := m.drop (measurementCount (beginW ++ beforeGroup))
  let tape := referenceTape true (plan true) t
  refine ⟨joinTapes (beginR ++ beforeGroup) n tape,?_⟩
  rw [prefixR,prefixW,joined,run_append,run_take,eq]
  rw [eq] at pair
  exact ExteriorEntryCut.group_run F k t _ _ pair

theorem newShape : MiddleContract.divHead = prefixW ++ ReturningTail.program pre between post FieldParity.setup := by
  simp only [MiddleContract.divHead,KernelPrograms.divBefore,corrected,field,prefixW,beginW,
    opening,KernelPrograms.openWalk,StartStates.openWalk,pack,post,ReturningTail.program,
    Six505.rename_append,List.append_assoc]
theorem oldShape : MiddleContract.oldDivHead = prefixR ++ ReturningTail.program pre between post StairSchedule.paritySetup := by
  simp only [MiddleContract.oldDivHead,Stair44Kernel.fieldD,ordinary,field,prefixR,refBegin,
    post,ReturningTail.program,List.append_assoc]
theorem entry : MiddleContract.entry :=
  ReturningTail.entryOfPrefix newShape oldShape preFree betweenFree postFree starts
end ECDSAAdd.Entrant.StairPacket.Extension270.ExteriorDivReady
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.KernelReplay
theorem contracts : KernelPrograms.Contracts where
  divSites := CallerSupport.division
  mulSites := CallerSupport.multiplication
  enter := division_correct ExteriorDivReady.entry
  exit := multiplication_eq ExitReady.exit
end ECDSAAdd.Entrant.StairPacket.Extension270.KernelReplay
end

section
namespace ECDSAAdd.Entrant.StairPacket.Extension270.ReleaseProof
open Arithmetic Secp256k1 Challenge

theorem certificate : Challenge.Certificate Caller.entry Caller.bounds :=
  Caller.certificateOf Caller.computedCounts
    ⟨Generic.correct KernelReplay.contracts,Caller.physical,Caller.width⟩
end ECDSAAdd.Entrant.StairPacket.Extension270.ReleaseProof
end

namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := StairPacket.Extension270.Caller.entry
def bounds : Challenge.Bounds := StairPacket.Extension270.Caller.bounds
theorem certificate : Challenge.Certificate entry bounds :=
  StairPacket.Extension270.ReleaseProof.certificate

end ECDSAAdd.Entrant
