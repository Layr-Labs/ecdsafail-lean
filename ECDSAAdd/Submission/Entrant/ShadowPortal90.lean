import ECDSAAdd.Submission.Entrant.ShadowPortalFacts

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(328, 1558), (329, 1559), (330, 1560), (331, 1561), (332, 1562), (333, 1563), (334, 1564), (335, 1565), (336, 1566), (337, 1567), (338, 1568), (339, 1569), (340, 1570), (341, 1571), (342, 1572), (343, 1573), (344, 1574), (345, 1575), (346, 1576), (347, 1577), (348, 1578), (349, 1579), (350, 1580), (351, 1581), (352, 1582), (353, 1583), (354, 1584), (355, 1585), (356, 1586), (357, 1587), (358, 1588), (359, 1589), (360, 1590), (361, 1591), (362, 1592), (363, 1593)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : (((Shadow7.portalP 90)).drop 155).take 148=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(1007, 1556), (1008, 1557), (1009, 1558), (1010, 1559), (1011, 1560), (1012, 1561), (1013, 1562), (1014, 1563), (1015, 1564), (1016, 1565), (1017, 1566), (1018, 1567), (1019, 1568), (1020, 1569), (1021, 1570), (1022, 1571), (1023, 1572), (1024, 1573), (1025, 1574), (1026, 1575), (1027, 1576), (1028, 1577), (1029, 1578), (1030, 1579), (1031, 1580), (1032, 1581), (1033, 1582), (1034, 1583), (1035, 1584), (1036, 1585), (1037, 1586), (1038, 1587), (1039, 1588), (1040, 1589), (1041, 1590), (1042, 1591), (1043, 1592)]
def orientation := latch false (some 1781) 1782 1006 orientationPairs
theorem orientation_layout : (1782::1006::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : (((Shadow7.portalP 90)).drop 306).take 152=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1781∉1782::1006::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363]
def railB : List Wire := [1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 363 1783,.CX 1043 1783] ++
  RailPair.exchange 105 (railA.zip railB) ++ signComplement 1783 railB
def flags : Program := [.CCX 326 327 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 326 327],.CX 1556 1781,.CX 1781 1556] ++ orientation
def erase : Program := [.X 328,.CCX 1008 328 1556] ++
  Companion.erase bulkA bulkB carry 1782 1556 ++
  [.measureX 1556 [] [.CZ 1008 328],.X 328]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1783 (railB.take 3) ++ RailPair.exchange 105 ((railA.take 3).zip (railB.take 3))
theorem emitted : (Shadow7.portalP 90)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (105::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1783∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1782 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 326 327 1557 1556 1781 1782 1006 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 328 1008 1556 (PortalBorrow.restore bulkA bulkB carry 1782 1556)
theorem emitted_back : (Shadow7.portalInvP 90)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 326 327 1557 1556 1781 1782 1006 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 328 1008 1556 (Companion.erase bulkA bulkB carry 1782 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1781,1782,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1783 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 326 327 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 1006 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1781 f) 1782 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags_run
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags_undo
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem erase_return (s:State) (m n:List Bool) (h:s.basis 1556=false ∧ ∀q∈carry,s.basis q=false) :
    run backErase n (run erase m s)=s := by
  rw [erase_spec]
  apply PortalBorrow.erase_undo
  · exact copy_good
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · exact PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h.1
  · exact h.2
theorem portal_return (s:State) (m tape:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run (Shadow7.portalInvP 90) tape (run (Shadow7.portalP 90) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1781 ∧ q≠1782 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 90) (OB5.sig 89) 220 363 1043 105 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 363 1043 105 1783 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 363 1043 105 1783 pairs := by decide +kernel
theorem scan_real (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (s:State) (m:List Bool) (h:Rolling1588.Integer.Stage base d x p 90 s.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init x p)
    let v:=run scan m (pullState (OB5.sig 89) s)
    ∃g sg:Bool,v.basis 1783=negative sg z.u ∧ v.basis 105=g ∧ regValue railA v.basis=(z.u+z.v)/2^220 ∧
      regValue railB v.basis=(z.u-(negative sg z.u).toNat)/2^220 := by
  obtain ⟨route,sg,inp⟩:=real_input d x p 90 hp0 hx0 hpo hp hq hx hc (by decide) s h
  have clean: (pullState (OB5.sig 89) s).basis 1783=false := by
    apply (regValue_zero _ _).mp inp.2.2.2.2.2 (OB5.sig 89 1783)
    decide +kernel
  have v:=scan_input _ _ _ _ _ _ _ _ source geom s m _ _ _ _ inp clean
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at v
  exact ⟨route,sg,v⟩

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^220 ≤ u+v → min u v < 2^204) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^220) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^220) :
    let far:=decide (3*2^220≤u+v)
    let long:=decide (3*2^220≤u+v ∧ 2^204≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1781 far) 1782 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 326 327 thresholdPairs orientationPairs 1006 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^220) (2^204) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^220 ≤ u+v → min u v < 2^204) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^220) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^220)
    (mode:q.basis 1782=decide (3*2^220≤u+v ∧ 2^204≤u)) :
    let r:=run erase m q
    r.phase=q.phase ∧ (∀w,w∉bulkB → r.basis w=q.basis w) ∧ regValue bulkB r.basis=0 := by
  rw [erase_spec]
  apply PortalBorrow.erase_run
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fresh.1
  · exact fresh.2
  · apply PortalValues.input_eq_shadow7 326 327 328 1006 1007 1008 1782 bulkA bulkB q.basis (2^220) (2^204) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 105 1783 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 105 1783 1781 1782 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1781 ∧ w≠1782 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1781 ∧ w≠1782 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal90Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 89) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 89 q∈(W.compactSkywalkTickLayout base 90).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 204 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 89) raw
    PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  let origin:=pullState (OB5.sig 89) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^220≤z.u+z.v)
  let long:=decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u)
  have short : 3*2^220 ≤ z.u+z.v → min z.u z.v < 2^204 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1783=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 89 1783)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1781 far) 1782 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1781) (qu:q≠1782):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 363 1043 105 1783 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 363 ^^ origin.basis 1043)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 105 1783 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 105 1783 1781 1782 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
theorem physical_frame_for (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 90 raw.basis)
    (route sg:Bool)
    (record:let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
      SkywalkIntegerInput (W.compactSkywalkTickLayout base 90) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 89) raw
    PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  have _input:=original_input d seed p 90 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact physical_frame_local _ (Shadow7.Envelope.inputs seed p 90 (by omega) hp (by decide)).1 raw m route sg record
theorem physical_frame (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 90 raw.basis) :
    let z:=SkywalkNat.step^[90] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 89) raw
    ∃sg:Bool,PackedCut loPairs hiPairs 105 1783 1781 1782 (negative sg z.u)
      (decide (3*2^220≤z.u+z.v)) (decide (3*2^220≤z.u+z.v ∧ 2^204≤z.u))
      origin (run (Shadow7.portalP 90) m origin) := by
  obtain ⟨route,sg,input⟩:=real_input d seed p 90 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact ⟨sg,physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m h route sg input⟩

end ECDSAAdd.Entrant.StairPacket.Portal90Flag7
