import ECDSAAdd.Submission.Entrant.ShadowPortalFacts

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(478, 1558), (479, 1559), (480, 1560), (481, 1561), (482, 1562), (483, 1563), (484, 1564), (485, 1565), (486, 1566), (487, 1567), (488, 1568), (489, 1569), (490, 1570), (491, 1571), (492, 1572), (493, 1573), (494, 1574), (495, 1575), (496, 1576), (497, 1577), (498, 1578), (499, 1579), (500, 1580), (501, 1581), (502, 1582), (503, 1583), (504, 1584), (505, 1585), (506, 1586), (507, 1587), (508, 1588), (509, 1589), (510, 1590), (511, 1591), (512, 1592), (513, 1593), (514, 1594), (515, 1595), (516, 1596), (517, 1597), (518, 1598), (519, 1599), (520, 1600), (521, 1601), (522, 1602), (523, 1603), (524, 1604), (525, 1605), (526, 1606), (527, 1607), (528, 1608)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : (((Shadow7.portalP 390)).drop 215).take 208=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(857, 1556), (858, 1557), (859, 1558), (860, 1559), (861, 1560), (862, 1561), (863, 1562), (864, 1563), (865, 1564), (866, 1565), (867, 1566), (868, 1567), (869, 1568), (870, 1569), (871, 1570), (872, 1571), (873, 1572), (874, 1573), (875, 1574), (876, 1575), (877, 1576), (878, 1577), (879, 1578), (880, 1579), (881, 1580), (882, 1581), (883, 1582), (884, 1583), (885, 1584), (886, 1585), (887, 1586), (888, 1587), (889, 1588), (890, 1589), (891, 1590), (892, 1591), (893, 1592), (894, 1593), (895, 1594), (896, 1595), (897, 1596), (898, 1597), (899, 1598), (900, 1599), (901, 1600), (902, 1601), (903, 1602), (904, 1603), (905, 1604), (906, 1605), (907, 1606), (908, 1607)]
def orientation := latch false (some 1631) 1632 856 orientationPairs
theorem orientation_layout : (1632::856::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : (((Shadow7.portalP 390)).drop 426).take 212=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1631∉1632::856::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528]
def railB : List Wire := [856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
def scan : Program := [.CX 528 1633,.CX 908 1633] ++
  RailPair.exchange 405 (railA.zip railB) ++ signComplement 1633 railB
def flags : Program := [.CCX 476 477 1557] ++ threshold ++
  [.measureX 1557 [] [.CZ 476 477],.CX 1556 1631,.CX 1631 1556] ++ orientation
def erase : Program := [.X 478,.CCX 858 478 1556] ++
  Companion.erase bulkA bulkB carry 1632 1556 ++
  [.measureX 1556 [] [.CZ 858 478],.X 478]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1633 (railB.take 3) ++ RailPair.exchange 405 ((railA.take 3).zip (railB.take 3))
theorem emitted : (Shadow7.portalP 390)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (405::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1633∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1632 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 476 477 1557 1556 1631 1632 856 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 478 858 1556 (PortalBorrow.restore bulkA bulkB carry 1632 1556)
theorem emitted_back : (Shadow7.portalInvP 390)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 476 477 1557 1556 1631 1632 856 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 478 858 1556 (Companion.erase bulkA bulkB carry 1632 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1631,1632,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1633 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 476 477 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 856 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1631 f) 1632 u⟩ := by
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
    run (Shadow7.portalInvP 390) tape (run (Shadow7.portalP 390) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1631 ∧ q≠1632 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 390) (OB5.sig 389) 70 528 908 405 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 528 908 405 1633 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 528 908 405 1633 pairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^70 ≤ u+v → min u v < 2^54) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^70) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^70) :
    let far:=decide (3*2^70≤u+v)
    let long:=decide (3*2^70≤u+v ∧ 2^54≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1631 far) 1632 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 476 477 thresholdPairs orientationPairs 856 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^70) (2^54) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 3*2^70 ≤ u+v → min u v < 2^54) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^70) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^70)
    (mode:q.basis 1632=decide (3*2^70≤u+v ∧ 2^54≤u)) :
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
  · apply PortalValues.input_eq_shadow7 476 477 478 856 857 858 1632 bulkA bulkB q.basis (2^70) (2^54) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 405 1633 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 405 1633 1631 1632 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1631 ∧ w≠1632 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1631 ∧ w≠1632 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal390Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 389) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 389 q∈(W.compactSkywalkTickLayout base 390).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 389) raw
    PackedCut loPairs hiPairs 405 1633 1631 1632 (negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      origin (run (Shadow7.portalP 390) m origin) := by
  let origin:=pullState (OB5.sig 389) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^70≤z.u+z.v)
  let long:=decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u)
  have short : 3*2^70 ≤ z.u+z.v → min z.u z.v < 2^54 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1633=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 389 1633)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1631 far) 1632 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1631) (qu:q≠1632):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 528 908 405 1633 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 528 ^^ origin.basis 908)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 405 1633 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 405 1633 1631 1632 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
end ECDSAAdd.Entrant.StairPacket.Portal390Flag7
