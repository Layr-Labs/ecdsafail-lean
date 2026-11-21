import ECDSAAdd.Submission.Entrant.ShadowPortal390
import ECDSAAdd.Submission.Entrant.ShadowParts

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [396,1689,397,1688,398,1687,399,1686,400,1685,401,1684,402,1683,403,1682,404,1681,405,1680,909,910,911,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [396,1689,397,1688,398,399,1686,400,401,1684,402,1683,403,404,1681,405,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923,1687,1685,1682,1680,909,910,911]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [396,1689,397,1688,398,1687,399,1686,400,1685,401,1684,402,1683,403,1682,404,1681,405,1680,909,910,911,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := [(399,1687),(1686,1687),(400,1687),(401,1687),(1684,1685),(402,1687),(1683,1685),(403,1687),(404,1685),(1681,1687),(405,1682)]
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : (Shadow7.exitLoadP 390) d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
theorem load_unique : Function.Injective rawPorts := by exact injective_list rawPortsList (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem load_map : ∀q:Fin 155, loadMap q=rawPorts ⟨q,by omega⟩ := by
  have h1 : (loadMapList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q
  simp only [loadMap, rawPorts, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  revert q
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_route : ∀i,backMap loadMoves (codePorts i)=rawPorts (loadRoute i) := by
  have h1 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h3 : ((loadRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [codePorts, rawPorts, loadRoute, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h3]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_sort : ∀ i, loadRoute i=i ∨ (16≤ i.val ∧ 16≤(loadRoute i).val) := by
  have h1 : ((loadRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [loadRoute, Fin.ext_iff, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_scope : ∀p∈loadMoves,(∃i,rawPorts i=p.1) ∧ (∃i,rawPorts i=p.2) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem load_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame rawPorts (startCols true d) row s) :
    let t:=run ((Shadow7.exitLoadP 390) d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [396,1689,397,1688,398,399,1686,400,401,1684,402,1683,403,404,1681,405,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,912,913,914,915,916,917,918,919,920,921,922,923]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1687,399),(399,1686),(1686,400),(400,401),(1685,1684),(401,402),(1684,1683),(402,403),(1683,404),(403,1681),(1682,405),(404,1556),(1681,1557),(405,1558),(1680,1559),(909,1560),(910,1561),(911,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : (Shadow7.exitRestoreP 390) d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
theorem restore_unique : Function.Injective codePorts := by exact injective_list codePortsList (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem restore_map : ∀q:Fin 150, restoreMap q=codePorts ⟨q,by omega⟩ := by
  have h1 : (restoreMapList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q
  simp only [restoreMap, codePorts, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2]
  revert q
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_route : ∀i,backMap restoreMoves (rawPorts i)=codePorts (restoreRoute i) := by
  have h1 : (rawPortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h2 : (codePortsList.all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have h3 : ((restoreRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [codePorts, rawPorts, restoreRoute, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h2, ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h3]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_sort : ∀ i, restoreRoute i=i ∨ (23≤ i.val ∧ 23≤(restoreRoute i).val) := by
  have h1 : ((restoreRouteList.map Fin.val).all fun x => decide (x < 2 ^ 11)) = true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro i
  simp only [restoreRoute, Fin.ext_iff, ECDSAAdd.Entrant.WSlimV3.fin_getD_val, Fin.val_zero, Fin.isValue,
    ECDSAAdd.Entrant.WSlimV3.tget_tpack' 11 _ h1]
  revert i
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_scope : ∀p∈restoreMoves,(∃i,codePorts i=p.1) ∧ (∃i,codePorts i=p.2) := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem restore_run (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame codePorts (startCols false d) row s) :
    let t:=run ((Shadow7.exitRestoreP 390) d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run ((Shadow7.exitRestoreP 390) d) n (run ((Shadow7.exitLoadP 390) d) m s)=s := by
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
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run ((Shadow7.exitLoadP 390) d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then enter0Trace0In else enter1Trace0In) i).testBit row) ∧
        (∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run ((Shadow7.exitRestoreP 390) d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame rawPorts s row data h recorded scratch
  have ⟨ph,fr,away⟩:=load_run d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip d row hr s m tape ready⟩
  intro i
  exact (fr ⟨i,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d i))
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary3907

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveBoundary3907
def sourceIdx : Fin 23 := ⟨20,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (Shadow7.shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (Shadow7.native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveBoundary3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack3907
def program (d:Bool) := renameProgram (OB5.sig 390) (Rolling1588.packAtTick d 380)
def reverse (d:Bool) := renameProgram (OB5.sig 390) (Rolling1588.unpackAtTick d 380)
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack3907
def history (q:Fin 10) := OB5.sig 390 (History5.historyMap base 375 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair
namespace Portal390Flag7
set_option exponentiation.threshold 1024
theorem release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw packed:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      (pullState (OB5.sig 389) raw) packed) :
    run (Shadow7.portalInvP 390) m packed=pullState (OB5.sig 389) raw := by
  rw [cut.unique (physical_frame_local z small raw [] route sg record)]
  exact portal_return _ [] m (clean_for raw z route sg record)

end Portal390Flag7
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails
namespace NativePack3907
open ArchiveBoundary3907
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (Shadow7.shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (Shadow7.shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
end NativePack3907
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1634,1635,1636]
def dst : List Wire := [909,910,911]
def pairs : List (Wire×Wire) := [(909,1634),(910,1635),(911,1636)]
def stash (payload:State) (s:State) : State :=
  ⟨s.phase,fun q=>if q∈dst then payload.basis (backMap pairs q) else s.basis q⟩

theorem commutes (p:Program) (free:∀q∈dst,q∉wires p) (m:List Bool) (payload s:State):
    run p m (stash payload s)=stash payload (run p m s) := by
  have inc:=run_measured_locality p (wires p) (Finset.Subset.refl _) (stash payload s) s m rfl
    (fun q h=>by simp [stash,show q∉dst from fun eq=>free _ eq h])
  apply congrArg₂ State.mk inc.1
  funext q
  by_cases h:q∈wires p
  · simpa [stash,show q∉dst from fun eq=>free _ eq h] using inc.2 q h
  · rw [run_preserves_outside _ m _ _ h]
    simp only [stash,run_preserves_outside _ m s _ h]

theorem park (s:State) (m:List Bool) (empty:∀q∈dst,s.basis q=false) :
    run (Shadow7.parkP 390) m s=stash s (eraseSites src s) := by
  rw [show (Shadow7.parkP 390)=moves pairs by rfl,moves_run _ (by decide) s m]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases dest:q∈dst
  · simp [stash,dest]
  by_cases source:q∈src
  · have toDst:∀w∈src,backMap pairs w∈dst:=by decide
    simp [stash,eraseSites,dest,source,empty _ (toDst _ source)]
  · simp only [src,List.mem_cons,List.not_mem_nil,or_false,not_or] at source
    have nod:=dest
    simp only [dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at nod
    simp [stash,eraseSites,dest,src,pairs,backMap,source.1,source.2.1,source.2.2,nod.1,nod.2.1,nod.2.2]

theorem park_undo (s:State) (m n:List Bool) : run (Shadow7.parkInvP 390) n (run (Shadow7.parkP 390) m s)=s := by
  rw [show (Shadow7.parkP 390)=moves pairs by rfl,show (Shadow7.parkInvP 390)=moves pairs.reverse by rfl,moves_run _ (by decide),moves_run _ (by decide)]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases h:q∈src++dst
  · have inv:∀w∈src++dst,backMap pairs (backMap pairs.reverse w)=w:=by decide
    exact congrArg s.basis (inv _ h)
  · simp only [List.mem_append,src,dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    rcases h with ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩⟩
    simp [pairs,backMap,h1,h2,h3,h4,h5,h6]


end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed Portal390Flag7
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
def misses (i:Instr) := decide (909∉i.wires ∧ 910∉i.wires ∧ 911∉i.wires)
theorem misses_all (P:Program) (h:P.all misses=true) : ∀q∈dst,q∉wires P:=by
  intro q hq
  induction P with
  | nil=>simp [wires]
  | cons i P ih=>
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hi:909∉i.wires ∧ 910∉i.wires ∧ 911∉i.wires:=of_decide_eq_true h.1
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨by rcases List.mem_cons.mp hq with rfl|h'
              · exact hi.1
              · rcases List.mem_cons.mp h' with rfl|h''
                · exact hi.2.1
                · obtain rfl:=List.mem_singleton.mp h'';exact hi.2.2,ih h.2⟩
theorem avoid : ∀q∈dst,q∉wires (Shadow7.portalP 390):=misses_all _ (by decide +kernel)
theorem avoidInv : ∀q∈dst,q∉wires (Shadow7.portalInvP 390):=misses_all _ (by decide +kernel)

theorem parked_release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 54 15 z) (raw s:State) (m n:List Bool)
    (route sg:Bool)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 390) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 405 1633 1631 1632 (PortalValues.negative sg z.u)
      (decide (3*2^70≤z.u+z.v)) (decide (3*2^70≤z.u+z.v ∧ 2^54≤z.u))
      (pullState (OB5.sig 389) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) :
    let out:=run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)
    out=stash s (pullState (OB5.sig 389) raw) ∧ ∀a b,
      run (Shadow7.parkInvP 390) b (run (Shadow7.portalP 390) a out)=s := by
  have fw (a:List Bool):=cut.unique (physical_frame_local z small raw a route sg input)
  have endEq:run (Shadow7.portalInvP 390) n (run (Shadow7.parkP 390) m s)=stash s (pullState (OB5.sig 389) raw):=by
    rw [park _ _ empty,commutes _ avoidInv,release z small raw _ n route sg input cut]
  refine ⟨endEq,?_⟩
  intro a b
  rw [endEq,commutes _ avoid,←fw,←park s m empty,park_undo]

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
theorem released : ∀q∈dst,OB5.sig 389 q∈(W.compactSkywalkSignPoolB base 390).released := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem dormant (i:Nat) (d:Bool) (seed p:Nat) (raw:State) (q:Wire)
    (stage:Rolling1588.Integer.Stage base d seed p i raw.basis)
    (outside:q∉wires (Rolling1588.Integer.encodePrefix base d i))
    (inHigh:q∈(W.compactSkywalkSignPoolB base i).released) : raw.basis q=false := by
  obtain ⟨s,hs,eq⟩:=stage
  have clean:(W.compactSkywalkSignPoolB base i).Clean s.basis:=hs.2.2
  rw [eq,run_preserves_outside _ _ s q outside]
  exact clean q inHigh
theorem above_history (i:Nat) (lim:i≤512) (d:Bool) (q:Nat)
    (q0:i+16<q) (q1:q<1044) : q∉wires (Rolling1588.Integer.encodePrefix base d i):=by
  rw [Rolling1588.Integer.prefix_support_eq]
  intro mem
  obtain ⟨j,where',side⟩:=StackOB5Base.encodePrefix_mem i lim _ mem
  change q=j+16 at where'
  omega
theorem clear_dest (d:Bool) (seed p:Nat) (raw:State)
    (stage:Rolling1588.Integer.Stage base d seed p 390 raw.basis) :
    ∀q∈dst,(pullState (OB5.sig 389) raw).basis q=false:=by
  have bounds:∀q∈dst,390+16<OB5.sig 389 q ∧ OB5.sig 389 q<1044:=by decide +kernel
  intro q hit
  exact dormant 390 d seed p raw (OB5.sig 389 q) stage
    (above_history 390 (by decide) d _ (bounds _ hit).1 (bounds _ hit).2) (released _ hit)

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint3907

end
