import ECDSAAdd.Submission.Entrant.StairSideAP1

section


section


end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialCosts
open Arithmetic MappedCompressed Partial StairArchiveGates
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem part30 : toffoliCount (archiveRestore270 false) = 80 ∧ measurementCount (archiveRestore270 false) = 124 := by
  decide +kernel

theorem part31 : toffoliCount (Rolling1588.unpackAtTick false 260) = 11 ∧ measurementCount (Rolling1588.unpackAtTick false 260) = 2 := by
  decide +kernel

theorem part32 : toffoliCount (W.ReverseCarry.compactReceiverTick base 270) = 481 ∧ measurementCount (W.ReverseCarry.compactReceiverTick base 270) = 241 := by
  have a := W.ReverseCarry.compactReceiverTick_counts base 270 (by decide) base_pool_nodup
  have b := W.compactSkywalkReverseTick_counts base 270 (by decide) base_pool_nodup
  have width : W.compactSkywalkTickPreWidth 270 - 1 + (W.compactSkywalkTickPostWidth 270 - 1) = 483 := by decide +kernel
  have post : W.compactSkywalkTickPostWidth 270 - 1 = 241 := by decide +kernel
  have trim : (if W.trimTick 270 then 1 else 0) = 1 := by decide +kernel
  omega

theorem part33 : toffoliCount (portal270) = 526 ∧ measurementCount (portal270) = 313 := by
  decide +kernel

theorem part34 : toffoliCount (park270Inv) = 0 ∧ measurementCount (park270Inv) = 0 := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.PartialCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialCosts
open Arithmetic MappedCompressed Partial StairArchiveGates
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem part35 : toffoliCount (leave255Inv) = 910 ∧ measurementCount (leave255Inv) = 328 := by
  decide +kernel

theorem part36 : toffoliCount (unrouted ⟨12,by decide⟩ 1 14) = 4116 ∧ measurementCount (unrouted ⟨12,by decide⟩ 1 14) = 2058 := by
  let j : Fin 23 := ⟨12,by decide⟩
  have h := (fixed_route j 1 14 (by decide)).2
  have hs := IntegerPacket.metrics (shape j) 1 14 (by decide +kernel)
  rw [h, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, hs.2.2.1, hs.2.2.2]
  dsimp only [j]
  decide +kernel

theorem part37 : toffoliCount (archiveRestore255 false) = 80 ∧ measurementCount (archiveRestore255 false) = 124 := by
  decide +kernel

theorem part38 : toffoliCount (Rolling1588.unpackAtTick false 245) = 11 ∧ measurementCount (Rolling1588.unpackAtTick false 245) = 2 := by
  decide +kernel

theorem part39 : toffoliCount (unrouted ⟨12,by decide⟩ 0 1) = 294 ∧ measurementCount (unrouted ⟨12,by decide⟩ 0 1) = 147 := by
  let j : Fin 23 := ⟨12,by decide⟩
  have h := (fixed_route j 0 1 (by decide)).2
  have hs := IntegerPacket.metrics (shape j) 0 1 (by decide +kernel)
  rw [h, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, hs.2.2.1, hs.2.2.2]
  dsimp only [j]
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.PartialCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialCosts
open Arithmetic MappedCompressed Partial StairArchiveGates
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem part40 : toffoliCount (enter255Inv) = 20 ∧ measurementCount (enter255Inv) = 6 := by
  decide +kernel

theorem part41 : toffoliCount (leave240Inv) = 871 ∧ measurementCount (leave240Inv) = 315 := by
  decide +kernel

theorem part42 : toffoliCount (unrouted ⟨11,by decide⟩ 1 14) = 4312 ∧ measurementCount (unrouted ⟨11,by decide⟩ 1 14) = 2156 := by
  let j : Fin 23 := ⟨11,by decide⟩
  have h := (fixed_route j 1 14 (by decide)).2
  have hs := IntegerPacket.metrics (shape j) 1 14 (by decide +kernel)
  rw [h, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, hs.2.2.1, hs.2.2.2]
  dsimp only [j]
  decide +kernel

theorem part43 : toffoliCount (archiveRestore240 false) = 80 ∧ measurementCount (archiveRestore240 false) = 124 := by
  decide +kernel

theorem part44 : toffoliCount (Rolling1588.unpackAtTick false 230) = 11 ∧ measurementCount (Rolling1588.unpackAtTick false 230) = 2 := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.PartialCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialCosts
open Arithmetic MappedCompressed Partial StairArchiveGates
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem part45 : toffoliCount (unrouted ⟨11,by decide⟩ 0 1) = 308 ∧ measurementCount (unrouted ⟨11,by decide⟩ 0 1) = 154 := by
  let j : Fin 23 := ⟨11,by decide⟩
  have h := (fixed_route j 0 1 (by decide)).2
  have hs := IntegerPacket.metrics (shape j) 0 1 (by decide +kernel)
  rw [h, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, hs.2.2.1, hs.2.2.2]
  dsimp only [j]
  decide +kernel

theorem part46 : toffoliCount (enter240Inv) = 20 ∧ measurementCount (enter240Inv) = 6 := by
  decide +kernel

theorem part47 : toffoliCount (leave225Inv) = 820 ∧ measurementCount (leave225Inv) = 298 := by
  decide +kernel

theorem part48 : toffoliCount (unrouted ⟨10,by decide⟩ 1 14) = 4536 ∧ measurementCount (unrouted ⟨10,by decide⟩ 1 14) = 2268 := by
  let j : Fin 23 := ⟨10,by decide⟩
  have h := (fixed_route j 1 14 (by decide)).2
  have hs := IntegerPacket.metrics (shape j) 1 14 (by decide +kernel)
  rw [h, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2, hs.2.2.1, hs.2.2.2]
  dsimp only [j]
  decide +kernel

theorem part49 : toffoliCount (Rolling1588.unpackAtTick false 225) = 11 ∧ measurementCount (Rolling1588.unpackAtTick false 225) = 2 := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.PartialCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Control
open Partial HighBankControl Leave255Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def controls0 : List Wire := [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560]

theorem selection0 (key : Fin 16) :
    parity (fun q => decide (q = Leave255Join.tags.getD key 0)) controls0 = key.val.testBit 0 := by
  revert key
  decide +kernel

theorem away0 : 1613 ∉ controls0 ∧ ∀ q ∈ controls0, q ∉ bank0 := by decide +kernel

theorem on0 : ((leave255.drop 892).take 8) = toggles 1613 controls0 := by rfl
theorem off0 : ((leave255.drop 1236).take 8) = toggles 1613 controls0 := by rfl
theorem reverseOn0 : ((leave255Inv.drop 2266).take 8) = toggles 1613 controls0.reverse := by rfl
theorem reverseOff0 : ((leave255Inv.drop 2610).take 8) = toggles 1613 controls0.reverse := by rfl
theorem wrapped0 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls0)⟩
    let v := run (HighBankShift.program 1613 (bank0.getD · 0) 1 112) m u
    run ((leave255.drop 892).take 352) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave255.drop 892).take 352) =
      toggles 1613 controls0 ++ (HighBankShift.program 1613 (bank0.getD · 0) 1 112 ++ toggles 1613 controls0) := by rfl
  rw [exactSlice]
  apply wrapped layout0 (by decide) _ away0.1
  intro q hq i hi eq
  have h : i < bank0.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away0.2 q hq (eq ▸ List.getElem_mem h)


def controls1 : List Wire := [1563, 1564, 1567, 1568, 1571, 1572, 1575, 1560]

theorem selection1 (key : Fin 16) :
    parity (fun q => decide (q = Leave255Join.tags.getD key 0)) controls1 = key.val.testBit 1 := by
  revert key
  decide +kernel

theorem away1 : 1613 ∉ controls1 ∧ ∀ q ∈ controls1, q ∉ bank1 := by decide +kernel

theorem on1 : ((leave255.drop 1244).take 8) = toggles 1613 controls1 := by rfl
theorem off1 : ((leave255.drop 1591).take 8) = toggles 1613 controls1 := by rfl
theorem reverseOn1 : ((leave255Inv.drop 1911).take 8) = toggles 1613 controls1.reverse := by rfl
theorem reverseOff1 : ((leave255Inv.drop 2258).take 8) = toggles 1613 controls1.reverse := by rfl
theorem wrapped1 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls1)⟩
    let v := run (HighBankShift.program 1613 (bank1.getD · 0) 2 113) m u
    run ((leave255.drop 1244).take 355) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave255.drop 1244).take 355) =
      toggles 1613 controls1 ++ (HighBankShift.program 1613 (bank1.getD · 0) 2 113 ++ toggles 1613 controls1) := by rfl
  rw [exactSlice]
  apply wrapped layout1 (by decide) _ away1.1
  intro q hq i hi eq
  have h : i < bank1.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away1.2 q hq (eq ▸ List.getElem_mem h)


def controls2 : List Wire := [1565, 1566, 1567, 1568, 1573, 1574, 1575, 1560]

theorem selection2 (key : Fin 16) :
    parity (fun q => decide (q = Leave255Join.tags.getD key 0)) controls2 = key.val.testBit 2 := by
  revert key
  decide +kernel

theorem away2 : 1613 ∉ controls2 ∧ ∀ q ∈ controls2, q ∉ bank2 := by decide +kernel

theorem on2 : ((leave255.drop 1599).take 8) = toggles 1613 controls2 := by rfl
theorem off2 : ((leave255.drop 1952).take 8) = toggles 1613 controls2 := by rfl
theorem reverseOn2 : ((leave255Inv.drop 1550).take 8) = toggles 1613 controls2.reverse := by rfl
theorem reverseOff2 : ((leave255Inv.drop 1903).take 8) = toggles 1613 controls2.reverse := by rfl
theorem wrapped2 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls2)⟩
    let v := run (HighBankShift.program 1613 (bank2.getD · 0) 4 115) m u
    run ((leave255.drop 1599).take 361) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave255.drop 1599).take 361) =
      toggles 1613 controls2 ++ (HighBankShift.program 1613 (bank2.getD · 0) 4 115 ++ toggles 1613 controls2) := by rfl
  rw [exactSlice]
  apply wrapped layout2 (by decide) _ away2.1
  intro q hq i hi eq
  have h : i < bank2.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away2.2 q hq (eq ▸ List.getElem_mem h)


def controls3 : List Wire := [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]

theorem selection3 (key : Fin 16) :
    parity (fun q => decide (q = Leave255Join.tags.getD key 0)) controls3 = key.val.testBit 3 := by
  revert key
  decide +kernel

theorem away3 : 1613 ∉ controls3 ∧ ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel

theorem on3 : ((leave255.drop 1960).take 8) = toggles 1613 controls3 := by rfl
theorem off3 : ((leave255.drop 2325).take 8) = toggles 1613 controls3 := by rfl
theorem reverseOn3 : ((leave255Inv.drop 1177).take 8) = toggles 1613 controls3.reverse := by rfl
theorem reverseOff3 : ((leave255Inv.drop 1542).take 8) = toggles 1613 controls3.reverse := by rfl
theorem wrapped3 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls3)⟩
    let v := run (HighBankShift.program 1613 (bank3.getD · 0) 8 119) m u
    run ((leave255.drop 1960).take 373) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave255.drop 1960).take 373) =
      toggles 1613 controls3 ++ (HighBankShift.program 1613 (bank3.getD · 0) 8 119 ++ toggles 1613 controls3) := by rfl
  rw [exactSlice]
  apply wrapped layout3 (by decide) _ away3.1
  intro q hq i hi eq
  have h : i < bank3.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away3.2 q hq (eq ▸ List.getElem_mem h)


end ECDSAAdd.Entrant.StairPacket.Leave255Control

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Baselines Challenge
set_option maxHeartbeats 900000
theorem tick (p : IntegerPacket.Shape) (i : Nat) :
    gateSlots (skywalkIntegerTick (IntegerPacket.ports p i)) ≤ 5000 ∧
    gateSlots (skywalkIntegerUntick (IntegerPacket.ports p i)) ≤ 5000 := by
  let L := IntegerPacket.ports p i
  obtain ⟨f,r⟩ := signedRecord_gateSlots_le L.ext L.bSign L.history L.half L.b L.carry
  have ah : L.ah.length=p.mid+1 := by simp [L,IntegerPacket.ports,SkywalkIntegerLayout.ah]
  have bh : L.bh.length=p.mid+1 := by simp [L,IntegerPacket.ports,SkywalkIntegerLayout.bh]
  have a : L.half.length=p.mid+2 := by simp [SkywalkIntegerLayout.half,ah]
  have b : L.b.length=p.mid+2 := by simp [SkywalkIntegerLayout.b,bh]
  have w := p.midBound
  change gateSlots (skywalkIntegerTick L) ≤ 5000 ∧ gateSlots (skywalkIntegerUntick L) ≤ 5000
  simp only [skywalkIntegerTick,skywalkIntegerUntick,skywalkRoute,skywalkSignedHalf,
    gateSlots_append,swapRegisters_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,ah,bh,
    Nat.min_self]
  rw [a,b] at r
  rw [a] at f
  exact ⟨by omega,by omega⟩

theorem route (j : Fin 23) (i n : Nat) : gateSlots (routed j i n) ≤ 5000*n ∧
    gateSlots (unrouted j i n) ≤ 5000*n := by
  induction n generalizing i with
  | zero => exact ⟨by rfl,by rfl⟩
  | succ n ih =>
    have tail := ih (i+1)
    have t := tick (shape j) i
    simp only [routed,unrouted,gateSlots_append,rename_gateSlots,Nat.mul_succ]
    exact ⟨by omega,by omega⟩
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Barrel
open Partial Leave255Control Leave255Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev wire (i : Nat) := bank3.getD i 0
def passes0 : Program := []
def passes1 := passes0 ++ stage 1613 wire controls0 1 112
def passes2 := passes1 ++ stage 1613 wire controls1 2 113
def passes3 := passes2 ++ stage 1613 wire controls2 4 115
def passes4 := passes3 ++ stage 1613 wire controls3 8 119

theorem emitted : ((leave255.drop 892).take 1441) = passes4 := by rfl

theorem value (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^112) (h : holds wire 127 x s) (clean : s.basis 1613=false)
    (tags : ∀ q ∈ Leave255Join.tags, s.basis q = decide (q = Leave255Join.tags.getD key 0)) :
    Result wire 127 (x <<< key.val) s (run ((leave255.drop 892).take 1441) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 127 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 127 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 112+0 ≤ 112)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls0, q ∈ Leave255Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 127 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 112+(key.val % 2) ≤ 113)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls1, q ∈ Leave255Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 127 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 112+(key.val % 4) ≤ 115)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls2, q ∈ Leave255Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 127 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 112+(key.val % 8) ≤ 119)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls3, q ∈ Leave255Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave255Barrel

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialCosts
open Arithmetic MappedCompressed Partial StairArchiveGates
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.PartialCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part0 : gateSlots (portal225) ≤ 2030 := by decide +kernel

theorem part1 : gateSlots (enter225) ≤ 93 := by decide +kernel

theorem part2 : gateSlots (routed ⟨10,by decide⟩ 0 1) ≤ 5000 := (route ⟨10,by decide⟩ 0 1).1

theorem part3 : gateSlots (Rolling1588.packAtTick false 225) ≤ 156 := by decide +kernel

theorem part4 : gateSlots (routed ⟨10,by decide⟩ 1 14) ≤ 70000 := (route ⟨10,by decide⟩ 1 14).1
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part5 : gateSlots (leave225) ≤ 3489 := by decide +kernel

theorem part6 : gateSlots (enter240) ≤ 93 := by decide +kernel

theorem part7 : gateSlots (routed ⟨11,by decide⟩ 0 1) ≤ 5000 := (route ⟨11,by decide⟩ 0 1).1

theorem part8 : gateSlots (Rolling1588.packAtTick false 230) ≤ 156 := by decide +kernel

theorem part9 : gateSlots (archiveLoad240 false) ≤ 15988 := by
  have move : gateSlots moveLoad240 = 33 := by decide +kernel
  simp only [archiveLoad240,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load1_counts.2.2.2,move]
  decide
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part50 : gateSlots (unrouted ⟨10,by decide⟩ 0 1) ≤ 5000 := (route ⟨10,by decide⟩ 0 1).2

theorem part51 : gateSlots (enter225Inv) ≤ 93 := by decide +kernel

theorem part52 : gateSlots (portal225Inv) ≤ 2030 := by decide +kernel

theorem part53 : gateSlots (archiveRestore270 true) ≤ 12242 := by
  have move : gateSlots moveRestore270 = 54 := by decide +kernel
  simp only [archiveRestore270,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore0_counts.2.2.2,move]
  decide

theorem part54 : gateSlots (Rolling1588.unpackAtTick true 260) ≤ 166 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part10 : gateSlots (routed ⟨11,by decide⟩ 1 14) ≤ 70000 := (route ⟨11,by decide⟩ 1 14).1

theorem part11 : gateSlots (leave240) ≤ 3704 := by decide +kernel

theorem part12 : gateSlots (enter255) ≤ 93 := by decide +kernel

theorem part13 : gateSlots (routed ⟨12,by decide⟩ 0 1) ≤ 5000 := (route ⟨12,by decide⟩ 0 1).1

theorem part14 : gateSlots (Rolling1588.packAtTick false 245) ≤ 156 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part15 : gateSlots (archiveLoad255 false) ≤ 15988 := by
  have move : gateSlots moveLoad255 = 33 := by decide +kernel
  simp only [archiveLoad255,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load1_counts.2.2.2,move]
  decide

theorem part16 : gateSlots (routed ⟨12,by decide⟩ 1 14) ≤ 70000 := (route ⟨12,by decide⟩ 1 14).1

theorem part17 : gateSlots (leave255) ≤ 3837 := by decide +kernel

theorem part18 : gateSlots (park270) ≤ 9 := by decide +kernel

theorem part19 : gateSlots (portal270Inv) ≤ 2219 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part25 : gateSlots (archiveLoad240 true) ≤ 15978 := by
  have move : gateSlots moveLoad240 = 33 := by decide +kernel
  simp only [archiveLoad240,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load0_counts.2.2.2,move]
  decide

theorem part26 : gateSlots (Rolling1588.packAtTick true 245) ≤ 168 := by decide +kernel

theorem part27 : gateSlots (archiveLoad255 true) ≤ 15978 := by
  have move : gateSlots moveLoad255 = 33 := by decide +kernel
  simp only [archiveLoad255,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load0_counts.2.2.2,move]
  decide

theorem part28 : gateSlots (Rolling1588.packAtTick true 260) ≤ 168 := by decide +kernel

theorem part29 : gateSlots (archiveLoad270 true) ≤ 15978 := by
  have move : gateSlots moveLoad270 = 33 := by decide +kernel
  simp only [archiveLoad270,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load0_counts.2.2.2,move]
  decide
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part30 : gateSlots (archiveRestore270 false) ≤ 12262 := by
  have move : gateSlots moveRestore270 = 54 := by decide +kernel
  simp only [archiveRestore270,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore1_counts.2.2.2,move]
  decide

theorem part31 : gateSlots (Rolling1588.unpackAtTick false 260) ≤ 154 := by decide +kernel

theorem part32 : gateSlots (W.ReverseCarry.compactReceiverTick base 270) ≤ 6001 := by
  have h := W.ReverseCarry.compactReceiverTick_slots base 270 (by decide) base_pool_nodup
  have c := (W.compactTick_gateSlots_le base 270 (by decide)).2
  omega

theorem part33 : gateSlots (portal270) ≤ 2219 := by decide +kernel

theorem part34 : gateSlots (park270Inv) ≤ 9 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part35 : gateSlots (leave255Inv) ≤ 3838 := by decide +kernel

theorem part36 : gateSlots (unrouted ⟨12,by decide⟩ 1 14) ≤ 70000 := (route ⟨12,by decide⟩ 1 14).2

theorem part37 : gateSlots (archiveRestore255 false) ≤ 12262 := by
  have move : gateSlots moveRestore255 = 54 := by decide +kernel
  simp only [archiveRestore255,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore1_counts.2.2.2,move]
  decide

theorem part38 : gateSlots (Rolling1588.unpackAtTick false 245) ≤ 154 := by decide +kernel

theorem part39 : gateSlots (unrouted ⟨12,by decide⟩ 0 1) ≤ 5000 := (route ⟨12,by decide⟩ 0 1).2
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part40 : gateSlots (enter255Inv) ≤ 93 := by decide +kernel

theorem part41 : gateSlots (leave240Inv) ≤ 3705 := by decide +kernel

theorem part42 : gateSlots (unrouted ⟨11,by decide⟩ 1 14) ≤ 70000 := (route ⟨11,by decide⟩ 1 14).2

theorem part43 : gateSlots (archiveRestore240 false) ≤ 12262 := by
  have move : gateSlots moveRestore240 = 54 := by decide +kernel
  simp only [archiveRestore240,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore1_counts.2.2.2,move]
  decide

theorem part44 : gateSlots (Rolling1588.unpackAtTick false 230) ≤ 154 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part45 : gateSlots (unrouted ⟨11,by decide⟩ 0 1) ≤ 5000 := (route ⟨11,by decide⟩ 0 1).2

theorem part46 : gateSlots (enter240Inv) ≤ 93 := by decide +kernel

theorem part47 : gateSlots (leave225Inv) ≤ 3490 := by decide +kernel

theorem part48 : gateSlots (unrouted ⟨10,by decide⟩ 1 14) ≤ 70000 := (route ⟨10,by decide⟩ 1 14).2

theorem part49 : gateSlots (Rolling1588.unpackAtTick false 225) ≤ 154 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave255Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def ys : List Wire := [1703, 1704, 1705, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042]
def carries : List Wire := [1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1713, 1714, 1715, 1716, 1717, 1718]

theorem emitted : ((leave255.drop 334).take 558) = adjust ys carries 1709 1597 := by rfl
theorem combined : ((leave255.drop 334).take 1999) =
    adjust ys carries 1709 1597 ++ ((leave255.drop 892).take 1441) := by rfl

theorem result (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (one : ∀ q ∈ Leave255Join.tags, s.basis q = decide (q = Leave255Join.tags.getD key 0)) :
    let x := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    Result wire 127 (x <<< key.val) s (run ((leave255.drop 334).take 1999) m s) := by
  let p := adjust ys carries 1709 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1709 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 112, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 127, 112 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^112 := regValue_lt ys t.basis
  have data : holds wire 127 x t := by
    intro i hi
    by_cases lo : i < 112
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 112 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave255Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave255Join.tags, t.basis q = decide (q = Leave255Join.tags.getD key 0) :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (one _ h)
  have action := value key x t (m.drop (measurementCount p)) small data cold keys
  have initial : x = adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨action.bits,action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 112 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave255High

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Word
open Partial Leave255Join Leave255Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev row (i : Fin 18) := columns[i.val]'(i.isLt)
def hot (key : Fin 16) (q : Wire) := decide (q = tags.getD key 0)

theorem combine (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis 1709).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614=false) :
    let out := run ((leave255.drop 2335).take 108) m s
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
  have geom : ∀ i : Fin 18, (row i).shadow=416+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have hits : ∀ r ∈ columns, ∀ q ∈ r.hot, q∈tags := by decide +kernel
  have members : ∀ q ∈ tags, ∀ i : Fin 18, q≠416+i.val := by decide +kernel
  have tx : ∀ i j : Fin 18, wire i.val ≠ 416+j.val := by decide +kernel
  have cold : ∀ i : Fin 18, 1614 ≠ 416+i.val := by decide +kernel
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
  rw [Leave255Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero]
  refine ⟨word.1.trans z.1,fun i => word.2.1 i.val i.isLt,?_⟩
  intro q away
  have safe (j : Fin 18) : q ≠ 416+j.val := by
    rw [← (geom j).1]
    exact (away _ (List.getElem_mem j.isLt)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe ⟨key.val,by omega⟩) (safe ⟨key.val+1,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave255Word

end
end
-- ==== w4: GateMirror core and lemma blocks, moved verbatim from Window (record lines 8320..12146) ====
section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
open Arithmetic
inductive Gate where
  | x (t:Wire)
  | cx (a t:Wire)
  | ccx (a b t:Wire)
  | make (a b t:Wire)
  | pop (a b t:Wire)
  deriving DecidableEq

def erase (a b t:Wire):Instr := .measureX t [] [.CZ a b]
def front : Gate→Instr
  | .x t=>.X t
  | .cx a t=>.CX a t
  | .ccx a b t | .make a b t=>.CCX a b t
  | .pop a b t=>erase a b t
def back : Gate→Instr
  | .x t=>.X t
  | .cx a t=>.CX a t
  | .ccx a b t | .pop a b t=>.CCX a b t
  | .make a b t=>erase a b t
def proper : Gate→Bool
  | .x _=>true
  | .cx a t=>decide (a≠t)
  | .ccx a b t | .make a b t | .pop a b t=>decide (a≠t ∧ b≠t)
def ValueOK (s:State):Gate→Prop
  | .pop a b t=>s.basis t=(s.basis a && s.basis b)
  | _=>True
def Fresh (s:State):Gate→Prop
  | .make _ _ t=>s.basis t=false
  | _=>True
def forward (ops:List Gate):Program:=ops.map front
def inverse (ops:List Gate):Program:=(ops.map back).reverse
def transition (g:Gate) (s:State):State:=run [front g] [] s
def Prepared (s:State):List Gate→Prop
  | []=>True
  | g::gs=>ValueOK s g ∧ Prepared (transition g s) gs
theorem no_phase (ops:List Gate) (s:State):(run (forward ops) [] s).phase=s.phase:=by
  induction ops generalizing s with
  | nil=>rfl
  | cons g gs ih=>
    change (run ([front g]++forward gs) [] s).phase=_
    rw [run_append,run_take,List.drop_nil,ih]
    cases g <;> first | rfl | simp [front,erase,run,measureAndCorrect,ECDSAAdd.correct]
theorem head_default (g:Gate) (s:State) (correct:ValueOK s g) (phys:proper g=true) (m:List Bool):
    run [front g] m s=transition g s:=by
  cases g with
  | x|cx|ccx|make=>rfl
  | pop a b t=>
    have dist : a≠t ∧ b≠t := of_decide_eq_true phys
    change s.basis t=(s.basis a && s.basis b) at correct
    cases m with
    | nil=>rfl
    | cons v xs=>
      cases v
      · rfl
      · simp [front,erase,transition,run,measureAndCorrect,correct,ECDSAAdd.correct,writeBit,dist.1,dist.2]
theorem all_prepared (ops:List Gate) (s:State) (phys:∀g∈ops,proper g=true)
    (quiet:∀m,(run (forward ops) m s).phase=s.phase):Prepared s ops:=by
  induction ops generalizing s with
  | nil=>trivial
  | cons g gs ih=>
    have hp:=phys g (by simp)
    have root : ∀m,(run (forward gs) (m.drop (measurementCount [front g])) (run [front g] m s)).phase=s.phase:=by
      intro m
      have eq:=quiet m
      change (run ([front g]++forward gs) m s).phase=_ at eq
      rwa [run_append,run_take] at eq
    have val:ValueOK s g:=by
      cases g with
      | x|cx|ccx|make=>trivial
      | pop a b t=>
        have rel:=root [true]
        change (run (forward gs) [] _).phase=_ at rel
        rw [no_phase] at rel
        have dist : a≠t ∧ b≠t := of_decide_eq_true hp
        change s.basis t=(s.basis a && s.basis b)
        simp [front,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,dist.1,dist.2] at rel
        revert rel;cases s.phase <;> cases s.basis t <;> cases s.basis a <;> cases s.basis b <;> decide
    refine ⟨val,ih _ (fun k h=>phys k (by simp [h])) ?_⟩
    intro m
    let tape:=(List.replicate (measurementCount [front g]) false)++m
    have drop:tape.drop (measurementCount [front g])=m:=by simp [tape]
    have rel:=root tape
    rw [drop,head_default g s val hp] at rel
    have base:(transition g s).phase=s.phase:=by cases g <;> first | rfl | simp [front,transition,erase,run,measureAndCorrect,ECDSAAdd.correct]
    exact rel.trans base.symm

end ECDSAAdd.Entrant.StairPacket.GateMirror

end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
open Arithmetic
private theorem reset (f:BasisState) (t:Wire) (b:Bool) :
    writeBit (writeBit f t b) t (f t)=f:=by
  funext q
  by_cases e:q=t <;> simp [writeBit,e]
private theorem restore (s:State) (t:Wire) (b:Bool) :
    (⟨s.phase,writeBit (writeBit s.basis t b) t (s.basis t)⟩:State)=s:=by rw [reset]
theorem undo (g:Gate) (s:State) (hp:proper g=true) (hv:ValueOK s g) (hf:Fresh s g) (m:List Bool):
    run [back g] m (transition g s)=s:=by
  cases g with
  | x t=>
    simp [transition,front,back,run,writeBit]
  | cx a t=>
    have ha:a≠t:=of_decide_eq_true hp
    simp [transition,front,back,run,writeBit,ha]
  | ccx a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    simp [transition,front,back,run,writeBit,ha,hb]
  | pop a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    change s.basis t=(s.basis a && s.basis b) at hv
    simpa [transition,front,back,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ha,hb,hv] using restore s t false
  | make a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    change s.basis t=false at hf
    have h:=restore s t (s.basis a && s.basis b)
    cases e:m.head?.getD false <;>
      simpa [transition,front,back,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ha,hb,hf,e] using h

def Ready (s:State):List Gate→Prop
  | []=>True
  | g::gs=>Fresh s g ∧ Ready (transition g s) gs

theorem invert (ops:List Gate) (s:State) (phys:∀g∈ops,proper g=true)
    (ok:Prepared s ops) (clean:Ready s ops) (m n:List Bool):
    run (inverse ops) n (run (forward ops) m s)=s:=by
  induction ops generalizing s m n with
  | nil=>rfl
  | cons g gs ih=>
    have hp:=phys g (by simp)
    change run ((back g::gs.map back).reverse) n (run ([front g]++forward gs) m s)=s
    rw [List.reverse_cons,run_append,run_append,run_take,run_take]
    rw [head_default g s ok.1 hp]
    rw [show (gs.map back).reverse=inverse gs from rfl,
      ih _ (fun k h=>phys k (by simp [h])) ok.2 clean.2]
    exact undo g s hp ok.1 clean.1 _

end ECDSAAdd.Entrant.StairPacket.GateMirror

end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def target:Gate→Wire
  | .x t | .cx _ t | .ccx _ _ t | .make _ _ t | .pop _ _ t=>t
def WritesZero:Gate→Bool
  | .pop ..=>true
  | _=>false
def NeedsZero:Gate→Bool
  | .make ..=>true
  | _=>false
def zeros (s:State) (ws:List Wire):Prop:=∀q∈ws,s.basis q=false
def before (g:Gate) (ws:List Wire):List Wire:=
  let surviving:=ws.filter (· != target g)
  if NeedsZero g then target g::surviving else surviving
def safe (g:Gate) (ws:List Wire):Bool:=proper g && (WritesZero g || !(ws.contains (target g)))
theorem before_step (g:Gate) (ws:List Wire) (s:State) (hg:safe g ws=true)
    (h:zeros s (before g ws)): proper g=true ∧ Fresh s g ∧ zeros (transition g s) ws:=by
  have hh:=Bool.and_eq_true_iff.mp hg
  refine ⟨hh.1,?_,?_⟩
  · cases g <;> first | trivial | exact h _ (by simp [before,NeedsZero,target])
  · intro q hq
    by_cases eq:q=target g
    · subst q
      have hz:WritesZero g=true:=by simpa [hq] using hh.2
      cases g <;> simp [WritesZero] at hz
      simp [transition,front,run,erase,measureAndCorrect,target,writeBit]
    · have hz:s.basis q=false:=by
        apply h
        cases hneeds:NeedsZero g <;> simp [before,hneeds,hq,eq]
      cases g <;> simp [target] at eq <;>
        simp [transition,front,run,erase,measureAndCorrect,writeBit,eq,hz]
def checked (gs:List Gate) (post:List Wire):Option (List Wire):=
  match gs with
  | []=>some post
  | g::rest=>do
    let ws←checked rest post
    if safe g ws then some (before g ws) else none
theorem checked_sound (gs:List Gate) (s:State) (pre post:List Wire)
    (hc:checked gs post=some pre) (hi:zeros s pre):
    (∀g∈gs,proper g=true) ∧ Ready s gs ∧ zeros (run (forward gs) [] s) post:=by
  induction gs generalizing s pre with
  | nil=>
    simp [checked] at hc
    exact ⟨by simp, trivial,hc ▸ hi⟩
  | cons g gs ih=>
    cases hx:checked gs post with
    | none=>simp [checked,hx] at hc
    | some ws=>
      by_cases hv:safe g ws=true
      · simp [checked,hx,hv] at hc
        subst pre
        obtain ⟨hp,hf,hz⟩:=before_step g ws s hv hi
        obtain ⟨hps,hr,hend⟩:=ih (transition g s) ws hx hz
        refine ⟨fun k hk=>?_,⟨hf,hr⟩,?_⟩
        · rcases List.mem_cons.mp hk with rfl|hh
          · exact hp
          · exact hps k hh
        · change zeros (run ([front g]++forward gs) [] s) post
          rwa [run_append,run_take,List.drop_nil]
      · simp [checked,hx,hv] at hc

theorem check_join (as bs:List Gate) (first middle last:List Wire)
    (ha:checked as middle=some first) (hb:checked bs last=some middle):
    checked (as++bs) last=some first:=by
  induction as generalizing first with
  | nil=>simpa [checked] using hb.trans ha
  | cons g gs ih=>
    cases hh:checked gs middle with
    | none=>simp [checked,hh] at ha
    | some ws=>
      have total:=ih ws hh
      simpa only [List.cons_append,checked,total] using (show (do
        let xs←some ws
        if safe g xs then some (before g xs) else none)=some first by simpa only [checked,hh] using ha)

theorem ready_append (as bs:List Gate) (s:State) (ha:Ready s as)
    (hb:Ready (run (forward as) [] s) bs):Ready s (as++bs):=by
  induction as generalizing s with
  | nil=>exact hb
  | cons g gs ih=>
    refine ⟨ha.1,ih _ ha.2 ?_⟩
    change Ready (run ([front g]++forward gs) [] s) bs at hb
    rwa [run_append,run_take,List.drop_nil] at hb
end ECDSAAdd.Entrant.StairPacket.GateMirror

end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def Masked (s:State) (mask:Nat):Prop:=∀q,mask.testBit q=true → s.basis q=false
def addBit (m q:Nat):Nat:=m ||| 2^q
def cutBit (m q:Nat):Nat:=if m.testBit q then m ^^^ 2^q else m
theorem add_bit (m t q:Nat):(addBit m t).testBit q=(decide (q=t) || m.testBit q):=by
  rw [addBit,Nat.testBit_or,Nat.testBit_two_pow]
  by_cases h:q=t
  · subst q;simp
  · simp [h,Ne.symm h]
theorem cut_bit (m t q:Nat):(cutBit m t).testBit q=(!decide (q=t) && m.testBit q):=by
  by_cases h:q=t
  · subst q
    cases b:m.testBit t <;> simp [cutBit,b,Nat.testBit_xor]
  · by_cases b:m.testBit t=true <;> simp [cutBit,b,h,Ne.symm h,Nat.testBit_xor]
def bitBefore (g:Gate) (m:Nat):Nat:=if NeedsZero g then addBit m (target g) else cutBit m (target g)
def bitSafe (g:Gate) (m:Nat):Bool:=proper g && (WritesZero g || !m.testBit (target g))
theorem bitStep (g:Gate) (ws:Nat) (s:State) (hg:bitSafe g ws=true)
    (h:Masked s (bitBefore g ws)):proper g=true ∧ Fresh s g ∧ Masked (transition g s) ws:=by
  have hh:=Bool.and_eq_true_iff.mp hg
  refine ⟨hh.1,?_,?_⟩
  · cases g <;> first | trivial | exact h _ (by simp [bitBefore,NeedsZero,target,add_bit])
  · intro q hq
    by_cases eq:q=target g
    · subst q
      have hz:WritesZero g=true:=by simpa [hq] using hh.2
      cases g <;> simp [WritesZero] at hz
      simp [transition,front,run,erase,measureAndCorrect,target,writeBit]
    · have hz:s.basis q=false:=by
        apply h
        cases hneeds:NeedsZero g <;> simp [bitBefore,hneeds,hq,eq,add_bit,cut_bit]
      cases g <;> simp [target] at eq <;>
        simp [transition,front,run,erase,measureAndCorrect,writeBit,eq,hz]
def bitCheck (gs:List Gate) (post:Nat):Option Nat:=
  match gs with
  | []=>some post
  | g::rest=>do
    let ws←bitCheck rest post
    if bitSafe g ws then some (bitBefore g ws) else none
theorem bit_sound (gs:List Gate) (s:State) (pre post:Nat)
    (hc:bitCheck gs post=some pre) (hi:Masked s pre):
    (∀g∈gs,proper g=true) ∧ Ready s gs ∧ Masked (run (forward gs) [] s) post:=by
  induction gs generalizing s pre with
  | nil=>
    simp [bitCheck] at hc
    exact ⟨by simp, trivial,hc ▸ hi⟩
  | cons g gs ih=>
    cases hx:bitCheck gs post with
    | none=>simp [bitCheck,hx] at hc
    | some ws=>
      by_cases hv:bitSafe g ws=true
      · simp [bitCheck,hx,hv] at hc
        subst pre
        obtain ⟨hp,hf,hz⟩:=bitStep g ws s hv hi
        obtain ⟨hps,hr,hend⟩:=ih (transition g s) ws hx hz
        refine ⟨fun k hk=>?_,⟨hf,hr⟩,?_⟩
        · rcases List.mem_cons.mp hk with rfl|hh
          · exact hp
          · exact hps k hh
        · change Masked (run ([front g]++forward gs) [] s) post
          rwa [run_append,run_take,List.drop_nil]
      · simp [bitCheck,hx,hv] at hc

theorem bit_join (as bs:List Gate) (first middle last:Nat)
    (ha:bitCheck as middle=some first) (hb:bitCheck bs last=some middle):
    bitCheck (as++bs) last=some first:=by
  induction as generalizing first with
  | nil=>simpa [bitCheck] using hb.trans ha
  | cons g gs ih=>
    cases hh:bitCheck gs middle with
    | none=>simp [bitCheck,hh] at ha
    | some ws=>
      have total:=ih ws hh
      simpa only [List.cons_append,bitCheck,total] using (show (do
        let xs←some ws
        if bitSafe g xs then some (bitBefore g xs) else none)=some first by simpa only [bitCheck,hh] using ha)

theorem subMask {s:State} {small big:Nat} (test:small &&& big=small) (h:Masked s big):Masked s small:=by
  intro q hq
  have v:=congrArg (fun n:Nat=>n.testBit q) test
  simp [Nat.testBit_and,hq] at v
  exact h q v
theorem bothMasks {s:State} {a b:Nat} (ha:Masked s a) (hb:Masked s b):Masked s (a ||| b):=by
  intro q hq
  rw [Nat.testBit_or,Bool.or_eq_true] at hq
  exact hq.elim (ha q) (hb q)
def interval (lo width:Nat):Nat:=(2^width-1) <<< lo
theorem fromRange {s:State} {lo width:Nat} (h:∀q,lo≤q→q<lo+width→s.basis q=false):
    Masked s (interval lo width):=by
  intro q hq
  simp only [interval,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one] at hq
  apply h <;> simp_all
  omega
def maskSites (ws:List Wire):Nat:=ws.foldr (fun q m=>addBit m q) 0
theorem fromList {s:State} {ws:List Wire} (h:zeros s ws):Masked s (maskSites ws):=by
  induction ws with
  | nil=>intro q hq;simp [maskSites] at hq
  | cons a as ih=>
    intro q hq
    change (addBit (maskSites as) a).testBit q=true at hq
    rw [add_bit,Bool.or_eq_true] at hq
    rcases hq with eq|hv
    · exact h q (by simp [of_decide_eq_true eq])
    · exact ih (fun k hh=>h k (by simp [hh])) q hv
theorem fwAppend (a b:List Gate):forward (a++b)=forward a ++ forward b:=List.map_append
theorem bwAppend (a b:List Gate):inverse (a++b)=inverse b ++ inverse a:=by
  simp only [inverse,List.map_append,List.reverse_append]
theorem fwNil:forward []=[]:=rfl
theorem bwNil:inverse []=[]:=rfl
end ECDSAAdd.Entrant.StairPacket.GateMirror

end

-- ==== leave-move: c9cc6a76 R1 MoveChain (controlled-move bridge) and its GateMirror form, verbatim ====
section

namespace ECDSAAdd.Entrant.StairPacket.MoveChain

/-- (tag, cell). A hot tag moves its cell into the clean wire `c`. -/
abbrev Row := Wire × Wire

/-- Reference shape: one-hot mux into `c`. -/
def mux (c : Wire) (rs : List Row) : Program := rs.map (fun r => Instr.CCX r.1 r.2 c)
/-- Reference shape: the later clears of the selected cell. -/
def clears (c : Wire) (rs : List Row) : Program := rs.map (fun r => Instr.CCX r.1 c r.2)
/-- Physical shape: one controlled swap (one Toffoli) per row. -/
def rows (c : Wire) : List Row → Program
  | [] => []
  | r :: rs => .CX r.2 c :: .CCX r.1 c r.2 :: .CX r.2 c :: rows c rs
/-- Reference digit pass: clear of row i followed by the kept gate i. -/
def weave (c : Wire) : List Row → Program → Program
  | r :: rs, k :: ks => .CCX r.1 c r.2 :: k :: weave c rs ks
  | _, _ => []

def clr (c : Wire) (r : Row) (s : State) : State :=
  ⟨s.phase, writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))⟩
def clrAll (c : Wire) (rs : List Row) (s : State) : State := rs.foldl (fun t r => clr c r t) s
def muxS (c : Wire) (r : Row) (s : State) : State :=
  ⟨s.phase, writeBit s.basis c (s.basis c ^^ (s.basis r.1 && s.basis r.2))⟩
def rowS (c : Wire) (r : Row) (s : State) : State :=
  run [.CX r.2 c, .CCX r.1 c r.2, .CX r.2 c] [] s

def corrFree (a : Wire) : List Correction → Bool
  | [] => true
  | .Z t :: cs => decide (t ≠ a) && corrFree a cs
  | .CZ x y :: cs => decide (x ≠ a) && (decide (y ≠ a) && corrFree a cs)
/-- A gate that commutes with the clear of row `r`: it never writes the tag or `c` and never reads the cell. -/
def quiet (c : Wire) (r : Row) : Instr → Bool
  | .X t => decide (t ≠ r.1) && decide (t ≠ c)
  | .CX a t => decide (t ≠ r.1) && (decide (t ≠ c) && decide (a ≠ r.2))
  | .CCX a b t => decide (t ≠ r.1) && (decide (t ≠ c) && (decide (a ≠ r.2) && decide (b ≠ r.2)))
  | .measureX t c0 c1 => decide (t ≠ r.1) && (decide (t ≠ c) && (decide (t ≠ r.2) && (corrFree r.2 c0 && corrFree r.2 c1)))
def woven (c : Wire) : List Row → Program → Bool
  | _ :: rs, k :: ks => rs.all (fun r => [k].all (quiet c r)) && woven c rs ks
  | [], [] => true
  | _, _ => false
/-- Tags, cells and `c` are pairwise different wires; tags are never cells. -/
def apart (c : Wire) (rs : List Row) : Bool :=
  rs.all (fun r => decide (r.1 ≠ c) && (decide (r.2 ≠ c) && (decide (r.1 ≠ r.2) && rs.all (fun r' => decide (r'.1 ≠ r.2)))))
def lone : List Row → Bool
  | [] => true
  | r :: rs => rs.all (fun r' => decide (r'.2 ≠ r.2)) && lone rs

theorem wb_same (b : BasisState) (w : Wire) (v : Bool) : writeBit b w v w = v := by simp [writeBit]
theorem wb_other (b : BasisState) (w q : Wire) (v : Bool) (h : q ≠ w) : writeBit b w v q = b q := by
  simp [writeBit, h]
theorem wb_keep (b : BasisState) (w : Wire) : writeBit b w (b w) = b := by
  funext q
  by_cases e : q = w
  · rw [e, wb_same]
  · rw [wb_other b w q _ e]

theorem clears_run (c : Wire) (rs : List Row) (m : List Bool) (s : State) :
    run (clears c rs) m s = clrAll c rs s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (clr c r s)
theorem rows_count (c : Wire) (rs : List Row) : measurementCount (rows c rs) = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih
theorem mux_count (c : Wire) (rs : List Row) : measurementCount (mux c rs) = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih
theorem weave_count (c : Wire) (rs : List Row) (ks : Program) (h : woven c rs ks = true) :
    measurementCount (weave c rs ks) = measurementCount ks := by
  induction rs generalizing ks with
  | nil =>
    cases ks with
    | nil => rfl
    | cons k ks => exact absurd h (by simp [woven])
  | cons r rs ih =>
    cases ks with
    | nil => exact absurd h (by simp [woven])
    | cons k ks =>
      have t : woven c rs ks = true := (Bool.and_eq_true_iff.mp h).2
      have e := ih ks t
      show measurementCount (k :: weave c rs ks) = measurementCount (k :: ks)
      cases k <;> simp only [measurementCount, e]

/-! Cold rows do nothing. -/
theorem clr_cold (c : Wire) (r : Row) (s : State) (off : s.basis r.1 = false) : clr c r s = s := by
  unfold clr
  rw [off, Bool.false_and, Bool.xor_false, wb_keep]
theorem muxS_cold (c : Wire) (r : Row) (s : State) (off : s.basis r.1 = false) : muxS c r s = s := by
  unfold muxS
  rw [off, Bool.false_and, Bool.xor_false, wb_keep]
theorem muxS_frame (c : Wire) (r : Row) (s : State) (q : Wire) (h : q ≠ c) : (muxS c r s).basis q = s.basis q :=
  wb_other _ _ _ _ h
theorem clr_frame (c : Wire) (r : Row) (s : State) (q : Wire) (h : q ≠ r.2) : (clr c r s).basis q = s.basis q :=
  wb_other _ _ _ _ h
theorem rowS_cold (c : Wire) (r : Row) (s : State) (off : s.basis r.1 = false) (tc : r.1 ≠ c) (ac : r.2 ≠ c) :
    rowS c r s = s := by
  have e1 : (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 = false := (wb_other _ _ _ _ tc).trans off
  have e2 : (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 = s.basis r.2 := wb_other _ _ _ _ ac
  show (⟨s.phase, writeBit (writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) c
      ((writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) c ^^
       (writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) r.2)⟩ : State) = s
  rw [e1, Bool.false_and, Bool.xor_false, wb_keep, wb_same, e2]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases e : q = c
  · rw [e, wb_same]
    cases s.basis c <;> cases s.basis r.2 <;> rfl
  · rw [wb_other _ _ _ _ e, wb_other _ _ _ _ e]
/-- A hot row with `c` clean is the mux step followed by the clear. -/
theorem rowS_hot (c : Wire) (r : Row) (s : State) (on : s.basis r.1 = true) (clean : s.basis c = false)
    (tc : r.1 ≠ c) (ac : r.2 ≠ c) (_ta : r.1 ≠ r.2) : rowS c r s = clr c r (muxS c r s) := by
  have ca : c ≠ r.2 := fun e => ac e.symm
  apply congrArg (State.mk s.phase)
  funext q
  show writeBit (writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) c
      ((writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) c ^^
       (writeBit (writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2
      ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ s.basis r.2)) r.1 && (writeBit s.basis c (s.basis c ^^ s.basis r.2)) c))) r.2) q =
    writeBit (writeBit s.basis c (s.basis c ^^ (s.basis r.1 && s.basis r.2))) r.2
      ((writeBit s.basis c (s.basis c ^^ (s.basis r.1 && s.basis r.2))) r.2 ^^
        ((writeBit s.basis c (s.basis c ^^ (s.basis r.1 && s.basis r.2))) r.1 &&
          (writeBit s.basis c (s.basis c ^^ (s.basis r.1 && s.basis r.2))) c)) q
  rw [wb_other _ c r.1 _ tc, wb_other _ c r.1 _ tc, wb_other _ c r.2 _ ac, wb_other _ c r.2 _ ac,
    wb_same, wb_same, wb_same, wb_other _ r.2 c _ ca, wb_same, on, clean]
  by_cases e : q = c
  · rw [e, wb_same, wb_other _ r.2 c _ ca, wb_same]
    cases s.basis r.2 <;> rfl
  · rw [wb_other _ c q _ e]
    by_cases e2 : q = r.2
    · rw [e2, wb_same, wb_same]
      cases s.basis r.2 <;> rfl
    · rw [wb_other _ r.2 q _ e2, wb_other _ r.2 q _ e2, wb_other _ c q _ e, wb_other _ c q _ e]

theorem rows_cold (c : Wire) (rs : List Row) (m : List Bool) (s : State)
    (off : ∀ r ∈ rs, s.basis r.1 = false ∧ r.1 ≠ c ∧ r.2 ≠ c) : run (rows c rs) m s = s := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := off r (List.mem_cons_self ..)
    show run (rows c rs) m (rowS c r s) = s
    rw [rowS_cold c r s h.1 h.2.1 h.2.2]
    exact ih (fun x hx => off x (List.mem_cons_of_mem _ hx))
theorem mux_cold (c : Wire) (rs : List Row) (m : List Bool) (s : State)
    (off : ∀ r ∈ rs, s.basis r.1 = false) : run (mux c rs) m s = s := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show run (mux c rs) m (muxS c r s) = s
    rw [muxS_cold c r s (off r (List.mem_cons_self ..))]
    exact ih (fun x hx => off x (List.mem_cons_of_mem _ hx))
theorem clrAll_cold (c : Wire) (rs : List Row) (s : State)
    (off : ∀ r ∈ rs, s.basis r.1 = false) : clrAll c rs s = s := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show clrAll c rs (clr c r s) = s
    rw [clr_cold c r s (off r (List.mem_cons_self ..))]
    exact ih (fun x hx => off x (List.mem_cons_of_mem _ hx))
theorem mux_frame (c : Wire) (rs : List Row) (m : List Bool) (s : State) (q : Wire) (h : q ≠ c) :
    (run (mux c rs) m s).basis q = s.basis q := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact (ih (muxS c r s)).trans (muxS_frame c r s q h)

/-- The move lemma: with `c` clean and every hot tag pointing at the same cell, the swap rows equal the mux
followed by all clears. -/
theorem move (c : Wire) (rs : List Row) (m : List Bool) (s : State) (a0 : Wire)
    (sep : ∀ r ∈ rs, r.1 ≠ c ∧ r.2 ≠ c ∧ r.1 ≠ r.2) (cross : ∀ r ∈ rs, ∀ r' ∈ rs, r'.1 ≠ r.2)
    (nd : lone rs = true) (clean : s.basis c = false)
    (sel : ∀ r ∈ rs, s.basis r.1 = true → r.2 = a0) :
    run (rows c rs) m s = clrAll c rs (run (mux c rs) m s) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := sep r (List.mem_cons_self ..)
    have tailSep : ∀ x ∈ rs, x.1 ≠ c ∧ x.2 ≠ c ∧ x.1 ≠ x.2 := fun x hx => sep x (List.mem_cons_of_mem _ hx)
    have nd2 := Bool.and_eq_true_iff.mp nd
    show run (rows c rs) m (rowS c r s) = clrAll c rs (clr c r (run (mux c rs) m (muxS c r s)))
    cases on : s.basis r.1 with
    | false =>
      rw [rowS_cold c r s on hr.1 hr.2.1, muxS_cold c r s on,
        clr_cold c r _ ((mux_frame c rs m s r.1 hr.1).trans on)]
      exact ih tailSep (fun x hx y hy => cross x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        nd2.2 (fun x hx => sel x (List.mem_cons_of_mem _ hx))
    | true =>
      have here : r.2 = a0 := sel r (List.mem_cons_self ..) on
      have cold : ∀ x ∈ rs, s.basis x.1 = false := by
        intro x hx
        cases ox : s.basis x.1 with
        | false => rfl
        | true =>
          have there : x.2 = a0 := sel x (List.mem_cons_of_mem _ hx) ox
          exact absurd (there.trans here.symm) (of_decide_eq_true (List.all_eq_true.mp nd2.1 x hx))
      have coldMux : ∀ x ∈ rs, (muxS c r s).basis x.1 = false := fun x hx =>
        (muxS_frame c r s x.1 (tailSep x hx).1).trans (cold x hx)
      have coldEnd : ∀ x ∈ rs, (clr c r (muxS c r s)).basis x.1 = false := fun x hx =>
        (clr_frame c r _ x.1 (cross r (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx))).trans (coldMux x hx)
      rw [mux_cold c rs m _ coldMux, clrAll_cold c rs _ coldEnd, rowS_hot c r s on clean hr.1 hr.2.1 hr.2.2]
      exact rows_cold c rs m _ (fun x hx => ⟨coldEnd x hx, (tailSep x hx).1, (tailSep x hx).2.1⟩)

/-! Clears commute with every quiet gate, for every measurement record. -/
theorem corr_comm (c : Wire) (r : Row) (cs : List Correction) (h : corrFree r.2 cs = true) (s : State) :
    ECDSAAdd.correct cs (clr c r s) = clr c r (ECDSAAdd.correct cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons x cs ih =>
    cases x with
    | Z t =>
      have hh := Bool.and_eq_true_iff.mp h
      have ta : t ≠ r.2 := of_decide_eq_true hh.1
      show ECDSAAdd.correct cs ⟨(clr c r s).phase ^^ (clr c r s).basis t, (clr c r s).basis⟩ =
        clr c r (ECDSAAdd.correct cs ⟨s.phase ^^ s.basis t, s.basis⟩)
      rw [← ih hh.2, clr_frame c r s t ta]
      rfl
    | CZ x y =>
      have hh := Bool.and_eq_true_iff.mp h
      have h2 := Bool.and_eq_true_iff.mp hh.2
      have xa : x ≠ r.2 := of_decide_eq_true hh.1
      have ya : y ≠ r.2 := of_decide_eq_true h2.1
      show ECDSAAdd.correct cs ⟨(clr c r s).phase ^^ ((clr c r s).basis x && (clr c r s).basis y), (clr c r s).basis⟩ =
        clr c r (ECDSAAdd.correct cs ⟨s.phase ^^ (s.basis x && s.basis y), s.basis⟩)
      rw [← ih h2.2, clr_frame c r s x xa, clr_frame c r s y ya]
      rfl

/-- Two xor-writes commute when neither value reads the other target. -/
theorem xor_comm (b : BasisState) (t u : Wire) (x y x' y' : Bool)
    (hx : x' = x) (hy : y' = y) :
    writeBit (writeBit b u (b u ^^ y)) t ((writeBit b u (b u ^^ y)) t ^^ x') =
      writeBit (writeBit b t (b t ^^ x)) u ((writeBit b t (b t ^^ x)) u ^^ y') := by
  subst hx; subst hy
  funext q
  by_cases e : q = t
  · by_cases f : q = u
    · have tu : t = u := e.symm.trans f
      subst tu
      rw [e, wb_same, wb_same, wb_same, wb_same]
      cases b t <;> cases x' <;> cases y' <;> rfl
    · have tu : t ≠ u := fun h => f (e.trans h)
      rw [e, wb_same, wb_other _ u t _ tu, wb_other _ u t _ tu, wb_same]
  · by_cases f : q = u
    · have ut : u ≠ t := fun h => e (f.trans h)
      rw [f, wb_other _ t u _ ut, wb_same, wb_same, wb_other _ t u _ ut]
    · rw [wb_other _ t q _ e, wb_other _ u q _ f, wb_other _ u q _ f, wb_other _ t q _ e]

theorem step_comm (c : Wire) (r : Row) (g : Instr) (h : quiet c r g = true) (m : List Bool) (s : State) :
    run [g] m (clr c r s) = clr c r (run [g] m s) := by
  cases g with
  | X t =>
    have hh := Bool.and_eq_true_iff.mp h
    have t1 : t ≠ r.1 := of_decide_eq_true hh.1
    have tc : t ≠ c := of_decide_eq_true hh.2
    apply congrArg (State.mk s.phase)
    show writeBit (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t
        (!(writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t) =
      writeBit (writeBit s.basis t (!s.basis t)) r.2 ((writeBit s.basis t (!s.basis t)) r.2 ^^
        ((writeBit s.basis t (!s.basis t)) r.1 && (writeBit s.basis t (!s.basis t)) c))
    rw [wb_other _ t r.1 _ (fun e => t1 e.symm), wb_other _ t c _ (fun e => tc e.symm),
      ← Bool.xor_true, ← Bool.xor_true (s.basis t)]
    exact xor_comm s.basis t r.2 true _ true _ rfl rfl
  | CX a t =>
    have hh := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp hh.2
    have t1 : t ≠ r.1 := of_decide_eq_true hh.1
    have tc : t ≠ c := of_decide_eq_true h2.1
    have aa : a ≠ r.2 := of_decide_eq_true h2.2
    apply congrArg (State.mk s.phase)
    show writeBit (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t
        ((writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t ^^
          (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) a) =
      writeBit (writeBit s.basis t (s.basis t ^^ s.basis a)) r.2 ((writeBit s.basis t (s.basis t ^^ s.basis a)) r.2 ^^
        ((writeBit s.basis t (s.basis t ^^ s.basis a)) r.1 && (writeBit s.basis t (s.basis t ^^ s.basis a)) c))
    rw [wb_other _ t r.1 _ (fun e => t1 e.symm), wb_other _ t c _ (fun e => tc e.symm), wb_other _ r.2 a _ aa]
    exact xor_comm s.basis t r.2 _ _ _ _ rfl rfl
  | CCX a b t =>
    have hh := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp hh.2
    have h3 := Bool.and_eq_true_iff.mp h2.2
    have t1 : t ≠ r.1 := of_decide_eq_true hh.1
    have tc : t ≠ c := of_decide_eq_true h2.1
    have aa : a ≠ r.2 := of_decide_eq_true h3.1
    have ba : b ≠ r.2 := of_decide_eq_true h3.2
    apply congrArg (State.mk s.phase)
    show writeBit (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t
        ((writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t ^^
          ((writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) a &&
            (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) b)) =
      writeBit (writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))) r.2
        ((writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))) r.2 ^^
        ((writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))) r.1 &&
          (writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))) c))
    rw [wb_other _ t r.1 _ (fun e => t1 e.symm), wb_other _ t c _ (fun e => tc e.symm), wb_other _ r.2 a _ aa,
      wb_other _ r.2 b _ ba]
    exact xor_comm s.basis t r.2 _ _ _ _ rfl rfl
  | measureX t c0 c1 =>
    have hh := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp hh.2
    have h3 := Bool.and_eq_true_iff.mp h2.2
    have h4 := Bool.and_eq_true_iff.mp h3.2
    have t1 : t ≠ r.1 := of_decide_eq_true hh.1
    have tc : t ≠ c := of_decide_eq_true h2.1
    have ta : t ≠ r.2 := of_decide_eq_true h3.1
    have free : corrFree r.2 (if m.headD false then c1 else c0) = true := by
      cases m.headD false
      · exact h4.1
      · exact h4.2
    show ECDSAAdd.correct (if m.headD false then c1 else c0)
        ⟨(clr c r s).phase ^^ (m.headD false && (clr c r s).basis t), writeBit (clr c r s).basis t false⟩ =
      clr c r (ECDSAAdd.correct (if m.headD false then c1 else c0)
        ⟨s.phase ^^ (m.headD false && s.basis t), writeBit s.basis t false⟩)
    rw [← corr_comm c r _ free, clr_frame c r s t ta]
    apply congrArg (ECDSAAdd.correct _)
    apply congrArg (State.mk _)
    show writeBit (writeBit s.basis r.2 (s.basis r.2 ^^ (s.basis r.1 && s.basis c))) t false =
      writeBit (writeBit s.basis t false) r.2 ((writeBit s.basis t false) r.2 ^^
        ((writeBit s.basis t false) r.1 && (writeBit s.basis t false) c))
    rw [wb_other _ t r.2 _ (fun e => ta e.symm), wb_other _ t r.1 _ (fun e => t1 e.symm),
      wb_other _ t c _ (fun e => tc e.symm)]
    funext q
    by_cases e : q = t
    · rw [e, wb_same, wb_other _ r.2 t _ ta, wb_same]
    · by_cases f : q = r.2
      · rw [wb_other _ t q _ e, f, wb_same, wb_same]
      · rw [wb_other _ t q _ e, wb_other _ r.2 q _ f, wb_other _ r.2 q _ f, wb_other _ t q _ e]

theorem comm (c : Wire) (r : Row) (P : Program) (h : P.all (quiet c r) = true) (m : List Bool) (s : State) :
    run P m (clr c r s) = clr c r (run P m s) := by
  induction P generalizing m s with
  | nil => rfl
  | cons g P ih =>
    have hh := Bool.and_eq_true_iff.mp (show (quiet c r g && P.all (quiet c r)) = true from h)
    have e (x : State) : run (g :: P) m x =
        run P (m.drop (measurementCount [g])) (run [g] (m.take (measurementCount [g])) x) := run_append [g] P m x
    rw [e, e, step_comm c r g hh.1, ih hh.2]
theorem commAll (c : Wire) (rs : List Row) (P : Program) (h : rs.all (fun r => P.all (quiet c r)) = true)
    (m : List Bool) (s : State) : run P m (clrAll c rs s) = clrAll c rs (run P m s) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hh := Bool.and_eq_true_iff.mp (show (P.all (quiet c r) && rs.all (fun r => P.all (quiet c r))) = true from h)
    show run P m (clrAll c rs (clr c r s)) = clrAll c rs (clr c r (run P m s))
    rw [ih hh.2, comm c r P hh.1]

/-- The woven digit pass is the kept gates after all clears. -/
theorem weave_run (c : Wire) (rs : List Row) (ks : Program) (h : woven c rs ks = true) (m : List Bool) (s : State) :
    run (weave c rs ks) m s = run ks m (clrAll c rs s) := by
  induction rs generalizing ks m s with
  | nil =>
    cases ks with
    | nil => rfl
    | cons k ks => exact absurd h (by simp [woven])
  | cons r rs ih =>
    cases ks with
    | nil => exact absurd h (by simp [woven])
    | cons k ks =>
      have hh := Bool.and_eq_true_iff.mp (show (rs.all (fun x => [k].all (quiet c x)) && woven c rs ks) = true from h)
      have e (P : Program) (x : State) : run (k :: P) m x =
          run P (m.drop (measurementCount [k])) (run [k] (m.take (measurementCount [k])) x) := run_append [k] P m x
      show run (k :: weave c rs ks) m (clr c r s) = run (k :: ks) m (clrAll c rs (clr c r s))
      rw [e, e, ih ks hh.2, commAll c rs [k] hh.1]

theorem apart_sep (c : Wire) (rs : List Row) (geo : apart c rs = true) :
    ∀ r ∈ rs, r.1 ≠ c ∧ r.2 ≠ c ∧ r.1 ≠ r.2 := by
  intro r hr
  have a := Bool.and_eq_true_iff.mp (List.all_eq_true.mp geo r hr)
  have b := Bool.and_eq_true_iff.mp a.2
  have d := Bool.and_eq_true_iff.mp b.2
  exact ⟨of_decide_eq_true a.1, of_decide_eq_true b.1, of_decide_eq_true d.1⟩
theorem apart_cross (c : Wire) (rs : List Row) (geo : apart c rs = true) :
    ∀ r ∈ rs, ∀ r' ∈ rs, r'.1 ≠ r.2 := by
  intro r hr r' hr'
  have a := Bool.and_eq_true_iff.mp (List.all_eq_true.mp geo r hr)
  have b := Bool.and_eq_true_iff.mp a.2
  have d := Bool.and_eq_true_iff.mp b.2
  exact of_decide_eq_true (List.all_eq_true.mp d.2 r' hr')
/-- `move` with the wire geometry as one decidable check. -/
theorem moved (c : Wire) (rs : List Row) (m : List Bool) (s : State) (a0 : Wire)
    (geo : apart c rs = true) (nd : lone rs = true) (clean : s.basis c = false)
    (sel : ∀ r ∈ rs, s.basis r.1 = true → r.2 = a0) :
    run (rows c rs) m s = clrAll c rs (run (mux c rs) m s) :=
  move c rs m s a0 (apart_sep c rs geo) (apart_cross c rs geo) nd clean sel

/-- Bridge: the spliced program (rows at the mux, kept gates at the digit pass) runs exactly like the reference
(mux ... woven digit pass) from every state where `c` is clean and the hot tags select one cell before the mux. -/
theorem splice (c : Wire) (rs : List Row) (A B C ks : Program) (s : State) (m : List Bool) (a0 : Wire)
    (geo : apart c rs = true) (nd : lone rs = true)
    (still : rs.all (fun r => B.all (quiet c r)) = true) (wv : woven c rs ks = true)
    (clean : (run A m s).basis c = false)
    (sel : ∀ r ∈ rs, (run A m s).basis r.1 = true → r.2 = a0) :
    run (A ++ (rows c rs ++ (B ++ (ks ++ C)))) m s = run (A ++ (mux c rs ++ (B ++ (weave c rs ks ++ C)))) m s := by
  simp only [run_append, run_take, rows_count, mux_count, weave_count c rs ks wv, List.drop_zero]
  rw [moved c rs _ (run A m s) a0 geo nd clean sel, commAll c rs B still, weave_run c rs ks wv]
  rw [run_take]

end ECDSAAdd.Entrant.StairPacket.MoveChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror

/-- Gate form of `MoveChain.rows`. -/
def rowGates (c : Wire) : List MoveChain.Row → List Gate
  | [] => []
  | r :: rs => .cx r.2 c :: .ccx r.1 c r.2 :: .cx r.2 c :: rowGates c rs
def gateOf : Instr → Gate
  | .X t => .x t
  | .CX a t => .cx a t
  | .CCX a b t => .ccx a b t
  | .measureX t _ _ => .x t
/-- Gates that need no clean target. -/
def plainGate : Gate → Bool
  | .make _ _ _ => false
  | _ => true
/-- A gate whose step commutes with the clear of row `r` and whose freshness test does not read the cell. -/
def calmGate (c : Wire) (r : MoveChain.Row) (g : Gate) : Bool :=
  MoveChain.quiet c r (front g) && (plainGate g || decide (target g ≠ r.2))

theorem rowGates_forward (c : Wire) (rs : List MoveChain.Row) : forward (rowGates c rs) = MoveChain.rows c rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact congrArg (fun p => Instr.CX r.2 c :: Instr.CCX r.1 c r.2 :: Instr.CX r.2 c :: p) ih
theorem ready_plain (gs : List Gate) (h : gs.all plainGate = true) (s : State) : Ready s gs := by
  induction gs generalizing s with
  | nil => trivial
  | cons g gs ih =>
    have hh := Bool.and_eq_true_iff.mp (show (plainGate g && gs.all plainGate) = true from h)
    refine ⟨?_, ih hh.2 _⟩
    cases g with
    | make a b t => exact absurd hh.1 (by simp [plainGate])
    | x t => trivial
    | cx a t => trivial
    | ccx a b t => trivial
    | pop a b t => trivial
theorem rowGates_plain (c : Wire) (rs : List MoveChain.Row) : (rowGates c rs).all plainGate = true := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact ih
theorem ready_split (as bs : List Gate) (s : State) (h : Ready s (as ++ bs)) :
    Ready s as ∧ Ready (run (forward as) [] s) bs := by
  induction as generalizing s with
  | nil => exact ⟨trivial, h⟩
  | cons g gs ih =>
    have h' : Fresh s g ∧ Ready (transition g s) (gs ++ bs) := h
    obtain ⟨a, b⟩ := ih (transition g s) h'.2
    refine ⟨⟨h'.1, a⟩, ?_⟩
    show Ready (run ([front g] ++ forward gs) [] s) bs
    rw [run_append, run_take, List.drop_nil]
    exact b
theorem ready_clr (c : Wire) (r : MoveChain.Row) (gs : List Gate) (h : gs.all (calmGate c r) = true)
    (s : State) (rd : Ready s gs) : Ready (MoveChain.clr c r s) gs := by
  induction gs generalizing s with
  | nil => trivial
  | cons g gs ih =>
    have hh := Bool.and_eq_true_iff.mp (show (calmGate c r g && gs.all (calmGate c r)) = true from h)
    have hg := Bool.and_eq_true_iff.mp (show (MoveChain.quiet c r (front g) && (plainGate g || decide (target g ≠ r.2))) = true from hh.1)
    have rd' : Fresh s g ∧ Ready (transition g s) gs := rd
    have step : transition g (MoveChain.clr c r s) = MoveChain.clr c r (transition g s) :=
      MoveChain.step_comm c r (front g) hg.1 [] s
    refine ⟨?_, ?_⟩
    · cases g with
      | make a b t =>
        have ne : t ≠ r.2 := of_decide_eq_true (show decide (t ≠ r.2) = true from hg.2)
        exact (MoveChain.clr_frame c r s t ne).trans rd'.1
      | x t => trivial
      | cx a t => trivial
      | ccx a b t => trivial
      | pop a b t => trivial
    · rw [step]
      exact ih hh.2 _ rd'.2
theorem ready_clrAll (c : Wire) (rs : List MoveChain.Row) (gs : List Gate)
    (h : rs.all (fun r => gs.all (calmGate c r)) = true) (s : State) (rd : Ready s gs) :
    Ready (MoveChain.clrAll c rs s) gs := by
  induction rs generalizing s with
  | nil => exact rd
  | cons r rs ih =>
    have hh := Bool.and_eq_true_iff.mp (show (gs.all (calmGate c r) && rs.all (fun r => gs.all (calmGate c r))) = true from h)
    exact ih hh.2 _ (ready_clr c r gs hh.1 s rd)

/-- Freshness of every `make` carries over from the reference gate list to the spliced one. -/
theorem ready_move (c : Wire) (rs : List MoveChain.Row) (A B C muxG digG keptG : List Gate) (s : State) (a0 : Wire)
    (hmux : forward muxG = MoveChain.mux c rs)
    (hdig : forward digG = MoveChain.weave c rs (forward keptG))
    (hk : keptG.all plainGate = true)
    (geo : MoveChain.apart c rs = true) (nd : MoveChain.lone rs = true)
    (still : rs.all (fun r => (forward B).all (MoveChain.quiet c r)) = true)
    (calmB : rs.all (fun r => B.all (calmGate c r)) = true)
    (wv : MoveChain.woven c rs (forward keptG) = true)
    (clean : (run (forward A) [] s).basis c = false)
    (sel : ∀ r ∈ rs, (run (forward A) [] s).basis r.1 = true → r.2 = a0)
    (rd : Ready s (A ++ (muxG ++ (B ++ (digG ++ C))))) :
    Ready s (A ++ (rowGates c rs ++ (B ++ (keptG ++ C)))) := by
  obtain ⟨rA, r1⟩ := ready_split _ _ _ rd
  obtain ⟨_, r2⟩ := ready_split _ _ _ r1
  rw [hmux] at r2
  obtain ⟨rB, r3⟩ := ready_split _ _ _ r2
  obtain ⟨_, rC⟩ := ready_split _ _ _ r3
  rw [hdig, MoveChain.weave_run c rs (forward keptG) wv, ← MoveChain.commAll c rs (forward B) still] at rC
  refine ready_append _ _ _ rA (ready_append _ _ _ (ready_plain _ (rowGates_plain c rs) _) ?_)
  rw [rowGates_forward, MoveChain.moved c rs [] _ a0 geo nd clean sel]
  exact ready_append _ _ _ (ready_clrAll c rs B calmB _ rB) (ready_append _ _ _ (ready_plain _ hk _) rC)

end ECDSAAdd.Entrant.StairPacket.GateMirror

end

-- ==== w4: par-b Partial section (c66d73e, HBJ appendix lines 40..1530) ====

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Parametric window programs (Job B of PARAMETRIC.md). Block `j : Fin 23` starts at tick
`s = start j = 75+15j`; its leave, enter, portal, park and archive pieces are functions of `s`.
Each leave/enter/portal/park is a `List GateMirror.Gate`: the forward program is `forward ops`
and the inverse is `inverse ops`, so the literal `*Inv` programs are mirrors by construction.
Wires: physical, except the history cells, which sit in the `OB5.sig (s+14)` frame (leave and
enter) or the `OB5.sig t` frame (archive at tick t). -/

/-- Route-rail width `R(s)` (= `W.narrowSkywalkRouteWidth s` for `s ≤ 510`). -/
def railP (s : Nat) : Nat := if s < 225 then 258 else if s < 257 then 257 else 513-s
/-- Small register bits `sb = (513-s)/2` (= `smallBits j` at `s = start j`). -/
def sbP (s : Nat) : Nat := (513-s)/2
/-- Bank width at the portal, `Wp = R-sb-16`; the leave works on `W = Wp+15` wires. -/
def wpP (s : Nat) : Nat := railP s - sbP s - 16
/-- First wire of the anchored ten-wire scratch block (`carryTop+1 = 1556+mid+1`). -/
def e0P (s : Nat) : Nat := 1574 + sbP s
/-- Top wire of the B rail (`785+R`). -/
def bTopP (s : Nat) : Nat := 785 + railP s
/-- Number of low columns of the join: 11 or 10. -/
def lowsP (s : Nat) : Nat := 18 + sbP (s+15) - sbP s
/-- First join column on the A side, `s+sb+32`. -/
def a0P (s : Nat) : Nat := s + sbP s + 32
/-- First low column on the B side, `787+sb`. -/
def b0P (s : Nat) : Nat := 787 + sbP s

/-- The leave's bank (`bank3`): `e0..e0+2`, the top `Wp-3` B-rail wires, then `1598..1612`. -/
def bankW (s i : Nat) : Wire :=
  if i < 3 then e0P s + i else if i < wpP s then bTopP s + 1 + i - wpP s else 1598 + i - wpP s
/-- Carry pool of the bank AND chain: `1598..` skipping the anchored block `e0..e0+9`. -/
def poolW (s i : Nat) : Wire := if 1598 + i < e0P s then 1598 + i else 1608 + i
/-- Carry pool of the StoreMapped chain: `1558..` skipping `1598..1612`. -/
def storeW (i : Nat) : Wire := if 1558 + i < 1598 then 1558 + i else 1573 + i

/-! Gate-level copies of dadon's gadgets (same recursion, so `forward` of each is the gadget). -/

/-- `signComplement q xs`. -/
def cxsG (q : Wire) (xs : List Wire) : List Gate := xs.map (fun x => .cx q x)
def xsG (xs : List Wire) : List Gate := xs.map .x
/-- `HighBankUnit.add ys carry cin` (= `mappedAdd (zeros ..)`): carries are made and popped. -/
def addG : List Wire → List Wire → Wire → List Gate
  | y::y'::ys, c::cs, cin => .make y cin c :: (addG (y'::ys) cs c ++ [.pop y cin c, .cx cin y])
  | [y], _, cin => [.cx cin y]
  | _, _, _ => []
/-- `HighBankAdjust.adjust ys cs cin neg`. -/
def adjustG (ys cs : List Wire) (cin neg : Wire) : List Gate :=
  cxsG neg ys ++ (addG ys cs cin ++ cxsG neg ys)
/-- `cswap c a b`. -/
def cswapG (c a b : Wire) : List Gate := [.cx b a, .ccx c a b, .cx b a]
/-- `HighBankShift.program c w d n`. -/
def shiftG (c : Wire) (w : Nat → Wire) (d : Nat) : Nat → List Gate
  | 0 => []
  | n+1 => cswapG c (w (n+d)) (w n) ++ shiftG c w d n
/-- `HighBankControl.toggles c xs`. -/
def togglesG (c : Wire) (xs : List Wire) : List Gate := xs.map (fun q => .cx q c)
/-- `HighBankBarrel.stage c w xs d n`. -/
def stageG (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) : List Gate :=
  togglesG c xs ++ (shiftG c w d n ++ togglesG c xs)
/-- `HighBankJoin.clearDigit`. -/
def clearG (hot cross d1 lo hi : Wire) : List Gate := [.ccx hot cross lo, .ccx hot d1 hi]
/-- `HighBankJoin.digits hot bank c d start n`. -/
def digitsG (hot bank : Nat → Wire) (c d start : Nat) : Nat → List Gate
  | 0 => []
  | n+1 => clearG (hot start) c d (bank start) (bank (start+1)) ++ digitsG hot bank c d (start+1) n
/-- `HighBankJoin.pair`. -/
def pairG (low : Bool) (a s t : Wire) : List Gate :=
  if low then [.cx t s, .ccx a s t] else [.cx s t, .cx t s, .ccx a t s]
/-- `HighBankJoin.toggle`. -/
def toggleG (a : Wire) : Option Wire → List Gate
  | none => []
  | some w => [.cx w a]
/-- `HighBankJoin.word a rows`. -/
def wordG (a : Wire) : List HighBankJoin.Column → List Gate
  | [] => []
  | r::rs => toggleG a r.hot ++ (pairG r.low a r.shadow r.tube ++ (wordG a rs ++ toggleG a r.hot))
/-- AND chain `c i ∧ seq i → c (i+1)` for `n` steps around `body`, popped in reverse. -/
def chainG (c seq : Nat → Wire) (body : List Gate) (i : Nat) : Nat → List Gate
  | 0 => body
  | n+1 => .make (c i) (seq i) (c (i+1)) :: (chainG c seq body (i+1) n ++ [.pop (c i) (seq i) (c (i+1))])
/-- Event chain of the close: each event bit gates the next flag, then the output is toggled. -/
def eventsG (a out : Wire) : List (Wire × Wire) → List Gate
  | [] => [.cx a out]
  | (x,t)::ps => [.x x, .make a x t] ++ (eventsG t out ps ++ [.pop a x t, .x x])
def swapG (p : Wire × Wire) : List Gate := [.cx p.1 p.2, .cx p.2 p.1, .cx p.1 p.2]
def swapsG (ps : List (Wire × Wire)) : List Gate := ps.flatMap swapG

/-! Leave: 17 segments (cut points `cutsP`). -/

def tagsP : List Wire := [1576, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]
def controlsP0 : List Wire := [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560]
def controlsP1 : List Wire := [1563, 1564, 1567, 1568, 1571, 1572, 1575, 1560]
def controlsP2 : List Wire := [1565, 1566, 1567, 1568, 1573, 1574, 1575, 1560]
def controlsP3 : List Wire := [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]

/-- Segment 6: bank-wide adjust (fan-out 1597, AND chain into the pool, fan-in). -/
def leaveAdjust (s : Nat) : List Gate :=
  adjustG ((List.range (wpP s)).map (bankW s)) ((List.range (wpP s - 1)).map (poolW s)) (e0P s + 6) 1597
/-- Segment 7: the four barrel stages (shift by 1, 2, 4, 8). -/
def leaveBarrel (s : Nat) : List Gate :=
  stageG 1613 (bankW s) controlsP0 1 (wpP s) ++ stageG 1613 (bankW s) controlsP1 2 (wpP s + 1) ++
  stageG 1613 (bankW s) controlsP2 4 (wpP s + 3) ++ stageG 1613 (bankW s) controlsP3 8 (wpP s + 7)
/-- The 18 join columns (`Leave{s}Join.columns`). -/
def columnsP (s : Nat) : List HighBankJoin.Column :=
  (List.range 18).map fun i =>
    ⟨decide (i < lowsP s), if i < 16 then some (tagsP.getD i 0) else none, a0P s + i, bankW s i⟩
/-- Segment 9: `digitPass ++ wordPass`. -/
def leaveJoin (s : Nat) : List Gate :=
  digitsG (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16 ++ wordG 1614 (columnsP s)
/-- Segment 13: low-limb store (sign close, low adds, borrow chain). -/
def leaveLowStore (s : Nat) : List Gate :=
  let L := lowsP s; let bs := (List.range L).map (b0P s + ·)
  [.cx (e0P s + 3) 1560, .cx 1559 1560, .pop (e0P s + 3) (e0P s + 4) 1559] ++
  (List.range L).map (fun i => .ccx 1556 (a0P s + i) (b0P s + i)) ++ xsG bs ++
  addG bs ((List.range (L-1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (b0P s - 1) 1557 1558, .cx (a0P s - 1) 1557, .x 1557]
/-- Segment 14: StoreMapped (top-of-word AND chain, then the B-side chain). -/
def leaveStoreMapped (s : Nat) : List Gate :=
  let L := lowsP s; let top := a0P s + L - 1; let H := wpP s + 15 - L
  let hi := (List.range H).map (fun i => bankW s (L+i))
  let seq := fun i => if i = 0 then top else bankW s (L+i-1)
  let seq2 := (List.range (L+1)).map (b0P s - 1 + ·)
  [.make (top-2) (top-1) 1558, .x 1558, .x top] ++ xsG hi ++
  chainG storeW seq [.cx (storeW (H+1)) 1557, .x 1557] 0 (H+1) ++
  xsG hi.reverse ++ [.x top, .x 1558, .pop (top-2) (top-1) 1558, .make 1556 1557 1558, .x 1558] ++
  xsG seq2 ++ chainG (1558 + ·) (b0P s - 1 + ·) [.cx (1558+(L+1)) 1556, .x 1556] 0 (L+1) ++
  xsG seq2.reverse ++ [.x 1558]
/-- Segment 15: history flip and the low-column hand-back. -/
def leaveLowClose (s : Nat) : List Gate :=
  let L := lowsP s
  xsG ((List.range 15).map (s+16+·)) ++
  (List.range (L+1)).map (fun i => .cx (e0P s + 5) (b0P s - 1 + i)) ++
  (List.range (L+1)).flatMap (fun i => cswapG (s+30) (b0P s - 1 + i) (a0P s - 1 + i))
/-- Relocation moves into the next tick's layout (`Leave{s}Relocated.moves`). -/
def movesP (s : Nat) : List (Wire × Wire) :=
  (List.range (wpP (s+15) - 3)).map (fun i => (bankW s (lowsP s + i), bTopP (s+15) + 4 + i - wpP (s+15))) ++
  [(1557, e0P (s+15) + 3), (1558, e0P (s+15) + 4), (e0P s + 5, e0P (s+15) + 5),
   (e0P s + 3, e0P (s+15) + 6), (e0P s + 7, e0P (s+15) + 7), (e0P s + 6, e0P (s+15) + 8)]
/-- Segment 16: event chain into the flag, then the relocation moves. -/
def leaveClose (s : Nat) : List Gate :=
  eventsG (e0P s + 7) (e0P s + 4)
    [(OB5.sig (s+14) (s+1044), 1556), (OB5.sig (s+14) (s+1045), 1559), (OB5.sig (s+14) (s+1046), 1560),
     (OB5.sig (s+14) (s+1047), 1561), (OB5.sig (s+14) (s+1048), 1562)] ++
  swapsG (movesP s)

-- generated by helpers/par-b/scripts/gen.py: fixed leave segments in (s, h = sb s), history wires in the OB5.sig (s+14) frame

def leaveFix0 (s h : Nat) : List Gate := [
  .cx (s+h+49) (h+1579),
  .cx (h+804) (h+1579),
  .cx (s+h+31) (h+786),
  .ccx (s+30) (h+786) (s+h+31),
  .cx (s+h+31) (h+786),
  .cx (s+h+32) (h+787),
  .ccx (s+30) (h+787) (s+h+32),
  .cx (s+h+32) (h+787),
  .cx (s+h+33) (h+788),
  .ccx (s+30) (h+788) (s+h+33),
  .cx (s+h+33) (h+788),
  .cx (s+h+34) (h+789),
  .ccx (s+30) (h+789) (s+h+34),
  .cx (s+h+34) (h+789),
  .cx (s+h+35) (h+790),
  .ccx (s+30) (h+790) (s+h+35),
  .cx (s+h+35) (h+790),
  .cx (s+h+36) (h+791),
  .ccx (s+30) (h+791) (s+h+36),
  .cx (s+h+36) (h+791),
  .cx (s+h+37) (h+792),
  .ccx (s+30) (h+792) (s+h+37),
  .cx (s+h+37) (h+792),
  .cx (s+h+38) (h+793),
  .ccx (s+30) (h+793) (s+h+38),
  .cx (s+h+38) (h+793),
  .cx (s+h+39) (h+794),
  .ccx (s+30) (h+794) (s+h+39),
  .cx (s+h+39) (h+794),
  .cx (s+h+40) (h+795),
  .ccx (s+30) (h+795) (s+h+40),
  .cx (s+h+40) (h+795),
  .cx (s+h+41) (h+796),
  .ccx (s+30) (h+796) (s+h+41),
  .cx (s+h+41) (h+796),
  .cx (s+h+42) (h+797),
  .ccx (s+30) (h+797) (s+h+42),
  .cx (s+h+42) (h+797),
  .cx (s+h+43) (h+798),
  .ccx (s+30) (h+798) (s+h+43),
  .cx (s+h+43) (h+798),
  .cx (s+h+44) (h+799),
  .ccx (s+30) (h+799) (s+h+44),
  .cx (s+h+44) (h+799),
  .cx (s+h+45) (h+800),
  .ccx (s+30) (h+800) (s+h+45),
  .cx (s+h+45) (h+800),
  .cx (s+h+46) (h+801),
  .ccx (s+30) (h+801) (s+h+46),
  .cx (s+h+46) (h+801),
  .cx (s+h+47) (h+802),
  .ccx (s+30) (h+802) (s+h+47),
  .cx (s+h+47) (h+802),
  .cx (s+h+48) (h+803),
  .ccx (s+30) (h+803) (s+h+48),
  .cx (s+h+48) (h+803),
  .cx (s+h+49) (h+804),
  .ccx (s+30) (h+804) (s+h+49),
  .cx (s+h+49) (h+804),
  .cx (h+1579) (h+786),
  .cx (h+1579) (h+787),
  .cx (h+1579) (h+788),
  .cx (h+1579) (h+789),
  .cx (h+1579) (h+790),
  .cx (h+1579) (h+791),
  .cx (h+1579) (h+792),
  .cx (h+1579) (h+793),
  .cx (h+1579) (h+794),
  .cx (h+1579) (h+795),
  .cx (h+1579) (h+796),
  .cx (h+1579) (h+797),
  .cx (h+1579) (h+798),
  .cx (h+1579) (h+799),
  .cx (h+1579) (h+800),
  .cx (h+1579) (h+801),
  .cx (h+1579) (h+802),
  .cx (h+1579) (h+803),
  .cx (h+1579) (h+804)]

def leaveFix1 (s h : Nat) : List Gate := [
  .x (s+16),
  .x (s+17),
  .x (s+18),
  .x (s+19),
  .x (s+20),
  .x (s+21),
  .x (s+22),
  .x (s+23),
  .x (s+24),
  .x (s+25),
  .x (s+26),
  .x (s+27),
  .x (s+28),
  .x (s+29),
  .x (s+30)]

def leaveFix2 (s h : Nat) : List Gate := [
  .x (h+786),
  .x (h+787),
  .x (h+788),
  .x (h+789),
  .x (h+790),
  .x (h+791),
  .x (h+792),
  .x (h+793),
  .x (h+794),
  .x (h+795),
  .x (h+796),
  .x (h+797),
  .x (h+798),
  .x (h+799),
  .x (h+800),
  .x (h+801),
  .x (h+802),
  .x (h+803),
  .x (h+804),
  .make (h+786) (h+787) 1557,
  .make 1557 (h+788) 1558,
  .make 1558 (h+789) 1559,
  .make 1559 (h+790) 1560,
  .make 1560 (h+791) 1561,
  .make 1561 (h+792) 1562,
  .make 1562 (h+793) 1563,
  .make 1563 (h+794) 1564,
  .make 1564 (h+795) 1565,
  .make 1565 (h+796) 1566,
  .make 1566 (h+797) 1567,
  .make 1567 (h+798) 1568,
  .make 1568 (h+799) 1569,
  .make 1569 (h+800) 1570,
  .make 1570 (h+801) 1571,
  .make 1571 (h+802) 1572,
  .make 1572 (h+803) 1573,
  .make 1573 (h+804) 1574,
  .cx 1574 1556,
  .x 1556,
  .pop 1573 (h+804) 1574,
  .pop 1572 (h+803) 1573,
  .pop 1571 (h+802) 1572,
  .pop 1570 (h+801) 1571,
  .pop 1569 (h+800) 1570,
  .pop 1568 (h+799) 1569,
  .pop 1567 (h+798) 1568,
  .pop 1566 (h+797) 1567,
  .pop 1565 (h+796) 1566,
  .pop 1564 (h+795) 1565,
  .pop 1563 (h+794) 1564,
  .pop 1562 (h+793) 1563,
  .pop 1561 (h+792) 1562,
  .pop 1560 (h+791) 1561,
  .pop 1559 (h+790) 1560,
  .pop 1558 (h+789) 1559,
  .pop 1557 (h+788) 1558,
  .pop (h+786) (h+787) 1557,
  .x (h+804),
  .x (h+803),
  .x (h+802),
  .x (h+801),
  .x (h+800),
  .x (h+799),
  .x (h+798),
  .x (h+797),
  .x (h+796),
  .x (h+795),
  .x (h+794),
  .x (h+793),
  .x (h+792),
  .x (h+791),
  .x (h+790),
  .x (h+789),
  .x (h+788),
  .x (h+787),
  .x (h+786),
  .x 1557,
  .cx (s+h+31) 1557,
  .make (h+786) 1557 1558,
  .make (h+787) 1558 1559,
  .make (h+788) 1559 1560,
  .make (h+789) 1560 1561,
  .make (h+790) 1561 1562,
  .make (h+791) 1562 1563,
  .make (h+792) 1563 1564,
  .make (h+793) 1564 1565,
  .make (h+794) 1565 1566,
  .make (h+795) 1566 1567,
  .make (h+796) 1567 1568,
  .make (h+797) 1568 1569,
  .make (h+798) 1569 1570,
  .make (h+799) 1570 1571,
  .make (h+800) 1571 1572,
  .make (h+801) 1572 1573,
  .make (h+802) 1573 1574,
  .make (h+803) 1574 1575,
  .cx 1575 (h+804),
  .pop (h+803) 1574 1575,
  .cx 1574 (h+803),
  .pop (h+802) 1573 1574,
  .cx 1573 (h+802),
  .pop (h+801) 1572 1573,
  .cx 1572 (h+801),
  .pop (h+800) 1571 1572,
  .cx 1571 (h+800),
  .pop (h+799) 1570 1571,
  .cx 1570 (h+799),
  .pop (h+798) 1569 1570,
  .cx 1569 (h+798),
  .pop (h+797) 1568 1569,
  .cx 1568 (h+797),
  .pop (h+796) 1567 1568,
  .cx 1567 (h+796),
  .pop (h+795) 1566 1567,
  .cx 1566 (h+795),
  .pop (h+794) 1565 1566,
  .cx 1565 (h+794),
  .pop (h+793) 1564 1565,
  .cx 1564 (h+793),
  .pop (h+792) 1563 1564,
  .cx 1563 (h+792),
  .pop (h+791) 1562 1563,
  .cx 1562 (h+791),
  .pop (h+790) 1561 1562,
  .cx 1561 (h+790),
  .pop (h+789) 1560 1561,
  .cx 1560 (h+789),
  .pop (h+788) 1559 1560,
  .cx 1559 (h+788),
  .pop (h+787) 1558 1559,
  .cx 1558 (h+787),
  .ccx 1556 (s+h+32) (h+787),
  .ccx 1556 (s+h+33) (h+788),
  .ccx 1556 (s+h+34) (h+789),
  .ccx 1556 (s+h+35) (h+790),
  .ccx 1556 (s+h+36) (h+791),
  .ccx 1556 (s+h+37) (h+792),
  .ccx 1556 (s+h+38) (h+793),
  .ccx 1556 (s+h+39) (h+794),
  .ccx 1556 (s+h+40) (h+795),
  .ccx 1556 (s+h+41) (h+796),
  .ccx 1556 (s+h+42) (h+797),
  .ccx 1556 (s+h+43) (h+798),
  .ccx 1556 (s+h+44) (h+799),
  .ccx 1556 (s+h+45) (h+800),
  .ccx 1556 (s+h+46) (h+801),
  .ccx 1556 (s+h+47) (h+802),
  .ccx 1556 (s+h+48) (h+803),
  .ccx 1556 (s+h+49) (h+804)]

def leaveFix3 (s h : Nat) : List Gate := [
  .make (h+1577) (h+1578) 1559,
  .cx (h+1577) 1560,
  .cx 1559 1560]

def leaveFix4 (s h : Nat) : List Gate := [
  .make 1560 (OB5.sig (s+14) (s+1044)) 1561,
  .cx 1561 1560,
  .make 1560 (OB5.sig (s+14) (s+1045)) 1562,
  .cx 1562 1560,
  .make 1560 (OB5.sig (s+14) (s+1046)) 1563,
  .cx 1563 1560,
  .make 1560 (OB5.sig (s+14) (s+1047)) 1564,
  .cx 1564 1560,
  .make 1560 (OB5.sig (s+14) (s+1048)) 1565,
  .cx 1565 1560,
  .make 1560 (OB5.sig (s+14) (s+1049)) 1566,
  .cx 1566 1560,
  .make 1560 (OB5.sig (s+14) (s+1050)) 1567,
  .cx 1567 1560,
  .make 1560 (OB5.sig (s+14) (s+1051)) 1568,
  .cx 1568 1560,
  .make 1560 (OB5.sig (s+14) (s+1052)) 1569,
  .cx 1569 1560,
  .make 1560 (OB5.sig (s+14) (s+1053)) 1570,
  .cx 1570 1560,
  .make 1560 (OB5.sig (s+14) (s+1054)) 1571,
  .cx 1571 1560,
  .make 1560 (OB5.sig (s+14) (s+1055)) 1572,
  .cx 1572 1560,
  .make 1560 (OB5.sig (s+14) (s+1056)) 1573,
  .cx 1573 1560,
  .make 1560 (OB5.sig (s+14) (s+1057)) 1574,
  .cx 1574 1560,
  .make 1560 (OB5.sig (s+14) (s+1058)) 1575,
  .cx 1575 1560]

def leaveFix5 (s h : Nat) : List Gate := [
  .cx 1559 (h+1581),
  .cx 1561 (h+1581),
  .cx 1562 (h+1581),
  .cx 1563 (h+1581),
  .cx 1564 (h+1581),
  .cx 1565 (h+1581),
  .cx 1559 1576,
  .cx 1561 1576,
  .make (s+29) (s+30) 1577,
  .make (s+28) 1577 1578,
  .make (s+27) 1578 1579,
  .make (s+26) 1579 1580,
  .make (s+25) 1580 1581,
  .make (s+24) 1581 1582,
  .make (s+23) 1582 1583,
  .make (s+22) 1583 1584,
  .make (s+21) 1584 1585,
  .make (s+20) 1585 1586,
  .make (s+19) 1586 1587,
  .make (s+18) 1587 1588,
  .make 1562 1588 1589,
  .make 1563 1586 1590,
  .make 1564 1584 1591,
  .make 1565 1582 1592,
  .make 1566 1580 1593,
  .make 1567 1578 1594,
  .make 1568 (s+30) 1595,
  .ccx 1576 (s+h+32) (h+1580),
  .ccx 1562 (s+h+33) (h+1580),
  .ccx 1563 (s+h+34) (h+1580),
  .ccx 1564 (s+h+35) (h+1580),
  .ccx 1565 (s+h+36) (h+1580),
  .ccx 1566 (s+h+37) (h+1580),
  .ccx 1567 (s+h+38) (h+1580),
  .ccx 1568 (s+h+39) (h+1580),
  .ccx 1569 (s+h+40) (h+1580),
  .ccx 1570 (s+h+41) (h+1580),
  .ccx 1571 (s+h+42) (h+1580),
  .ccx 1572 (s+h+43) (h+1580),
  .ccx 1573 (s+h+44) (h+1580),
  .ccx 1574 (s+h+45) (h+1580),
  .ccx 1575 (s+h+46) (h+1580),
  .ccx 1560 (s+h+47) (h+1580),
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
  .make (h+1580) 1596 1597]

def leaveFix8 (s h : Nat) : List Gate := [
  .x 1613,
  .cx 1597 1613]

def leaveFix10 (s h : Nat) : List Gate := [
  .cx 1597 1613,
  .x 1613]

def leaveFix11 (s h : Nat) : List Gate := [
  .pop (h+1580) 1596 1597,
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
  .pop 1568 (s+30) 1595,
  .pop 1567 1578 1594,
  .pop 1566 1580 1593,
  .pop 1565 1582 1592,
  .pop 1564 1584 1591,
  .pop 1563 1586 1590,
  .pop 1562 1588 1589,
  .pop (s+18) 1587 1588,
  .pop (s+19) 1586 1587,
  .pop (s+20) 1585 1586,
  .pop (s+21) 1584 1585,
  .pop (s+22) 1583 1584,
  .pop (s+23) 1582 1583,
  .pop (s+24) 1581 1582,
  .pop (s+25) 1580 1581,
  .pop (s+26) 1579 1580,
  .pop (s+27) 1578 1579,
  .pop (s+28) 1577 1578,
  .pop (s+29) (s+30) 1577,
  .cx 1559 1576,
  .cx 1561 1576]

def leaveFix12 (s h : Nat) : List Gate := [
  .cx 1575 1560,
  .pop 1560 (OB5.sig (s+14) (s+1058)) 1575,
  .cx 1574 1560,
  .pop 1560 (OB5.sig (s+14) (s+1057)) 1574,
  .cx 1573 1560,
  .pop 1560 (OB5.sig (s+14) (s+1056)) 1573,
  .cx 1572 1560,
  .pop 1560 (OB5.sig (s+14) (s+1055)) 1572,
  .cx 1571 1560,
  .pop 1560 (OB5.sig (s+14) (s+1054)) 1571,
  .cx 1570 1560,
  .pop 1560 (OB5.sig (s+14) (s+1053)) 1570,
  .cx 1569 1560,
  .pop 1560 (OB5.sig (s+14) (s+1052)) 1569,
  .cx 1568 1560,
  .pop 1560 (OB5.sig (s+14) (s+1051)) 1568,
  .cx 1567 1560,
  .pop 1560 (OB5.sig (s+14) (s+1050)) 1567,
  .cx 1566 1560,
  .pop 1560 (OB5.sig (s+14) (s+1049)) 1566,
  .cx 1565 1560,
  .pop 1560 (OB5.sig (s+14) (s+1048)) 1565,
  .cx 1564 1560,
  .pop 1560 (OB5.sig (s+14) (s+1047)) 1564,
  .cx 1563 1560,
  .pop 1560 (OB5.sig (s+14) (s+1046)) 1563,
  .cx 1562 1560,
  .pop 1560 (OB5.sig (s+14) (s+1045)) 1562,
  .cx 1561 1560,
  .pop 1560 (OB5.sig (s+14) (s+1044)) 1561]

def enterFix (s h : Nat) : List Gate := [
  .cx (s+h+31) (h+801),
  .make (s+15) (h+801) 1558,
  .cx 1558 (s+h+31),
  .cx (s+h+31) (h+801),
  .cx (s+h+32) (h+802),
  .ccx (s+15) (h+802) (s+h+32),
  .cx (s+h+32) (h+802),
  .cx (s+h+33) (h+803),
  .ccx (s+15) (h+803) (s+h+33),
  .cx (s+h+33) (h+803),
  .cx (s+h+34) (h+804),
  .ccx (s+15) (h+804) (s+h+34),
  .cx (s+h+34) (h+804),
  .cx (h+1579) (h+801),
  .cx (h+1579) (h+802),
  .cx (h+1579) (h+803),
  .cx (h+1579) (h+804),
  .x 1556,
  .cx (s+h+31) 1556,
  .make (h+801) 1556 1557,
  .make (h+802) 1557 1559,
  .make (h+803) 1559 1560,
  .cx 1560 (h+804),
  .pop (h+803) 1559 1560,
  .cx 1559 (h+803),
  .pop (h+802) 1557 1559,
  .cx 1557 (h+802),
  .cx (s+h+32) 1559,
  .ccx (h+1577) 1559 (s+h+32),
  .cx (s+h+32) 1559,
  .cx (s+h+33) 1560,
  .ccx (h+1577) 1560 (s+h+33),
  .cx (s+h+33) 1560,
  .cx (s+h+34) 1561,
  .ccx (h+1577) 1561 (s+h+34),
  .cx (s+h+34) 1561,
  .cx (h+1577) (s+h+33),
  .ccx (h+1578) 1559 (h+802),
  .cx (h+1577) 1560,
  .ccx (h+1578) 1560 (h+803),
  .cx (h+1577) 1560,
  .ccx (h+1578) 1561 (h+804),
  .x (h+802),
  .x (h+803),
  .x (h+804),
  .make (h+802) 1557 1562,
  .make (h+803) 1562 1563,
  .cx 1563 (h+804),
  .pop (h+803) 1562 1563,
  .cx 1562 (h+803),
  .pop (h+802) 1557 1562,
  .cx 1557 (h+802),
  .x (h+802),
  .x (h+803),
  .x (h+804),
  .pop (h+801) 1556 1557,
  .cx (s+h+31) 1556,
  .x 1556,
  .cx (h+1579) (h+801),
  .cx (h+1579) (h+802),
  .cx (h+1579) (h+803),
  .cx (h+1579) (h+804),
  .cx (s+h+31) (h+801),
  .cx 1558 (s+h+31),
  .pop (s+15) (h+801) 1558,
  .cx (s+h+31) (h+801),
  .cx (s+h+32) (h+802),
  .ccx (s+15) (h+802) (s+h+32),
  .cx (s+h+32) (h+802),
  .cx (s+h+33) (h+803),
  .ccx (s+15) (h+803) (s+h+33),
  .cx (s+h+33) (h+803),
  .cx (s+h+34) (h+804),
  .ccx (s+15) (h+804) (s+h+34),
  .cx (s+h+34) (h+804),
  .cx (s+h+34) (h+1579),
  .cx (h+804) (h+1579),
  .cx 1559 (h+1574),
  .cx (h+1574) 1559,
  .cx 1559 (h+1574),
  .cx 1560 (h+1575),
  .cx (h+1575) 1560,
  .cx 1560 (h+1575),
  .cx 1561 (h+1576),
  .cx (h+1576) 1561,
  .cx 1561 (h+1576)]

def moveLoadPairs (t : Nat) : List (Wire × Wire) := [
  ((OB5.sig t (t+1036)), (t+9)),
  ((OB5.sig t (t+1036)), (OB5.sig t (t+1037))),
  ((OB5.sig t (t+1036)), (t+10)),
  ((OB5.sig t (t+1036)), (t+11)),
  ((OB5.sig t (t+1038)), (OB5.sig t (t+1039))),
  ((OB5.sig t (t+1036)), (t+12)),
  ((OB5.sig t (t+1038)), (OB5.sig t (t+1040))),
  ((OB5.sig t (t+1036)), (t+13)),
  ((OB5.sig t (t+1038)), (t+14)),
  ((OB5.sig t (t+1036)), (OB5.sig t (t+1042))),
  ((OB5.sig t (t+1041)), (t+15))]

def moveRestorePairs (t f : Nat) : List (Wire × Wire) := [
  ((t+9), (OB5.sig t (t+1036))),
  ((OB5.sig t (t+1037)), (t+9)),
  ((t+10), (OB5.sig t (t+1037))),
  ((t+11), (t+10)),
  ((OB5.sig t (t+1039)), (OB5.sig t (t+1038))),
  ((t+12), (t+11)),
  ((OB5.sig t (t+1040)), (OB5.sig t (t+1039))),
  ((t+13), (t+12)),
  ((t+14), (OB5.sig t (t+1040))),
  ((OB5.sig t (t+1042)), (t+13)),
  ((t+15), (OB5.sig t (t+1041))),
  (1556, (t+14)),
  (1557, (OB5.sig t (t+1042))),
  (1558, (t+15)),
  (1559, (OB5.sig t (t+1043))),
  (1560, f),
  (1561, (f+1)),
  (1562, (f+2))]

/-- The leave of the block at tick `s`, as mirror ops. -/
def leaveOps (s : Nat) : List Gate :=
  leaveFix0 s (sbP s) ++ leaveFix1 s (sbP s) ++ leaveFix2 s (sbP s) ++ leaveFix3 s (sbP s) ++
  leaveFix4 s (sbP s) ++ leaveFix5 s (sbP s) ++ leaveAdjust s ++ leaveBarrel s ++
  leaveFix8 s (sbP s) ++ leaveJoin s ++ leaveFix10 s (sbP s) ++ leaveFix11 s (sbP s) ++
  leaveFix12 s (sbP s) ++ leaveLowStore s ++ leaveStoreMapped s ++ leaveLowClose s ++ leaveClose s

/-- The 35 cut points of the leave (offsets used by every `.drop`/`.take` of the per-block proofs;
an `Inv` offset is `length - cut`), and its length. -/
def cutsP (s : Nat) : List Nat :=
  let w := wpP s; let L := lowsP s; let H := w + 15 - L
  let p0 := 334 + (5*w - 2)
  let p1 := p0 + 16 + 3*w; let p2 := p1 + 16 + 3*(w+1); let p3 := p2 + 16 + 3*(w+3)
  let p4 := p3 + 16 + 3*(w+7)
  let j := p4 + 2; let r := j + (118 - L) + 2; let a := r + 67; let b := a + (6*L + 4)
  let t := b + (4*(w+15) + 19) + (4*L + 19)
  [0, 78, 93, 169, 172, 242, 245, 275, 334,
   p0, p0+8, p0+8+3*w, p1, p1+8, p1+8+3*(w+1), p2, p2+8, p2+8+3*(w+3), p3, p3+8, p3+8+3*(w+7), p4,
   j, j + (118 - L), r, r+37, r+67, a+3, a + (6*L+4) - 3, b, b + (4*H+10), b + (4*H+11), b + (4*(w+15)+19), t, t+21]
def cutP (s k : Nat) : Nat := (cutsP s).getD k 0
def leaveLength (s : Nat) : Nat := cutP s 33 + 21 + 3*(wpP (s+15) + 3)

/-! Portal (entry: `portalP s1`; exit: `portalInvP e` forward, `portalP e` reverse). -/

def exchangeG (c : Wire) (ps : List (Wire × Wire)) : List Gate :=
  ps.flatMap (fun p => [.cx p.1 p.2, .ccx c p.2 p.1, .cx p.1 p.2])
def transferG (ps : List (Wire × Wire)) : List Gate := ps.flatMap (fun p => [.cx p.1 p.2, .cx p.2 p.1])
def targetG : Option Wire → Wire → Wire → List Gate
  | none, a, out => [.cx a out, .x out]
  | some e, a, out => [.cx e out, .ccx e a out]
def latchChainG (e : Option Wire) (out : Wire) : Wire → List (Wire × Wire) → List Gate
  | a, [] => targetG e a out
  | a, (x,t)::ps => .make a x t :: (latchChainG e out t ps ++ [.pop a x t])
def latchG (rev : Bool) (e : Option Wire) (out a : Wire) (ps : List (Wire × Wire)) : List Gate :=
  let ds := a :: ps.map Prod.fst
  xsG ds ++ (latchChainG e out a ps ++ xsG (if rev then ds.reverse else ds))

def portalOps (t : Nat) : List Gate :=
  let w := wpP t; let aBot := a0P t; let bBot := 802 + sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-3)).map (aBot + 3 + ·); let bB := (List.range (w-3)).map (bBot + 3 + ·)
  let sgn := e0P t + 5; let G := t + 15; let f3 := e0P t + 3; let f4 := e0P t + 4
  [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] ++ exchangeG G (rA.zip rB) ++ cxsG sgn rB ++
  [.make aBot (aBot+1) 1557] ++ latchG true none 1556 1557 ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i))) ++
  [.pop aBot (aBot+1) 1557, .cx 1556 f3, .cx f3 1556] ++
  latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i))) ++
  [.x (aBot+2), .make (bBot+2) (aBot+2) 1556] ++ addG bB ((List.range (w-4)).map (1557 + ·)) 1556 ++
  (bA.zip bB).map (fun p => .ccx f4 p.1 p.2) ++ [.pop (bBot+2) (aBot+2) 1556, .x (aBot+2)] ++
  transferG (bA.zip bB) ++ cxsG sgn [bBot, bBot+1, bBot+2] ++
  exchangeG G [(aBot, bBot), (aBot+1, bBot+1), (aBot+2, bBot+2)]

/-- Park at the exit tick `e`: the last leave's flags `e0(e)+6..8` to the freed B-rail wires above `bTop(e)`. -/
def parkOps (e : Nat) : List Gate :=
  swapsG [(e0P e + 6, bTopP e + 1), (e0P e + 7, bTopP e + 2), (e0P e + 8, bTopP e + 3)]

def enterOps (s : Nat) : List Gate := enterFix s (sbP s)

/-! The window interface (PARAMETRIC.md, agreed with design-window and par-d). -/

def enterP (j : Fin 23) : Program := GateMirror.forward (enterOps (start j))
def enterInvP (j : Fin 23) : Program := inverse (enterOps (start j))
def leaveP (j : Fin 23) : Program := GateMirror.forward (leaveOps (start j))
def leaveInvP (j : Fin 23) : Program := inverse (leaveOps (start j))
def portalP (t : Nat) : Program := GateMirror.forward (portalOps t)
def portalInvP (t : Nat) : Program := inverse (portalOps t)
def parkP (e : Nat) : Program := GateMirror.forward (parkOps e)
def parkInvP (e : Nat) : Program := inverse (parkOps e)

/-! Archives. Cells of ticks `t-10..t-1` (raw `t'+16`, `t'+1044`, frame `OB5.sig t`); flags at `f..f+2`:
window form `f = e0(t)+6` (written by the previous leave), stock form at the exit `f = bTop(e)+1` (park);
codec scratch `scratchS t k` (both forms). -/

def cellsLoadP (t : Nat) : List Wire := (List.range 10).flatMap (fun k => [t+6+k, OB5.sig t (t+1034+k)])
def cellsRestoreP (t : Nat) : List Wire :=
  [t+6, OB5.sig t (t+1034), t+7, OB5.sig t (t+1035), t+8, t+9, OB5.sig t (t+1037), t+10, t+11,
   OB5.sig t (t+1039), t+12, OB5.sig t (t+1040), t+13, t+14, OB5.sig t (t+1042), t+15]
/-- Raw codec scratch: port `k` at `1556+k`, skipping the live anchored block `e0(t)..e0(t)+9` (as `poolW` does).
Equal to `1556+k` for every `t ≤ 281`. -/
def scratchW (t k : Nat) : Nat := if 1556 + k < e0P t then 1556 + k else 1566 + k
theorem bTopP_late (t : Nat) (lo : 257 ≤ t) (hi : t ≤ 512) : bTopP t = 1298 - t := by
  unfold bTopP railP
  rw [if_neg (by omega), if_neg (by omega)]
  omega
/-- Codec scratch of the window form: the raw port `scratchW t k` while it is a carry wire of the stock tick `t`
(`scratchW t k + t < 2068`); the ports beyond the carry sit on the released wires of the stock B rail above the three
park slots, `bTop(t)+4 ..` (= `scratchW t k - 766`; only for `t ≥ 369`). Equal to `scratchW t k` for `t ≤ 368`.
(The `OB5.sig t` image of a port beyond the carry is in `[1301, 1044+t]`, which has no phase site.) -/
def scratchS (t k : Nat) : Nat :=
  if scratchW t k + t < 2068 then scratchW t k else bTopP t + 4 + (scratchW t k + t - 2068)
def loadPortsWP (t f : Nat) : List Wire := cellsLoadP t ++ [f, f+1, f+2] ++ (List.range 132).map (scratchS t)
def restorePortsWP (t : Nat) : List Wire := cellsRestoreP t ++ (List.range 134).map (scratchS t)
/-- Exit-form codec scratch. Up to tick 369 it is `scratchS e`. From tick 370 on the anchored block is clean again
after the exit tick, so the scratch is the plain carry prefix `1556+k` while that is a carry wire of the stock tick
`e` (`k + e < 512`: all 134 ports for `e ≤ 378`), and the released B-rail wire `790+k` (= `bTop(e)+4 ..`) beyond. -/
def scratchX (e k : Nat) : Nat :=
  if e ≤ 369 then scratchS e k else if 1556 + k + e < 2068 then 1556 + k else bTopP e + 4 + (1556 + k + e - 2068)
def loadPortsXP (e f : Nat) : List Wire := cellsLoadP e ++ [f, f+1, f+2] ++ (List.range 132).map (scratchX e)
def restorePortsXP (e : Nat) : List Wire := cellsRestoreP e ++ (List.range 134).map (scratchX e)
theorem scratchX_low (e k : Nat) (he : e ≤ 369) : scratchX e k = scratchS e k := if_pos he
theorem loadPortsXP_low (e f : Nat) (he : e ≤ 369) : loadPortsXP e f = loadPortsWP e f := by
  rw [loadPortsXP, loadPortsWP, List.map_congr_left (fun k _ => scratchX_low e k he)]
theorem restorePortsXP_low (e : Nat) (he : e ≤ 369) : restorePortsXP e = restorePortsWP e := by
  rw [restorePortsXP, restorePortsWP, List.map_congr_left (fun k _ => scratchX_low e k he)]
theorem loadPortsXP_length (e f : Nat) : (loadPortsXP e f).length = 155 := by
  simp [loadPortsXP, cellsLoadP]
theorem restorePortsXP_length (e : Nat) : (restorePortsXP e).length = 150 := by
  simp [restorePortsXP, cellsRestoreP]
theorem scratchW_def (t k : Nat) : scratchW t k = if 1556 + k < e0P t then 1556 + k else 1566 + k := rfl
theorem scratchW_bounds (t k : Nat) : 1556 + k ≤ scratchW t k ∧ scratchW t k ≤ 1566 + k := by
  by_cases h : 1556 + k < e0P t
  · rw [scratchW_def, if_pos h]; omega
  · rw [scratchW_def, if_neg h]; omega
/-- The scratch never meets the anchored block `e0(t)..e0(t)+9`. -/
theorem scratchW_ne_e0 (t k i : Nat) (hi : i < 10) : scratchW t k ≠ e0P t + i := by
  by_cases h : 1556 + k < e0P t
  · rw [scratchW_def, if_pos h]; exact Nat.ne_of_lt (by omega)
  · rw [scratchW_def, if_neg h]; exact Nat.ne_of_gt (by omega)
theorem scratchW_inj (t k k' : Nat) (h : scratchW t k = scratchW t k') : k = k' := by
  have e1 := scratchW_def t k
  have e2 := scratchW_def t k'
  by_cases a : 1556 + k < e0P t <;> by_cases b : 1556 + k' < e0P t <;> simp only [a, b, if_true, if_false] at e1 e2 <;>
    omega
theorem scratchW_low (t k : Nat) (h : 1556 + k < e0P t) : scratchW t k = 1556 + k := if_pos h
theorem scratchW_le (t k : Nat) (hk : k < 134) : scratchW t k ≤ 1699 := by
  have := scratchW_bounds t k; omega
theorem scratchS_def (t k : Nat) : scratchS t k =
    if scratchW t k + t < 2068 then scratchW t k else bTopP t + 4 + (scratchW t k + t - 2068) := rfl
/-- A carry wire of the stock tick `t` is not moved. -/
theorem scratchS_eq (t k : Nat) (ht : t < 512) (h : scratchW t k + t < 2068) : scratchS t k = scratchW t k := by
  rw [scratchS_def, if_pos h]
/-- Beyond the stock carry the port sits 766 below its raw wire, in `[1302-t, 933]`. -/
theorem scratchS_high (t k : Nat) (ht : t < 512) (hk : k < 134) (h : 2068 ≤ scratchW t k + t) :
    scratchS t k = scratchW t k - 766 := by
  have l := scratchW_le t k hk
  have b := scratchW_bounds t k
  rw [scratchS_def, if_neg (by omega), bTopP_late t (by omega) (by omega)]
  omega
/-- Every window loader up to tick 368 keeps the raw scratch list. -/
theorem scratchS_window (t k : Nat) (ht : t ≤ 368) (hk : k < 134) : scratchS t k = scratchW t k :=
  scratchS_eq t k (by omega) (by have := scratchW_le t k hk; omega)
theorem scratchS_cases (t k : Nat) (ht : t < 512) (hk : k < 134) :
    (scratchS t k = scratchW t k ∧ 1556 ≤ scratchS t k ∧ scratchS t k ≤ 1699 ∧ scratchS t k + t < 2068) ∨
    (369 ≤ t ∧ 1302 ≤ scratchS t k + t ∧ scratchS t k ≤ 933) := by
  have b := scratchW_bounds t k
  have l := scratchW_le t k hk
  by_cases h : scratchW t k + t < 2068
  · left; rw [scratchS_eq t k ht h]; omega
  · right; rw [scratchS_high t k ht hk (by omega)]; omega
theorem scratchS_ne_e0 (t k i : Nat) (ht : t < 512) (hk : k < 134) (hi : i < 10) : scratchS t k ≠ e0P t + i := by
  have he : 1574 ≤ e0P t := by unfold e0P; omega
  rcases scratchS_cases t k ht hk with ⟨h1, -, -⟩ | ⟨-, -, h2⟩
  · rw [h1]; exact scratchW_ne_e0 t k i hi
  · exact Nat.ne_of_lt (by omega)
theorem scratchS_inj (t k k' : Nat) (ht : t < 512) (hk : k < 134) (hk' : k' < 134) (h : scratchS t k = scratchS t k') :
    k = k' := by
  apply scratchW_inj t
  have b := scratchW_bounds t k
  have b' := scratchW_bounds t k'
  have l := scratchW_le t k hk
  have l' := scratchW_le t k' hk'
  by_cases a : scratchW t k + t < 2068 <;> by_cases a' : scratchW t k' + t < 2068
  · rw [scratchS_eq t k ht a, scratchS_eq t k' ht a'] at h; exact h
  · rw [scratchS_eq t k ht a, scratchS_high t k' ht hk' (by omega)] at h; omega
  · rw [scratchS_high t k ht hk (by omega), scratchS_eq t k' ht a'] at h; omega
  · rw [scratchS_high t k ht hk (by omega), scratchS_high t k' ht hk' (by omega)] at h; omega
/-- A carry wire of the stock tick `e`: the plain port. -/
theorem scratchX_plain (e k : Nat) (he : 370 ≤ e) (h : k + e < 512) : scratchX e k = 1556 + k := by
  unfold scratchX; rw [if_neg (by omega), if_pos (by omega)]
/-- Beyond the stock carry: the released B-rail wire `790+k`. -/
theorem scratchX_host (e k : Nat) (he : 370 ≤ e) (hi : e ≤ 512) (h : 512 ≤ k + e) : scratchX e k = 790 + k := by
  unfold scratchX; rw [if_neg (by omega), if_neg (by omega), bTopP_late e (by omega) hi]; omega
theorem scratchX_cases (e k : Nat) (he : e < 512) (hk : k < 134) :
    (e ≤ 369 ∧ scratchX e k = scratchS e k) ∨ (370 ≤ e ∧ k + e < 512 ∧ scratchX e k = 1556 + k) ∨
    (379 ≤ e ∧ 512 ≤ k + e ∧ scratchX e k = 790 + k) := by
  by_cases a : e ≤ 369
  · left; exact ⟨a, scratchX_low e k a⟩
  · by_cases b : k + e < 512
    · right; left; exact ⟨by omega, b, scratchX_plain e k (by omega) b⟩
    · right; right; exact ⟨by omega, by omega, scratchX_host e k (by omega) (by omega) (by omega)⟩
theorem scratchX_inj (e k k' : Nat) (he : e < 512) (hk : k < 134) (hk' : k' < 134) (h : scratchX e k = scratchX e k') :
    k = k' := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩ <;>
    rcases scratchX_cases e k' he hk' with ⟨a', e2⟩ | ⟨a', b', e2⟩ | ⟨a', b', e2⟩ <;> rw [e1, e2] at h <;>
    first | exact scratchS_inj e k k' he hk hk' h | omega
theorem loadPortsWP_length (t f : Nat) : (loadPortsWP t f).length = 155 := by
  simp [loadPortsWP, cellsLoadP]
theorem restorePortsWP_length (t : Nat) : (restorePortsWP t).length = 150 := by
  simp [restorePortsWP, cellsRestoreP]
theorem loadPortsWP_scratch (t f k : Nat) (hk : k < 132) : (loadPortsWP t f).getD (23 + k) 0 = scratchS t k := by
  have hc : (cellsLoadP t ++ [f, f+1, f+2]).length = 23 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append_right _ _ _ _ (by omega), hc, show 23 + k - 23 = k by omega]
  simp [List.getD_eq_getElem?_getD, hk]
theorem loadPortsWP_flag (t f i : Nat) (hi : i < 3) : (loadPortsWP t f).getD (20 + i) 0 = f + i := by
  have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append _ _ _ _ (by simp [hc]; omega), List.getD_append_right _ _ _ _ (by omega), hc]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
theorem loadPortsWP_cell (t f k : Nat) (hk : k < 20) : (loadPortsWP t f).getD k 0 = (cellsLoadP t).getD k 0 := by
  have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
  rw [loadPortsWP, List.getD_append _ _ _ _ (by simp [hc]; omega), List.getD_append _ _ _ _ (by omega)]
theorem restorePortsWP_scratch (t k : Nat) (hk : k < 134) : (restorePortsWP t).getD (16 + k) 0 = scratchS t k := by
  have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
  rw [restorePortsWP, List.getD_append_right _ _ _ _ (by omega), hc, show 16 + k - 16 = k by omega]
  simp [List.getD_eq_getElem?_getD, hk]
theorem restorePortsWP_cell (t k : Nat) (hk : k < 16) : (restorePortsWP t).getD k 0 = (cellsRestoreP t).getD k 0 := by
  have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
  rw [restorePortsWP, List.getD_append _ _ _ _ (by omega)]
def moveLoadP (t : Nat) : Program := GateMirror.forward (swapsG (moveLoadPairs t))
def moveRestoreP (t f : Nat) : Program := GateMirror.forward (swapsG (moveRestorePairs t f))

section
open MappedCompressed StairArchiveGates

/-- Window-form archive of block `j` at tick `t = start j + 15` (cells of ticks `t-10..t-1`, block `j`'s
flags at `e0(t)+6..8`, codec scratch `scratchS t`), loaded inside block `j+1` after its pack at `t-10`.
`archiveLoadP 10 = archiveLoad240`. -/
def archiveLoadP (j : Fin 23) (d : Bool) : Program :=
  renameProgram (fun q => (loadPortsWP (start j + 15) (e0P (start j + 15) + 6)).getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP (start j + 15)
def archiveRestoreP (j : Fin 23) (d : Bool) : Program :=
  renameProgram (fun q => (restorePortsWP (start j + 15)).getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++ moveRestoreP (start j + 15) (e0P (start j + 15) + 6)
/-- Stock-form archive at the exit tick `e` (flags parked at `bTop(e)+1..3`, exit-form scratch `scratchX e`).
`exitLoadP 270 = archiveLoad270`. -/
def exitLoadP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (loadPortsXP e (bTopP e + 1)).getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP e
def exitRestoreP (e : Nat) (d : Bool) : Program :=
  renameProgram (fun q => (restorePortsXP e).getD q 0)
    (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1) ++ moveRestoreP e (bTopP e + 1)

end

end ECDSAAdd.Entrant.StairPacket.Partial

end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror Challenge
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Generic counts (no evaluation of wires): `Counts ops c m p n` = `c` plain Toffolis, `m` makes, `p` pops,
`n` gates. Then `toffoliCount (forward ops) = c+m`, `toffoliCount (inverse ops) = c+p`,
`measurementCount (forward ops) = p`, `measurementCount (inverse ops) = m`, slots `n+p` / `n+m`. -/

theorem forward_nil : GateMirror.forward [] = [] := rfl
theorem forward_cons (g : Gate) (gs : List Gate) : GateMirror.forward (g :: gs) = front g :: GateMirror.forward gs := rfl
theorem forward_app (a b : List Gate) : GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := List.map_append
theorem inverse_app (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp [inverse, List.map_append, List.reverse_append]


def isCCX : Gate → Bool
  | .ccx _ _ _ => true
  | _ => false
def isMake : Gate → Bool
  | .make _ _ _ => true
  | _ => false
def isPop : Gate → Bool
  | .pop _ _ _ => true
  | _ => false

structure Counts (ops : List Gate) (c m p n : Nat) : Prop where
  ccx : ops.countP isCCX = c
  make : ops.countP isMake = m
  pop : ops.countP isPop = p
  len : ops.length = n

theorem Counts.app {a b : List Gate} {c m p n c' m' p' n' : Nat} (ha : Counts a c m p n) (hb : Counts b c' m' p' n') :
    Counts (a ++ b) (c+c') (m+m') (p+p') (n+n') := by
  obtain ⟨h1,h2,h3,h4⟩ := ha
  obtain ⟨k1,k2,k3,k4⟩ := hb
  exact ⟨by simp [List.countP_append, h1, k1], by simp [List.countP_append, h2, k2],
    by simp [List.countP_append, h3, k3], by simp [h4, k4]⟩
theorem Counts.congr {a : List Gate} {c m p n c' m' p' n' : Nat} (h : Counts a c m p n)
    (e1 : c = c') (e2 : m = m') (e3 : p = p') (e4 : n = n') : Counts a c' m' p' n' := by
  subst e1 e2 e3 e4; exact h
theorem Counts.nil : Counts [] 0 0 0 0 := ⟨rfl, rfl, rfl, rfl⟩
theorem Counts.cons {g : Gate} {gs : List Gate} {c m p n : Nat} (h : Counts gs c m p n) :
    Counts (g :: gs) (c + (isCCX g).toNat) (m + (isMake g).toNat) (p + (isPop g).toNat) (n+1) := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨?_,?_,?_,?_⟩ <;> simp [List.countP_cons, h1, h2, h3, h4] <;> split <;> simp_all

theorem toffoli_forward (ops : List Gate) : toffoliCount (GateMirror.forward ops) = ops.countP isCCX + ops.countP isMake := by
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    rw [forward_cons]
    cases g <;> simp only [front, erase, toffoliCount, List.countP_cons, isCCX, isMake, ih] <;> simp <;> omega
theorem meas_forward (ops : List Gate) : measurementCount (GateMirror.forward ops) = ops.countP isPop := by
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    rw [forward_cons]
    cases g <;> simp only [front, erase, measurementCount, List.countP_cons, isPop, ih] <;> simp <;> omega
theorem slots_forward (ops : List Gate) : gateSlots (GateMirror.forward ops) = ops.length + ops.countP isPop := by
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    rw [forward_cons]
    cases g <;> simp only [front, erase, gateSlots, List.map_cons, List.sum_cons, instructionSlots,
      List.countP_cons, isPop, List.length_cons] at ih ⊢ <;> simp at ih ⊢ <;> omega
private theorem toffoli_reverse (l : Program) : toffoliCount l.reverse = toffoliCount l := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.reverse_cons, toffoliCount_append, ih]; cases i <;> simp [toffoliCount] <;> omega
private theorem meas_reverse (l : Program) : measurementCount l.reverse = measurementCount l := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.reverse_cons, measurementCount_append, ih]; cases i <;> simp [measurementCount] <;> omega
private theorem slots_reverse (l : Program) : gateSlots l.reverse = gateSlots l := by
  simp [gateSlots, List.map_reverse, List.sum_reverse]
theorem toffoli_inverse (ops : List Gate) : toffoliCount (inverse ops) = ops.countP isCCX + ops.countP isPop := by
  rw [inverse, toffoli_reverse]
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons]
    cases g <;> simp only [back, erase, toffoliCount, List.countP_cons, isCCX, isPop, ih] <;> simp <;> omega
theorem meas_inverse (ops : List Gate) : measurementCount (inverse ops) = ops.countP isMake := by
  rw [inverse, meas_reverse]
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons]
    cases g <;> simp only [back, erase, measurementCount, List.countP_cons, isMake, ih] <;> simp <;> omega
theorem slots_inverse (ops : List Gate) : gateSlots (inverse ops) = ops.length + ops.countP isMake := by
  rw [inverse, slots_reverse]
  induction ops with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp only [back, erase, gateSlots, List.map_cons, List.sum_cons, instructionSlots,
      List.countP_cons, isMake, List.length_cons] at ih ⊢ <;> simp at ih ⊢ <;> omega
theorem Counts.programs {ops : List Gate} {c m p n : Nat} (h : Counts ops c m p n) :
    toffoliCount (GateMirror.forward ops) = c + m ∧ toffoliCount (inverse ops) = c + p ∧
    measurementCount (GateMirror.forward ops) = p ∧ measurementCount (inverse ops) = m ∧
    gateSlots (GateMirror.forward ops) = n + p ∧ gateSlots (inverse ops) = n + m := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  rw [toffoli_forward, toffoli_inverse, meas_forward, meas_inverse, slots_forward, slots_inverse, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! Gadget counts. -/

theorem counts_cxsG (q : Wire) (xs : List Wire) : Counts (cxsG q xs) 0 0 0 xs.length := by
  induction xs with
  | nil => exact Counts.nil
  | cons x xs ih => exact (Counts.cons (g := .cx q x) ih).congr rfl rfl rfl (by simp)
theorem counts_xsG (xs : List Wire) : Counts (xsG xs) 0 0 0 xs.length := by
  induction xs with
  | nil => exact Counts.nil
  | cons x xs ih => exact (Counts.cons (g := .x x) ih).congr rfl rfl rfl (by simp)
theorem counts_togglesG (c : Wire) (xs : List Wire) : Counts (togglesG c xs) 0 0 0 xs.length := by
  induction xs with
  | nil => exact Counts.nil
  | cons x xs ih => exact (Counts.cons (g := .cx x c) ih).congr rfl rfl rfl (by simp)
theorem counts_addG : ∀ (cs ys : List Wire) (cin : Wire), ys.length = cs.length + 1 →
    Counts (addG ys cs cin) 0 cs.length cs.length (3*cs.length + 1)
  | [], [y], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | c::cs, y::y'::ys, cin, h => by
    have ih := counts_addG cs (y'::ys) c (by simpa using h)
    have e : addG (y::y'::ys) (c::cs) cin = [.make y cin c] ++ (addG (y'::ys) cs c ++ [.pop y cin c, .cx cin y]) := rfl
    rw [e]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.make y cin c] 0 1 0 1).app
      (ih.app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop y cin c, .cx cin y] 0 0 1 2))).congr
      rfl (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))
  | [], [], _, h => by simp at h
  | [], _::_::_, _, h => by simp at h
  | _::_, [], _, h => by simp at h
  | _::_, [_], _, h => by simp at h
theorem counts_shiftG (c : Wire) (w : Nat → Wire) (d n : Nat) : Counts (shiftG c w d n) n 0 0 (3*n) := by
  induction n with
  | zero => exact Counts.nil
  | succ n ih =>
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts (cswapG c (w (n+d)) (w n)) 1 0 0 3).app ih).congr (by omega) rfl rfl (by omega)
theorem counts_stageG (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) :
    Counts (stageG c w xs d n) n 0 0 (2*xs.length + 3*n) :=
  ((counts_togglesG c xs).app ((counts_shiftG c w d n).app (counts_togglesG c xs))).congr
    (by omega) rfl rfl (by omega)
theorem counts_digitsG (hot bank : Nat → Wire) (c d start n : Nat) :
    Counts (digitsG hot bank c d start n) (2*n) 0 0 (2*n) := by
  induction n generalizing start with
  | zero => exact Counts.nil
  | succ n ih =>
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts (clearG (hot start) c d (bank start) (bank (start+1))) 2 0 0 2).app
      (ih (start+1))).congr (by omega) rfl rfl (by omega)
theorem counts_wordG (a : Wire) : ∀ rs : List HighBankJoin.Column,
    Counts (wordG a rs) rs.length 0 0 (3*rs.length + 2*rs.countP (fun r => r.hot.isSome) - rs.countP (fun r => r.low))
  | [] => Counts.nil
  | r::rs => by
    have ih := counts_wordG a rs
    have hp : Counts (pairG r.low a r.shadow r.tube) 1 0 0 (if r.low then 2 else 3) := by
      cases r.low <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have ht : Counts (toggleG a r.hot) 0 0 0 (if r.hot.isSome then 1 else 0) := by
      cases r.hot <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have hl := List.countP_le_length (p := fun r : HighBankJoin.Column => r.low) (l := rs)
    exact (ht.app (hp.app (ih.app ht))).congr (by first | omega | (simp <;> omega)) rfl rfl (by
      simp only [List.length_cons, List.countP_cons]
      cases r.low <;> cases r.hot.isSome <;> simp <;> omega)
theorem counts_chainG (c seq : Nat → Wire) {body : List Gate} {cb mb pb nb : Nat} (hb : Counts body cb mb pb nb) :
    ∀ (i n : Nat), Counts (chainG c seq body i n) cb (mb+n) (pb+n) (nb+2*n)
  | _, 0 => hb
  | i, n+1 => by
    have ih := counts_chainG c seq hb (i+1) n
    have e : chainG c seq body i (n+1) =
        [.make (c i) (seq i) (c (i+1))] ++ (chainG c seq body (i+1) n ++ [.pop (c i) (seq i) (c (i+1))]) := rfl
    rw [e]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.make (c i) (seq i) (c (i+1))] 0 1 0 1).app
      (ih.app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (c i) (seq i) (c (i+1))] 0 0 1 1))).congr
      (by omega) (by omega) (by omega) (by omega)
theorem counts_eventsG : ∀ (a out : Wire) (ps : List (Wire × Wire)),
    Counts (eventsG a out ps) 0 ps.length ps.length (4*ps.length + 1)
  | _, _, [] => ⟨rfl, rfl, rfl, rfl⟩
  | a, out, (x,t)::ps => by
    have ih := counts_eventsG t out ps
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.x x, .make a x t] 0 1 0 2).app
      (ih.app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop a x t, .x x] 0 0 1 2))).congr
      rfl (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))
theorem counts_swapsG : ∀ ps : List (Wire × Wire), Counts (swapsG ps) 0 0 0 (3*ps.length)
  | [] => Counts.nil
  | p::ps => by
    have e : swapsG (p::ps) = swapG p ++ swapsG ps := List.flatMap_cons
    rw [e]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts (swapG p) 0 0 0 3).app (counts_swapsG ps)).congr rfl rfl rfl (by first | omega | (simp <;> omega))
theorem counts_exchangeG (c : Wire) : ∀ ps : List (Wire × Wire), Counts (exchangeG c ps) ps.length 0 0 (3*ps.length)
  | [] => Counts.nil
  | p::ps => by
    have e : exchangeG c (p::ps) = [.cx p.1 p.2, .ccx c p.2 p.1, .cx p.1 p.2] ++ exchangeG c ps := List.flatMap_cons
    rw [e]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx p.1 p.2, .ccx c p.2 p.1, .cx p.1 p.2] 1 0 0 3).app
      (counts_exchangeG c ps)).congr (by first | omega | (simp <;> omega)) rfl rfl (by first | omega | (simp <;> omega))
theorem counts_transferG : ∀ ps : List (Wire × Wire), Counts (transferG ps) 0 0 0 (2*ps.length)
  | [] => Counts.nil
  | p::ps => by
    have e : transferG (p::ps) = [.cx p.1 p.2, .cx p.2 p.1] ++ transferG ps := List.flatMap_cons
    rw [e]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx p.1 p.2, .cx p.2 p.1] 0 0 0 2).app (counts_transferG ps)).congr
      rfl rfl rfl (by first | omega | (simp <;> omega))
theorem counts_mapG {α : Type} (l : List α) (f : α → Gate) (cc mk pp : Bool) (hc : ∀ x, isCCX (f x) = cc)
    (hm : ∀ x, isMake (f x) = mk) (hp : ∀ x, isPop (f x) = pp) :
    Counts (l.map f) (if cc then l.length else 0) (if mk then l.length else 0) (if pp then l.length else 0) l.length := by
  induction l with
  | nil => exact ⟨by cases cc <;> rfl, by cases mk <;> rfl, by cases pp <;> rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨h1,h2,h3,h4⟩ := ih
    refine ⟨?_,?_,?_,by simp⟩ <;> simp only [List.map_cons, List.countP_cons, h1, h2, h3, hc, hm, hp] <;>
      cases cc <;> cases mk <;> cases pp <;> simp <;> omega
theorem countP_range_lt (n L : Nat) : (List.range n).countP (fun i => decide (i < L)) = min n L := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.countP_append, ih]; simp; split <;> omega
theorem counts_flatCswap (n : Nat) (c : Wire) (f g : Nat → Wire) :
    Counts ((List.range n).flatMap (fun i => cswapG c (f i) (g i))) n 0 0 (3*n) := by
  induction n with
  | zero => exact Counts.nil
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact (ih.app (⟨rfl, rfl, rfl, rfl⟩ : Counts (cswapG c (f n) (g n)) 1 0 0 3)).congr rfl rfl rfl (by omega)

/-! Fixed templates (by evaluation of the gate kinds only). -/

theorem counts_leaveFix0 (s h : Nat) : Counts (leaveFix0 s h) 19 0 0 78 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix1 (s h : Nat) : Counts (leaveFix1 s h) 0 0 0 15 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix2 (s h : Nat) : Counts (leaveFix2 s h) 18 36 35 149 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix3 (s h : Nat) : Counts (leaveFix3 s h) 0 1 0 3 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix4 (s h : Nat) : Counts (leaveFix4 s h) 0 15 0 30 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix5 (s h : Nat) : Counts (leaveFix5 s h) 16 20 0 59 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix8 (s h : Nat) : Counts (leaveFix8 s h) 0 0 0 2 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix10 (s h : Nat) : Counts (leaveFix10 s h) 0 0 0 2 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix11 (s h : Nat) : Counts (leaveFix11 s h) 0 0 20 37 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_leaveFix12 (s h : Nat) : Counts (leaveFix12 s h) 0 0 15 30 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_enterFix (s h : Nat) : Counts (enterFix s h) 12 6 6 86 := ⟨rfl, rfl, rfl, rfl⟩
/-! Segment counts. -/

theorem counts_leaveAdjust (s : Nat) (hw : 1 ≤ wpP s) :
    Counts (leaveAdjust s) 0 (wpP s - 1) (wpP s - 1) (5*wpP s - 2) :=
  ((counts_cxsG _ _).app ((counts_addG _ _ _ (by first | omega | (simp <;> omega))).app (counts_cxsG _ _))).congr
    (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))
theorem counts_leaveBarrel (s : Nat) : Counts (leaveBarrel s) (4*wpP s + 11) 0 0 (12*wpP s + 97) :=
  ((((counts_stageG _ _ _ _ _).app (counts_stageG _ _ _ _ _)).app (counts_stageG _ _ _ _ _)).app
    (counts_stageG _ _ _ _ _)).congr (by omega) rfl rfl
    (by simp only [controlsP0, controlsP1, controlsP2, controlsP3, List.length_cons, List.length_nil]; omega)
theorem counts_leaveJoin (s : Nat) (hL : lowsP s ≤ 18) : Counts (leaveJoin s) 50 0 0 (118 - lowsP s) := by
  have hw := counts_wordG 1614 (columnsP s)
  have e1 : (columnsP s).length = 18 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => decide (i < lowsP s)) = lowsP s
    rw [countP_range_lt]; omega
  rw [e1, e2, e3] at hw
  exact ((counts_digitsG _ _ _ _ _ _).app hw).congr (by omega) rfl rfl (by omega)
theorem counts_leaveLowStore (s : Nat) (hL : 1 ≤ lowsP s) :
    Counts (leaveLowStore s) (lowsP s) (lowsP s - 1) (lowsP s + 1) (6*lowsP s + 4) := by
  have a := counts_mapG (List.range (lowsP s)) (fun i => Gate.ccx 1556 (a0P s + i) (b0P s + i)) true false false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have b := counts_xsG ((List.range (lowsP s)).map (b0P s + ·))
  have c := counts_addG ((List.range (lowsP s - 1)).map (1559 + ·)) ((List.range (lowsP s)).map (b0P s + ·)) 1558
    (by first | omega | (simp <;> omega))
  exact ((((((⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.cx (e0P s + 3) 1560, .cx 1559 1560, .pop (e0P s + 3) (e0P s + 4) 1559] 0 0 1 3).app a).app b).app c).app
    b).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (b0P s - 1) 1557 1558, .cx (a0P s - 1) 1557, .x 1557] 0 0 1 3)).congr
    (by simp) (by simp) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))
theorem counts_leaveStoreMapped (s : Nat) (hL : lowsP s ≤ wpP s + 15) :
    Counts (leaveStoreMapped s) 0 (wpP s + 19) (wpP s + 18) (4*wpP s + 79) := by
  let L := lowsP s; let top := a0P s + L - 1; let H := wpP s + 15 - L
  let hi := (List.range H).map (fun i => bankW s (L+i))
  let seq := fun i => if i = 0 then top else bankW s (L+i-1)
  let seq2 := (List.range (L+1)).map (b0P s - 1 + ·)
  have c1 := counts_chainG storeW seq (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (storeW (H+1)) 1557, .x 1557] 0 0 0 2) 0 (H+1)
  have c2 := counts_chainG (1558 + ·) (b0P s - 1 + ·)
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (1558+(L+1)) 1556, .x 1556] 0 0 0 2) 0 (L+1)
  have x1 := counts_xsG hi
  have x2 := counts_xsG hi.reverse
  have x3 := counts_xsG seq2
  have x4 := counts_xsG seq2.reverse
  exact ((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.make (top-2) (top-1) 1558, .x 1558, .x top] 0 1 0 3).app
    x1).app c1).app x2).app (⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.x top, .x 1558, .pop (top-2) (top-1) 1558, .make 1556 1557 1558, .x 1558] 0 1 1 5)).app
    x3).app c2).app x4).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x 1558] 0 0 0 1))).congr
    (by simp) (by simp [H, L]; omega) (by simp [H, L]; omega) (by simp [hi, seq2, H, L]; omega)
theorem counts_leaveLowClose (s : Nat) : Counts (leaveLowClose s) (lowsP s + 1) 0 0 (4*lowsP s + 19) := by
  have a := counts_xsG ((List.range 15).map (s+16+·))
  have b := counts_mapG (List.range (lowsP s + 1)) (fun i => Gate.cx (e0P s + 5) (b0P s - 1 + i)) false false false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have c := counts_flatCswap (lowsP s + 1) (s+30) (fun i => b0P s - 1 + i) (fun i => a0P s - 1 + i)
  exact ((a.app b).app c).congr (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))
theorem counts_leaveClose (s : Nat) (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveClose s) 0 5 5 (21 + 3*(wpP (s+15) + 3)) := by
  have a := counts_eventsG (e0P s + 7) (e0P s + 4)
    [(OB5.sig (s+14) (s+1044), 1556), (OB5.sig (s+14) (s+1045), 1559), (OB5.sig (s+14) (s+1046), 1560),
     (OB5.sig (s+14) (s+1047), 1561), (OB5.sig (s+14) (s+1048), 1562)]
  have b := counts_swapsG (movesP s)
  exact (a.app b).congr (by simp) (by simp) (by simp) (by simp [movesP]; omega)

/-- The whole leave, for every block start `s` with a sane geometry. -/
theorem counts_leaveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 18)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveOps s) (4*wpP s + 2*lowsP s + 115) (2*wpP s + lowsP s + 94) (2*wpP s + lowsP s + 93)
      (21*wpP s + 9*lowsP s + 750 + 3*wpP (s+15)) := by
  have := ((((((((((((((((counts_leaveFix0 s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (counts_leaveFix2 s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5 s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (counts_leaveFix8 s (sbP s))).app (counts_leaveJoin s hL2)).app (counts_leaveFix10 s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  exact this.congr (by omega) (by omega) (by omega) (by omega)

theorem latch_counts (e : Option Wire) (out : Wire) : ∀ (a : Wire) (ps : List (Wire × Wire)),
    Counts (latchChainG e out a ps) (if e.isSome then 1 else 0) ps.length ps.length (2*ps.length + 2)
  | a, [] => by cases e <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | a, (x,t)::ps => by
    have ih := latch_counts e out t ps
    have eq : latchChainG e out a ((x,t)::ps) = [.make a x t] ++ (latchChainG e out t ps ++ [.pop a x t]) := rfl
    rw [eq]
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.make a x t] 0 1 0 1).app
      (ih.app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop a x t] 0 0 1 1))).congr
      (by omega) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))
theorem counts_latchG (rev : Bool) (e : Option Wire) (out a : Wire) (ps : List (Wire × Wire)) :
    Counts (latchG rev e out a ps) (if e.isSome then 1 else 0) ps.length ps.length (4*ps.length + 4) := by
  have x1 := counts_xsG (a :: ps.map Prod.fst)
  have x2 := counts_xsG (if rev then (a :: ps.map Prod.fst).reverse else a :: ps.map Prod.fst)
  have l : (if rev then (a :: ps.map Prod.fst).reverse else a :: ps.map Prod.fst).length = ps.length + 1 := by
    cases rev <;> simp
  rw [l] at x2
  exact (x1.app ((latch_counts e out a ps).app x2)).congr (by omega) (by omega) (by omega) (by first | omega | (simp <;> omega))

/-- The portal at tick `t`. -/
theorem counts_portalOps (t : Nat) (hw : 5 ≤ wpP t) :
    Counts (portalOps t) (2*wpP t + 1) (3*wpP t - 5) (3*wpP t - 5) (18*wpP t - 2) := by
  let w := wpP t; let aBot := a0P t; let bBot := 802 + sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-3)).map (aBot + 3 + ·); let bB := (List.range (w-3)).map (bBot + 3 + ·)
  let sgn := e0P t + 5; let G := t + 15; let f3 := e0P t + 3; let f4 := e0P t + 4
  have zAB : (rA.zip rB).length = w := by simp [rA, rB]
  have zb : (bA.zip bB).length = w - 3 := by simp [bA, bB]
  have p1 := counts_exchangeG G (rA.zip rB)
  have p2 := counts_cxsG sgn rB
  have p3 := counts_latchG true none 1556 1557 ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i)))
  have p4 := counts_latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i)))
  have p5 := counts_addG ((List.range (w-4)).map (1557 + ·)) bB 1556 (by simp [bB]; omega)
  have p6 := counts_mapG (bA.zip bB) (fun p => Gate.ccx f4 p.1 p.2) true false false (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  have p7 := counts_transferG (bA.zip bB)
  have p8 := counts_cxsG sgn [bBot, bBot+1, bBot+2]
  have p9 := counts_exchangeG G [(aBot, bBot), (aBot+1, bBot+1), (aBot+2, bBot+2)]
  exact ((((((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] 0 0 0 2).app
    p1).app p2).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.make aBot (aBot+1) 1557] 0 1 0 1)).app p3).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop aBot (aBot+1) 1557, .cx 1556 f3, .cx f3 1556] 0 0 1 3)).app p4).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x (aBot+2), .make (bBot+2) (aBot+2) 1556] 0 1 0 2)).app p5).app p6).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (bBot+2) (aBot+2) 1556, .x (aBot+2)] 0 0 1 2)).app p7).app p8).app p9).congr
    (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega)
    (by simp [zAB, zb, rB, w] at *; omega)

theorem counts_parkOps (e : Nat) : Counts (parkOps e) 0 0 0 9 := (counts_swapsG _).congr rfl rfl rfl rfl

/-! Window statements (the interface par-d uses). `j ∈ [1,21]` covers blocks 90..390 (exit 405). -/

theorem window_geom : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    31 ≤ wpP (start j) ∧ 10 ≤ lowsP (start j) ∧ lowsP (start j) ≤ 11 ∧ 38 ≤ wpP (start j + 15) := by
  decide
theorem leave_counts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    toffoliCount (leaveP j) = 6*wpP (start j) + 3*lowsP (start j) + 209 ∧
    toffoliCount (leaveInvP j) = 6*wpP (start j) + 3*lowsP (start j) + 208 ∧
    measurementCount (leaveP j) = 2*wpP (start j) + lowsP (start j) + 93 ∧
    measurementCount (leaveInvP j) = 2*wpP (start j) + lowsP (start j) + 94 ∧
    gateSlots (leaveP j) = 23*wpP (start j) + 10*lowsP (start j) + 843 + 3*wpP (start j + 15) ∧
    gateSlots (leaveInvP j) = 23*wpP (start j) + 10*lowsP (start j) + 844 + 3*wpP (start j + 15) := by
  obtain ⟨g1,g2,g3,g4⟩ := window_geom j h0 (by omega)
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_leaveOps (start j) (by omega) (by omega) (by omega) (by omega)).programs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [leaveP, t1]; omega
  · rw [leaveInvP, t2]; omega
  · rw [leaveP, m1]
  · rw [leaveInvP, m2]
  · rw [leaveP, s1]; omega
  · rw [leaveInvP, s2]; omega
theorem enter_counts (j : Fin 23) :
    toffoliCount (enterP j) = 18 ∧ toffoliCount (enterInvP j) = 18 ∧
    measurementCount (enterP j) = 6 ∧ measurementCount (enterInvP j) = 6 ∧
    gateSlots (enterP j) = 92 ∧ gateSlots (enterInvP j) = 92 :=
  (counts_enterFix _ _).programs
theorem portal_counts (t : Nat) (hw : 5 ≤ wpP t) :
    toffoliCount (portalP t) = 5*wpP t - 4 ∧ toffoliCount (portalInvP t) = 5*wpP t - 4 ∧
    measurementCount (portalP t) = 3*wpP t - 5 ∧ measurementCount (portalInvP t) = 3*wpP t - 5 ∧
    gateSlots (portalP t) = 21*wpP t - 7 ∧ gateSlots (portalInvP t) = 21*wpP t - 7 := by
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_portalOps t hw).programs
  exact ⟨by rw [portalP, t1]; omega, by rw [portalInvP, t2]; omega, by rw [portalP, m1], by rw [portalInvP, m2],
    by rw [portalP, s1]; omega, by rw [portalInvP, s2]; omega⟩
theorem park_counts (e : Nat) :
    toffoliCount (parkP e) = 0 ∧ toffoliCount (parkInvP e) = 0 ∧
    measurementCount (parkP e) = 0 ∧ measurementCount (parkInvP e) = 0 ∧
    gateSlots (parkP e) = 9 ∧ gateSlots (parkInvP e) = 9 :=
  (counts_parkOps e).programs

end ECDSAAdd.Entrant.StairPacket.Partial

end

/-! leave-move: c9cc6a76's leaveMove on the generic leave. The 16 selector-mux Toffolis into the crossing wire
`e0+6` (gates 27..42 of `leaveFix5`) become 16 controlled swaps (`rowGates`), and the 16 digit clears of the join's
digit pass (`digitsG`, the head of `leaveJoin`) are dropped (`keptG`): 16 Toffolis fewer per leave and per inverse. -/

section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror Challenge
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The move rows `(tag i, join cell i)`. -/
def moveRows (s : Nat) : List MoveChain.Row := (List.range 16).map (fun i => (tagsP.getD i 0, a0P s + i))
/-- `digitsG` without its clears (the kept half of the digit pass). -/
def keptG (hot bank : Nat → Wire) (d start : Nat) : Nat → List Gate
  | 0 => []
  | n+1 => .ccx (hot start) d (bank (start+1)) :: keptG hot bank d (start+1) n
/-- The rows the clears of `digitsG` read. -/
def rowsD (hot bank : Nat → Wire) (start : Nat) : Nat → List MoveChain.Row
  | 0 => []
  | n+1 => (hot start, bank start) :: rowsD hot bank (start+1) n

/-- Segment 5 of the move leave: the selector with the cross mux as controlled swaps. -/
def leaveFix5Move (s h : Nat) : List Gate :=
  (leaveFix5 s h).take 27 ++ (rowGates (e0P s + 6) (moveRows s) ++ (leaveFix5 s h).drop 43)
/-- Segment 9 of the move leave: the digit pass without the clears, then the word pass. -/
def leaveJoinMove (s : Nat) : List Gate :=
  keptG (tagsP.getD · 0) (fun i => a0P s + i) 1613 0 16 ++ wordG 1614 (columnsP s)

/-- The move leave of the block at tick `s` (c9cc6a76's `leave{s}Move`, generic). -/
def leaveMoveOps (s : Nat) : List Gate :=
  leaveFix0 s (sbP s) ++ leaveFix1 s (sbP s) ++ leaveFix2 s (sbP s) ++ leaveFix3 s (sbP s) ++
  leaveFix4 s (sbP s) ++ leaveFix5Move s (sbP s) ++ leaveAdjust s ++ leaveBarrel s ++
  leaveFix8 s (sbP s) ++ leaveJoinMove s ++ leaveFix10 s (sbP s) ++ leaveFix11 s (sbP s) ++
  leaveFix12 s (sbP s) ++ leaveLowStore s ++ leaveStoreMapped s ++ leaveLowClose s ++ leaveClose s

def leaveMoveP (j : Fin 23) : Program := GateMirror.forward (leaveMoveOps (start j))
def leaveMoveInvP (j : Fin 23) : Program := inverse (leaveMoveOps (start j))

/-! Counts. -/

theorem moveRows_length (s : Nat) : (moveRows s).length = 16 := by simp [moveRows]

theorem counts_rowGates (c : Wire) : ∀ rs : List MoveChain.Row, Counts (rowGates c rs) rs.length 0 0 (3*rs.length)
  | [] => Counts.nil
  | r :: rs => by
    have ih := counts_rowGates c rs
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx r.2 c, .ccx r.1 c r.2, .cx r.2 c] 1 0 0 3).app ih).congr
      (by simp; omega) rfl rfl (by simp; omega)

theorem counts_keptG (hot bank : Nat → Wire) (d : Nat) : ∀ start n, Counts (keptG hot bank d start n) n 0 0 n
  | _, 0 => Counts.nil
  | start, n+1 => by
    have ih := counts_keptG hot bank d (start+1) n
    exact ((⟨rfl, rfl, rfl, rfl⟩ : Counts [.ccx (hot start) d (bank (start+1))] 1 0 0 1).app ih).congr
      (by omega) rfl rfl (by omega)

theorem counts_leaveFix5Move (s h : Nat) : Counts (leaveFix5Move s h) 16 20 0 91 := by
  have a : Counts ((leaveFix5 s h).take 27) 0 19 0 27 := ⟨rfl, rfl, rfl, rfl⟩
  have b : Counts ((leaveFix5 s h).drop 43) 0 1 0 16 := ⟨rfl, rfl, rfl, rfl⟩
  have r := counts_rowGates (e0P s + 6) (moveRows s)
  rw [moveRows_length] at r
  exact (a.app (r.app b)).congr rfl rfl rfl rfl

theorem counts_leaveJoinMove (s : Nat) (hL : lowsP s ≤ 18) : Counts (leaveJoinMove s) 34 0 0 (102 - lowsP s) := by
  have hw := counts_wordG 1614 (columnsP s)
  have e1 : (columnsP s).length = 18 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 18).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    have hl := (counts_leaveJoin s hL).len
    have hd := (counts_digitsG (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16).len
    have hw' := hw.len
    simp only [leaveJoin, List.length_append] at hl
    rw [e1, e2] at hw'
    omega
  rw [e1, e2, e3] at hw
  exact ((counts_keptG _ _ 1613 0 16).app hw).congr (by omega) rfl rfl (by omega)

theorem counts_leaveMoveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 18)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveMoveOps s) (4*wpP s + 2*lowsP s + 99) (2*wpP s + lowsP s + 94) (2*wpP s + lowsP s + 93)
      (21*wpP s + 9*lowsP s + 766 + 3*wpP (s+15)) := by
  have := ((((((((((((((((counts_leaveFix0 s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (counts_leaveFix2 s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5Move s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (counts_leaveFix8 s (sbP s))).app (counts_leaveJoinMove s hL2)).app (counts_leaveFix10 s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  have base := counts_leaveOps s hw hL1 hL2 hn
  exact this.congr (by omega) (by omega) (by omega) (by omega)

theorem leaveMove_counts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    toffoliCount (leaveMoveP j) = 6*wpP (start j) + 3*lowsP (start j) + 193 ∧
    toffoliCount (leaveMoveInvP j) = 6*wpP (start j) + 3*lowsP (start j) + 192 ∧
    measurementCount (leaveMoveP j) = 2*wpP (start j) + lowsP (start j) + 93 ∧
    measurementCount (leaveMoveInvP j) = 2*wpP (start j) + lowsP (start j) + 94 ∧
    gateSlots (leaveMoveP j) = 23*wpP (start j) + 10*lowsP (start j) + 859 + 3*wpP (start j + 15) ∧
    gateSlots (leaveMoveInvP j) = 23*wpP (start j) + 10*lowsP (start j) + 860 + 3*wpP (start j + 15) := by
  obtain ⟨g1,g2,g3,g4⟩ := window_geom j h0 (by omega)
  obtain ⟨t1,t2,m1,m2,s1,s2⟩ := (counts_leaveMoveOps (start j) (by omega) (by omega) (by omega) (by omega)).programs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [leaveMoveP, t1]; omega
  · rw [leaveMoveInvP, t2]; omega
  · rw [leaveMoveP, m1]
  · rw [leaveMoveInvP, m2]
  · rw [leaveMoveP, s1]; omega
  · rw [leaveMoveInvP, s2]; omega

/-! Shape: the reference leave and the move leave share every gate outside the mux and the digit pass. -/

def moveA (s : Nat) : List Gate :=
  leaveFix0 s (sbP s) ++ leaveFix1 s (sbP s) ++ leaveFix2 s (sbP s) ++ leaveFix3 s (sbP s) ++
  leaveFix4 s (sbP s) ++ (leaveFix5 s (sbP s)).take 27
def moveMux (s : Nat) : List Gate := ((leaveFix5 s (sbP s)).drop 27).take 16
def moveB (s : Nat) : List Gate :=
  (leaveFix5 s (sbP s)).drop 43 ++ leaveAdjust s ++ leaveBarrel s ++ leaveFix8 s (sbP s)
def moveDig (s : Nat) : List Gate := digitsG (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16
def moveKept (s : Nat) : List Gate := keptG (tagsP.getD · 0) (fun i => a0P s + i) 1613 0 16
def moveC (s : Nat) : List Gate :=
  wordG 1614 (columnsP s) ++ leaveFix10 s (sbP s) ++ leaveFix11 s (sbP s) ++
  leaveFix12 s (sbP s) ++ leaveLowStore s ++ leaveStoreMapped s ++ leaveLowClose s ++ leaveClose s

theorem fix5_split (s h : Nat) :
    leaveFix5 s h = (leaveFix5 s h).take 27 ++ (((leaveFix5 s h).drop 27).take 16 ++ (leaveFix5 s h).drop 43) := rfl

theorem leaveOps_shape (s : Nat) :
    leaveOps s = moveA s ++ (moveMux s ++ (moveB s ++ (moveDig s ++ moveC s))) := by
  have e := fix5_split s (sbP s)
  unfold leaveOps moveA moveMux moveB moveDig moveC leaveJoin
  conv_lhs => rw [e]
  simp only [List.append_assoc]

theorem leaveMoveOps_shape (s : Nat) :
    leaveMoveOps s = moveA s ++ (rowGates (e0P s + 6) (moveRows s) ++ (moveB s ++ (moveKept s ++ moveC s))) := by
  unfold leaveMoveOps moveA moveB moveKept moveC leaveJoinMove leaveFix5Move
  simp only [List.append_assoc]

theorem mux_forward (s : Nat) : GateMirror.forward (moveMux s) = MoveChain.mux (e0P s + 6) (moveRows s) := by
  have e : sbP s + 1580 = e0P s + 6 := by unfold e0P; omega
  unfold moveMux
  rw [← e]
  rfl

theorem digits_weave (hot bank : Nat → Wire) (c d : Nat) : ∀ start n,
    GateMirror.forward (digitsG hot bank c d start n) =
      MoveChain.weave c (rowsD hot bank start n) (GateMirror.forward (keptG hot bank d start n))
  | _, 0 => rfl
  | start, n+1 => by
    have ih := digits_weave hot bank c d (start+1) n
    show Instr.CCX (hot start) c (bank start) :: Instr.CCX (hot start) d (bank (start+1)) ::
        GateMirror.forward (digitsG hot bank c d (start+1) n) = _
    rw [ih]; rfl

theorem rowsD_moveRows (s : Nat) : rowsD (tagsP.getD · 0) (fun i => a0P s + i) 0 16 = moveRows s := rfl

theorem dig_forward (s : Nat) :
    GateMirror.forward (moveDig s) = MoveChain.weave (e0P s + 6) (moveRows s) (GateMirror.forward (moveKept s)) := by
  unfold moveDig moveKept; rw [digits_weave, rowsD_moveRows]

end ECDSAAdd.Entrant.StairPacket.Partial
end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Bridges: `forward` of each Gate-level gadget is dadon's Instr-level gadget, so dadon's gadget
theorems apply to the parametric segments unchanged. -/

theorem forward_cxsG (q : Wire) (xs : List Wire) : GateMirror.forward (cxsG q xs) = signComplement q xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [cxsG, signComplement, List.map_cons] at ih ⊢; rw [forward_cons, ih]; rfl
theorem forward_addG : ∀ (ys cs : List Wire) (cin : Wire), GateMirror.forward (addG ys cs cin) = HighBankUnit.add ys cs cin
  | [], _, _ => rfl
  | [y], _, cin => by simp [addG, HighBankUnit.add, HighBankUnit.zeros, mappedAdd, mappedSum, GateMirror.forward, front]
  | _::_::_, [], _ => rfl
  | y::y'::ys, c::cs, cin => by
    have ih := forward_addG (y'::ys) cs c
    simp only [addG, HighBankUnit.add, HighBankUnit.zeros, List.length_cons, List.replicate_succ] at ih ⊢
    rw [forward_cons, forward_app, ih]
    simp [mappedAdd, mappedMajority, mappedEraseCarry, mappedSum, GateMirror.forward, front, erase]
theorem forward_adjustG (ys cs : List Wire) (cin neg : Wire) :
    GateMirror.forward (adjustG ys cs cin neg) = HighBankAdjust.adjust ys cs cin neg := by
  simp only [adjustG, HighBankAdjust.adjust, forward_app, forward_cxsG, forward_addG]
theorem forward_shiftG (c : Wire) (w : Nat → Wire) (d n : Nat) :
    GateMirror.forward (shiftG c w d n) = HighBankShift.program c w d n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftG, HighBankShift.program, forward_app, ih]; rfl
theorem forward_togglesG (c : Wire) (xs : List Wire) : GateMirror.forward (togglesG c xs) = HighBankControl.toggles c xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [togglesG, HighBankControl.toggles, List.map_cons] at ih ⊢; rw [forward_cons, ih]; rfl
theorem forward_stageG (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) :
    GateMirror.forward (stageG c w xs d n) = HighBankBarrel.stage c w xs d n := by
  simp only [stageG, HighBankBarrel.stage, forward_app, forward_togglesG, forward_shiftG]
theorem forward_digitsG (hot bank : Nat → Wire) (c d start n : Nat) :
    GateMirror.forward (digitsG hot bank c d start n) = HighBankJoin.digits hot bank c d start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [digitsG, HighBankJoin.digits, forward_app, ih]; rfl
theorem forward_pairG (low : Bool) (a s t : Wire) : GateMirror.forward (pairG low a s t) = HighBankJoin.pair low a s t := by
  cases low <;> rfl
theorem forward_toggleG (a : Wire) (h : Option Wire) : GateMirror.forward (toggleG a h) = HighBankJoin.toggle a h := by
  cases h <;> rfl
theorem forward_wordG (a : Wire) (rs : List HighBankJoin.Column) : GateMirror.forward (wordG a rs) = HighBankJoin.word a rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [wordG, HighBankJoin.word, forward_app, forward_toggleG, forward_pairG, ih]

/-- Segment 6 is `adjust` on the parametric bank and pool. -/
theorem forward_leaveAdjust (s : Nat) : GateMirror.forward (leaveAdjust s) =
    HighBankAdjust.adjust ((List.range (wpP s)).map (bankW s)) ((List.range (wpP s - 1)).map (poolW s)) (e0P s + 6) 1597 :=
  forward_adjustG _ _ _ _
/-- Segment 7 is the four barrel stages. -/
theorem forward_leaveBarrel (s : Nat) : GateMirror.forward (leaveBarrel s) =
    HighBankBarrel.stage 1613 (bankW s) controlsP0 1 (wpP s) ++ HighBankBarrel.stage 1613 (bankW s) controlsP1 2 (wpP s + 1) ++
    HighBankBarrel.stage 1613 (bankW s) controlsP2 4 (wpP s + 3) ++ HighBankBarrel.stage 1613 (bankW s) controlsP3 8 (wpP s + 7) := by
  simp only [leaveBarrel, forward_app, forward_stageG]
/-- Segment 9 is `digitPass ++ wordPass` at the parametric columns. -/
theorem forward_leaveJoin (s : Nat) : GateMirror.forward (leaveJoin s) =
    HighBankJoin.digits (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16 ++ HighBankJoin.word 1614 (columnsP s) := by
  simp only [leaveJoin, forward_app, forward_digitsG, forward_wordG]

end ECDSAAdd.Entrant.StairPacket.Partial

end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Window geometry and physical gates of enter/park (generic) and of the window's two portals (90, 405;
one small decide each). Leave physical: par-c1. -/

/-! Geometry facts on the window (ticks 90..405). -/

theorem rail_facts (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) :
    sbP s + 47 ≤ railP s ∧ railP s ≤ 258 ∧ sbP s = (513 - s)/2 ∧ (s ≤ 255 ∨ railP s = 513 - s) := by
  unfold railP sbP; split_ifs <;> omega
theorem rail_mono (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 390) : railP (s+15) ≤ railP s := by
  unfold railP; split_ifs <;> omega
theorem physical_of_proper (ops : List Gate) (h : ∀ g ∈ ops, proper g = true) :
    GatePhysical (GateMirror.forward ops) ∧ GatePhysical (inverse ops) := by
  constructor <;> apply physicalGateCheck_correct <;> rw [List.all_eq_true] <;> intro i hi
  · simp only [GateMirror.forward, List.mem_map] at hi
    obtain ⟨g, hg, rfl⟩ := hi
    have hp := h g hg
    cases g <;> simp_all [front, erase, physicalGateCheck, proper]
  · simp only [inverse, List.mem_reverse, List.mem_map] at hi
    obtain ⟨g, hg, rfl⟩ := hi
    have hp := h g hg
    cases g <;> simp_all [back, erase, physicalGateCheck, proper]

theorem enter_proper (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) : ∀ g ∈ enterOps s, proper g = true := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix
  simp only [List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)
theorem enterP_physical (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 22) :
    GatePhysical (enterP j) ∧ GatePhysical (enterInvP j) :=
  physical_of_proper _ (enter_proper (start j) (by simp [start]; omega) (by simp [start]; omega))
theorem park_proper (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) : ∀ g ∈ parkOps e, proper g = true := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts e h0 h1
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  unfold parkOps swapsG swapG
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)
theorem parkP_physical (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) :
    GatePhysical (parkP e) ∧ GatePhysical (parkInvP e) :=
  physical_of_proper _ (park_proper e h0 h1)
theorem portal_proper90 : (portalOps 90).all proper = true := by decide +kernel
theorem portal_proper405 : (portalOps 405).all proper = true := by decide +kernel
theorem portalP_physical90 : GatePhysical (portalP 90) ∧ GatePhysical (portalInvP 90) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper90)
theorem portalP_physical405 : GatePhysical (portalP 405) ∧ GatePhysical (portalInvP 405) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper405)

end ECDSAAdd.Entrant.StairPacket.Partial

end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror Challenge Baselines MappedCompressed StairArchiveGates
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem moves_counts (t f : Nat) :
    toffoliCount (moveLoadP t) = 0 ∧ measurementCount (moveLoadP t) = 0 ∧ gateSlots (moveLoadP t) = 33 ∧
    toffoliCount (moveRestoreP t f) = 0 ∧ measurementCount (moveRestoreP t f) = 0 ∧
    gateSlots (moveRestoreP t f) = 54 := by
  obtain ⟨a1,-,a3,-,a5,-⟩ := (counts_swapsG (moveLoadPairs t)).programs
  obtain ⟨b1,-,b3,-,b5,-⟩ := (counts_swapsG (moveRestorePairs t f)).programs
  exact ⟨a1, a3, a5, b1, b3, b5⟩
theorem moves240_counts :
    toffoliCount moveLoad240 = 0 ∧ measurementCount moveLoad240 = 0 ∧ gateSlots moveLoad240 = 33 ∧
    toffoliCount moveRestore240 = 0 ∧ measurementCount moveRestore240 = 0 ∧ gateSlots moveRestore240 = 54 := by
  decide +kernel
/-- Every archive piece costs what dadon's archive at 240 costs (same codec program, renamed; same move counts). -/
theorem archive_counts (j : Fin 23) (e : Nat) (d : Bool) :
    toffoliCount (archiveLoadP j d) = toffoliCount (archiveLoad240 d) ∧
    measurementCount (archiveLoadP j d) = measurementCount (archiveLoad240 d) ∧
    gateSlots (archiveLoadP j d) = gateSlots (archiveLoad240 d) ∧
    toffoliCount (archiveRestoreP j d) = toffoliCount (archiveRestore240 d) ∧
    measurementCount (archiveRestoreP j d) = measurementCount (archiveRestore240 d) ∧
    gateSlots (archiveRestoreP j d) = gateSlots (archiveRestore240 d) ∧
    toffoliCount (exitLoadP e d) = toffoliCount (archiveLoad240 d) ∧
    measurementCount (exitLoadP e d) = measurementCount (archiveLoad240 d) ∧
    gateSlots (exitLoadP e d) = gateSlots (archiveLoad240 d) ∧
    toffoliCount (exitRestoreP e d) = toffoliCount (archiveRestore240 d) ∧
    measurementCount (exitRestoreP e d) = measurementCount (archiveRestore240 d) ∧
    gateSlots (exitRestoreP e d) = gateSlots (archiveRestore240 d) := by
  have r1 : ∀ (f : Wire → Wire) (p : Program), toffoliCount (renameProgram f p) = toffoliCount p :=
    fun f p => (renameProgram_counts f p).1
  have r2 : ∀ (f : Wire → Wire) (p : Program), measurementCount (renameProgram f p) = measurementCount p :=
    fun f p => (renameProgram_counts f p).2
  obtain ⟨l1,l2,l3,l4,l5,l6⟩ := moves_counts (start j + 15) (e0P (start j + 15) + 6)
  obtain ⟨k1,k2,k3,k4,k5,k6⟩ := moves_counts e (bTopP e + 1)
  obtain ⟨m1,m2,m3,m4,m5,m6⟩ := moves240_counts
  simp only [archiveLoadP, archiveRestoreP, exitLoadP, exitRestoreP, archiveLoad240, archiveRestore240,
    toffoliCount_append, measurementCount_append, gateSlots_append, r1, r2, rename_gateSlots,
    l1, l2, l3, l4, l5, l6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, and_self]

end ECDSAAdd.Entrant.StairPacket.Partial

end

-- ==== w4: par-c1 HBJ appendix (a1dfeeb: generic Mirror, Foot, Fresh, Proper, Box, batch 1) ====

/-! par-c1 (Job C1): generic leave Mirror. Footprints (Gate.controls/wires, AllAT/AllW, NoMake), freshness by zero sets
(Safe), proper, the fixed-segment bitChecks over j in [1,21], and `Partial.leave_inverts` (replaces the per-block
`Leave{s}Mirror.inverts`). Sits after par-b's Partial sections; needs dadon's GateMirror lemma sections (moved from Roundtrip8ad0 to
PrizeHighBankJoin right after the GateMirror core). -/

section
namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def Gate.wires : Gate → List Wire
  | .x t => [t] | .cx a t => [a,t] | .ccx a b t => [a,b,t] | .make a b t => [a,b,t] | .pop a b t => [a,b,t]
end ECDSAAdd.Entrant.StairPacket.GateMirror
end



/-! par-c1: gate footprints of the parametric leave. `AllAT A T gs`: every control of every gate satisfies
`A` and every target satisfies `T`; `AllW P` (all operands satisfy `P`) is `AllAT P P`. `NoMake gs`: no gate
of `gs` is a `make`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def Gate.controls : Gate → List Wire
  | .x _ => [] | .cx a _ => [a] | .ccx a b _ => [a,b] | .make a b _ => [a,b] | .pop a b _ => [a,b]
theorem Gate.wires_eq (g : Gate) : g.wires = g.controls ++ [target g] := by cases g <;> rfl
end ECDSAAdd.Entrant.StairPacket.GateMirror

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def AllAT (A T : Wire → Prop) (gs : List Gate) : Prop := ∀ g ∈ gs, (∀ q ∈ g.controls, A q) ∧ T (target g)
/-- Every operand of every gate of `gs` satisfies `P`. -/
def AllW (P : Wire → Prop) (gs : List Gate) : Prop := ∀ g ∈ gs, ∀ q ∈ g.wires, P q
def NoMake (gs : List Gate) : Prop := ∀ g ∈ gs, NeedsZero g = false

theorem allW_of_allAT {P : Wire → Prop} {gs : List Gate} (h : AllAT P P gs) : AllW P gs := by
  intro g hg q hq
  rw [Gate.wires_eq, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq|rfl
  exacts [(h g hg).1 q hq, (h g hg).2]

theorem allAT_nil {A T : Wire → Prop} : AllAT A T [] := by intro g hg; cases hg
theorem allAT_append {A T : Wire → Prop} {a b : List Gate} (ha : AllAT A T a) (hb : AllAT A T b) :
    AllAT A T (a ++ b) := by
  intro g hg; rcases List.mem_append.mp hg with h|h
  exacts [ha g h, hb g h]
theorem allAT_cons {A T : Wire → Prop} {g : Gate} {gs : List Gate} (hg : (∀ q ∈ g.controls, A q) ∧ T (target g))
    (hs : AllAT A T gs) : AllAT A T (g :: gs) := by
  intro k hk; rcases List.mem_cons.mp hk with rfl|h
  exacts [hg, hs k h]
theorem allAT_mono {A T A' T' : Wire → Prop} (ha : ∀ q, A q → A' q) (ht : ∀ q, T q → T' q) {gs : List Gate}
    (h : AllAT A T gs) : AllAT A' T' gs :=
  fun g hg => ⟨fun q hq => ha q ((h g hg).1 q hq), ht _ (h g hg).2⟩
theorem allAT_flatMap {α} {A T : Wire → Prop} (f : α → List Gate) (xs : List α) (h : ∀ x ∈ xs, AllAT A T (f x)) :
    AllAT A T (xs.flatMap f) := by
  intro g hg; obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg; exact h x hx g hgx
theorem allAT_map {α} {A T : Wire → Prop} (f : α → Gate) (xs : List α)
    (h : ∀ x ∈ xs, (∀ q ∈ (f x).controls, A q) ∧ T (target (f x))) : AllAT A T (xs.map f) := by
  intro g hg; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg; exact h x hx

theorem noMake_nil : NoMake [] := by intro g hg; cases hg
theorem noMake_append {a b : List Gate} (ha : NoMake a) (hb : NoMake b) : NoMake (a ++ b) := by
  intro g hg; rcases List.mem_append.mp hg with h|h
  exacts [ha g h, hb g h]
theorem noMake_flatMap {α} (f : α → List Gate) (xs : List α) (h : ∀ x ∈ xs, NoMake (f x)) : NoMake (xs.flatMap f) := by
  intro g hg; obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg; exact h x hx g hgx
theorem noMake_map {α} (f : α → Gate) (xs : List α) (h : ∀ x ∈ xs, NeedsZero (f x) = false) : NoMake (xs.map f) := by
  intro g hg; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg; exact h x hx


theorem ok_x {A T : Wire → Prop} {t : Wire} (ht : T t) : (∀ q ∈ (Gate.x t).controls, A q) ∧ T (target (.x t)) :=
  ⟨fun q hq => by simp [Gate.controls] at hq, ht⟩
theorem ok_cx {A T : Wire → Prop} {a t : Wire} (ha : A a) (ht : T t) :
    (∀ q ∈ (Gate.cx a t).controls, A q) ∧ T (target (.cx a t)) :=
  ⟨fun q hq => by simp only [Gate.controls, List.mem_singleton] at hq; exact hq ▸ ha, ht⟩
theorem ok_ccx {A T : Wire → Prop} {a b t : Wire} (ha : A a) (hb : A b) (ht : T t) :
    (∀ q ∈ (Gate.ccx a b t).controls, A q) ∧ T (target (.ccx a b t)) :=
  ⟨fun q hq => by simp only [Gate.controls, List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl|rfl <;> assumption, ht⟩
theorem ok_make {A T : Wire → Prop} {a b t : Wire} (ha : A a) (hb : A b) (ht : T t) :
    (∀ q ∈ (Gate.make a b t).controls, A q) ∧ T (target (.make a b t)) :=
  ⟨fun q hq => by simp only [Gate.controls, List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl|rfl <;> assumption, ht⟩
theorem ok_pop {A T : Wire → Prop} {a b t : Wire} (ha : A a) (hb : A b) (ht : T t) :
    (∀ q ∈ (Gate.pop a b t).controls, A q) ∧ T (target (.pop a b t)) :=
  ⟨fun q hq => by simp only [Gate.controls, List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl|rfl <;> assumption, ht⟩

/-! Gadgets. Hypothesis convention: a wire used only as a control needs `A`; a wire that is ever a target
needs `A q ∧ T q`. -/

theorem allAT_cxsG {A T : Wire → Prop} (q : Wire) (xs : List Wire) (hq : A q) (hx : ∀ x ∈ xs, T x) :
    AllAT A T (cxsG q xs) :=
  allAT_map _ _ (fun x h => ok_cx hq (hx x h))
theorem allAT_xsG {A T : Wire → Prop} (xs : List Wire) (hx : ∀ x ∈ xs, T x) : AllAT A T (xsG xs) :=
  allAT_map _ _ (fun x h => ok_x (hx x h))
theorem allAT_togglesG {A T : Wire → Prop} (c : Wire) (xs : List Wire) (hc : T c) (hx : ∀ x ∈ xs, A x) :
    AllAT A T (togglesG c xs) :=
  allAT_map _ _ (fun x h => ok_cx (hx x h) hc)

theorem allAT_addG {A T : Wire → Prop} : ∀ (ys cs : List Wire) (cin : Wire), (∀ y ∈ ys, A y ∧ T y) →
    (∀ c ∈ cs, A c ∧ T c) → A cin → AllAT A T (addG ys cs cin)
  | y::y'::ys, c::cs, cin, hy, hc, hi => by
    have hy0 := hy y (by simp); have hc0 := hc c (by simp)
    have rest := allAT_addG (y'::ys) cs c (fun q h => hy q (List.mem_cons_of_mem _ h)) (fun q h => hc q (List.mem_cons_of_mem _ h)) hc0.1
    exact allAT_cons (ok_make hy0.1 hi hc0.2) (allAT_append rest (allAT_cons (ok_pop hy0.1 hi hc0.2)
      (allAT_cons (ok_cx hi hy0.2) allAT_nil)))
  | [y], cs, cin, hy, hc, hi => by
    exact allAT_cons (ok_cx hi (hy y (by simp)).2) allAT_nil
  | [], _, _, _, _, _ => by simp only [addG]; exact allAT_nil
  | _::_::_, [], _, _, _, _ => by simp only [addG]; exact allAT_nil

theorem allAT_adjustG {A T : Wire → Prop} (ys cs : List Wire) (cin neg : Wire) (hy : ∀ y ∈ ys, A y ∧ T y)
    (hc : ∀ c ∈ cs, A c ∧ T c) (hi : A cin) (hn : A neg) : AllAT A T (adjustG ys cs cin neg) :=
  allAT_append (allAT_cxsG _ _ hn (fun y h => (hy y h).2))
    (allAT_append (allAT_addG _ _ _ hy hc hi) (allAT_cxsG _ _ hn (fun y h => (hy y h).2)))

theorem allAT_cswapG {A T : Wire → Prop} (c a b : Wire) (hc : A c) (ha : A a ∧ T a) (hb : A b ∧ T b) :
    AllAT A T (cswapG c a b) := by
  exact allAT_cons (ok_cx hb.1 ha.2) (allAT_cons (ok_ccx hc ha.1 hb.2) (allAT_cons (ok_cx hb.1 ha.2) allAT_nil))

theorem allAT_shiftG {A T : Wire → Prop} (c : Wire) (w : Nat → Wire) (d : Nat) (hc : A c) :
    ∀ n, (∀ i, i < n → (A (w i) ∧ T (w i)) ∧ (A (w (i+d)) ∧ T (w (i+d)))) → AllAT A T (shiftG c w d n)
  | 0, _ => allAT_nil
  | n+1, h => allAT_append (allAT_cswapG _ _ _ hc (h n (by omega)).2 (h n (by omega)).1)
      (allAT_shiftG c w d hc n (fun i hi => h i (by omega)))

theorem allAT_stageG {A T : Wire → Prop} (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) (hc : A c ∧ T c)
    (hx : ∀ x ∈ xs, A x) (hw : ∀ i, i < n → (A (w i) ∧ T (w i)) ∧ (A (w (i+d)) ∧ T (w (i+d)))) :
    AllAT A T (stageG c w xs d n) :=
  allAT_append (allAT_togglesG _ _ hc.2 hx) (allAT_append (allAT_shiftG _ _ _ hc.1 _ hw) (allAT_togglesG _ _ hc.2 hx))

theorem allAT_digitsG {A T : Wire → Prop} (hot bank : Nat → Wire) (c d : Nat) (hc : A c) (hd : A d) :
    ∀ start n, (∀ i, start ≤ i → i < start + n → A (hot i) ∧ T (bank i) ∧ T (bank (i+1))) →
      AllAT A T (digitsG hot bank c d start n)
  | _, 0, _ => allAT_nil
  | start, n+1, h => by
    have h0 := h start (Nat.le_refl _) (by omega)
    refine allAT_append ?_ (allAT_digitsG hot bank c d hc hd (start+1) n (fun i h1 h2 => h i (by omega) (by omega)))
    exact allAT_cons (ok_ccx h0.1 hc h0.2.1) (allAT_cons (ok_ccx h0.1 hd h0.2.2) allAT_nil)

theorem allAT_pairG {A T : Wire → Prop} (low : Bool) (a s t : Wire) (ha : A a) (hs : A s ∧ T s) (ht : A t ∧ T t) :
    AllAT A T (pairG low a s t) := by
  cases low
  · exact allAT_cons (ok_cx hs.1 ht.2) (allAT_cons (ok_cx ht.1 hs.2) (allAT_cons (ok_ccx ha ht.1 hs.2) allAT_nil))
  · exact allAT_cons (ok_cx ht.1 hs.2) (allAT_cons (ok_ccx ha hs.1 ht.2) allAT_nil)

theorem allAT_toggleG {A T : Wire → Prop} (a : Wire) (o : Option Wire) (ha : T a) (ho : ∀ w, o = some w → A w) :
    AllAT A T (toggleG a o) := by
  cases o with
  | none => exact allAT_nil
  | some w =>
    exact allAT_cons (ok_cx (ho _ rfl) ha) allAT_nil

theorem allAT_wordG {A T : Wire → Prop} (a : Wire) (ha : A a ∧ T a) : ∀ rows : List HighBankJoin.Column,
    (∀ r ∈ rows, (∀ w, r.hot = some w → A w) ∧ (A r.shadow ∧ T r.shadow) ∧ (A r.tube ∧ T r.tube)) →
      AllAT A T (wordG a rows)
  | [], _ => allAT_nil
  | r::rs, h => by
    have h0 := h r (by simp)
    exact allAT_append (allAT_toggleG _ _ ha.2 h0.1) (allAT_append (allAT_pairG _ _ _ _ ha.1 h0.2.1 h0.2.2)
      (allAT_append (allAT_wordG a ha rs (fun x hx => h x (List.mem_cons_of_mem _ hx))) (allAT_toggleG _ _ ha.2 h0.1)))

theorem allAT_chainG {A T : Wire → Prop} (c seq : Nat → Wire) (body : List Gate) (hb : AllAT A T body) :
    ∀ i n, (∀ k, i ≤ k → k ≤ i + n → A (c k) ∧ (i < k → T (c k))) → (∀ k, i ≤ k → k < i + n → A (seq k)) →
      AllAT A T (chainG c seq body i n)
  | _, 0, _, _ => hb
  | i, n+1, hc, hs => by
    have c0 := hc i (Nat.le_refl _) (by omega); have c1 := hc (i+1) (by omega) (by omega)
    have s0 := hs i (Nat.le_refl _) (by omega)
    have t1 := c1.2 (by omega)
    refine allAT_cons ?_ (allAT_append (allAT_chainG c seq body hb (i+1) n
      (fun k h1 h2 => ⟨(hc k (by omega) (by omega)).1, fun _ => (hc k (by omega) (by omega)).2 (by omega)⟩)
      (fun k h1 h2 => hs k (by omega) (by omega))) (allAT_cons (ok_pop c0.1 s0 t1) allAT_nil))
    exact ok_make c0.1 s0 t1
termination_by _ n => n

theorem allAT_eventsG {A T : Wire → Prop} : ∀ (a out : Wire) (ps : List (Wire × Wire)), A a → T out →
    (∀ p ∈ ps, (A p.1 ∧ T p.1) ∧ (A p.2 ∧ T p.2)) → AllAT A T (eventsG a out ps)
  | a, out, [], ha, ho, _ => allAT_cons (ok_cx ha ho) allAT_nil
  | a, out, (x,t)::ps, ha, ho, hp => by
    have h0 := hp (x,t) (by simp)
    have rest := allAT_eventsG t out ps h0.2.1 ho (fun p h => hp p (List.mem_cons_of_mem _ h))
    obtain ⟨hx, ht⟩ := h0
    exact allAT_append (allAT_cons (ok_x hx.2) (allAT_cons (ok_make ha hx.1 ht.2) allAT_nil))
      (allAT_append rest (allAT_cons (ok_pop ha hx.1 ht.2) (allAT_cons (ok_x hx.2) allAT_nil)))

theorem allAT_swapsG {A T : Wire → Prop} (ps : List (Wire × Wire)) (hp : ∀ p ∈ ps, (A p.1 ∧ T p.1) ∧ (A p.2 ∧ T p.2)) :
    AllAT A T (swapsG ps) := by
  refine allAT_flatMap _ _ (fun p h => ?_)
  obtain ⟨h1, h2⟩ := hp p h
  exact allAT_cons (ok_cx h1.1 h2.2) (allAT_cons (ok_cx h2.1 h1.2) (allAT_cons (ok_cx h1.1 h2.2) allAT_nil))

/-! The all-operand API `AllW` (used by par-b's footprints). -/

theorem allW_nil {P : Wire → Prop} : AllW P [] := by intro g hg; cases hg
theorem allW_append {P : Wire → Prop} {a b : List Gate} (ha : AllW P a) (hb : AllW P b) :
    AllW P (a ++ b) := by
  intro g hg; rcases List.mem_append.mp hg with h|h
  exacts [ha g h, hb g h]
theorem allW_cons {P : Wire → Prop} {g : Gate} {gs : List Gate} (hg : ∀ q ∈ g.wires, P q)
    (hs : AllW P gs) : AllW P (g :: gs) := by
  intro k hk; rcases List.mem_cons.mp hk with rfl|h
  exacts [hg, hs k h]
theorem allW_append_iff {P : Wire → Prop} {a b : List Gate} : AllW P (a ++ b) ↔ AllW P a ∧ AllW P b :=
  ⟨fun h => ⟨fun g hg => h g (List.mem_append_left _ hg), fun g hg => h g (List.mem_append_right _ hg)⟩,
   fun h => allW_append h.1 h.2⟩
theorem allW_mono {P Q : Wire → Prop} (pq : ∀ q, P q → Q q) {gs : List Gate} (h : AllW P gs) : AllW Q gs :=
  fun g hg q hq => pq q (h g hg q hq)
theorem allW_flatMap {α} {P : Wire → Prop} (f : α → List Gate) (xs : List α) (h : ∀ x ∈ xs, AllW P (f x)) :
    AllW P (xs.flatMap f) := by
  intro g hg; obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg; exact h x hx g hgx
theorem allW_map {α} {P : Wire → Prop} (f : α → Gate) (xs : List α) (h : ∀ x ∈ xs, ∀ q ∈ (f x).wires, P q) :
    AllW P (xs.map f) := by
  intro g hg; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg; exact h x hx

theorem allW_cxsG {P : Wire → Prop} (q : Wire) (xs : List Wire) (hq : P q) (hx : ∀ x ∈ xs, P x) :
    AllW P (cxsG q xs) := allW_of_allAT (allAT_cxsG q xs hq hx)
theorem allW_xsG {P : Wire → Prop} (xs : List Wire) (hx : ∀ x ∈ xs, P x) : AllW P (xsG xs) :=
  allW_of_allAT (allAT_xsG xs hx)
theorem allW_togglesG {P : Wire → Prop} (c : Wire) (xs : List Wire) (hc : P c) (hx : ∀ x ∈ xs, P x) :
    AllW P (togglesG c xs) := allW_of_allAT (allAT_togglesG c xs hc hx)
theorem allW_addG {P : Wire → Prop} (ys cs : List Wire) (cin : Wire) (hy : ∀ y ∈ ys, P y) (hc : ∀ c ∈ cs, P c)
    (hi : P cin) : AllW P (addG ys cs cin) :=
  allW_of_allAT (allAT_addG ys cs cin (fun y h => ⟨hy y h, hy y h⟩) (fun c h => ⟨hc c h, hc c h⟩) hi)
theorem allW_adjustG {P : Wire → Prop} (ys cs : List Wire) (cin neg : Wire) (hy : ∀ y ∈ ys, P y)
    (hc : ∀ c ∈ cs, P c) (hi : P cin) (hn : P neg) : AllW P (adjustG ys cs cin neg) :=
  allW_of_allAT (allAT_adjustG ys cs cin neg (fun y h => ⟨hy y h, hy y h⟩) (fun c h => ⟨hc c h, hc c h⟩) hi hn)
theorem allW_cswapG {P : Wire → Prop} (c a b : Wire) (hc : P c) (ha : P a) (hb : P b) : AllW P (cswapG c a b) :=
  allW_of_allAT (allAT_cswapG c a b hc ⟨ha, ha⟩ ⟨hb, hb⟩)
theorem allW_shiftG {P : Wire → Prop} (c : Wire) (w : Nat → Wire) (d : Nat) (hc : P c) (n : Nat)
    (h : ∀ i, i < n → P (w i) ∧ P (w (i+d))) : AllW P (shiftG c w d n) :=
  allW_of_allAT (allAT_shiftG c w d hc n (fun i hi => ⟨⟨(h i hi).1, (h i hi).1⟩, ⟨(h i hi).2, (h i hi).2⟩⟩))
theorem allW_stageG {P : Wire → Prop} (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) (hc : P c)
    (hx : ∀ x ∈ xs, P x) (hw : ∀ i, i < n → P (w i) ∧ P (w (i+d))) : AllW P (stageG c w xs d n) :=
  allW_of_allAT (allAT_stageG c w xs d n ⟨hc, hc⟩ hx (fun i hi => ⟨⟨(hw i hi).1, (hw i hi).1⟩, ⟨(hw i hi).2, (hw i hi).2⟩⟩))
theorem allW_digitsG {P : Wire → Prop} (hot bank : Nat → Wire) (c d : Nat) (hc : P c) (hd : P d) (start n : Nat)
    (h : ∀ i, start ≤ i → i < start + n → P (hot i) ∧ P (bank i) ∧ P (bank (i+1))) :
    AllW P (digitsG hot bank c d start n) :=
  allW_of_allAT (allAT_digitsG hot bank c d hc hd start n h)
theorem allW_pairG {P : Wire → Prop} (low : Bool) (a s t : Wire) (ha : P a) (hs : P s) (ht : P t) :
    AllW P (pairG low a s t) := allW_of_allAT (allAT_pairG low a s t ha ⟨hs, hs⟩ ⟨ht, ht⟩)
theorem allW_toggleG {P : Wire → Prop} (a : Wire) (o : Option Wire) (ha : P a) (ho : ∀ w, o = some w → P w) :
    AllW P (toggleG a o) := allW_of_allAT (allAT_toggleG a o ha ho)
theorem allW_wordG {P : Wire → Prop} (a : Wire) (ha : P a) (rows : List HighBankJoin.Column)
    (h : ∀ r ∈ rows, (∀ w, r.hot = some w → P w) ∧ P r.shadow ∧ P r.tube) : AllW P (wordG a rows) :=
  allW_of_allAT (allAT_wordG a ⟨ha, ha⟩ rows (fun r hr => ⟨(h r hr).1, ⟨(h r hr).2.1, (h r hr).2.1⟩, ⟨(h r hr).2.2, (h r hr).2.2⟩⟩))
theorem allW_chainG {P : Wire → Prop} (c seq : Nat → Wire) (body : List Gate) (hb : AllW P body) (i n : Nat)
    (hc : ∀ k, i ≤ k → k ≤ i + n → P (c k)) (hs : ∀ k, i ≤ k → k < i + n → P (seq k)) :
    AllW P (chainG c seq body i n) := by
  intro g hg
  have hb' : AllAT P P body := fun k hk => ⟨fun q hq => hb k hk q (by rw [Gate.wires_eq]; exact List.mem_append_left _ hq),
    hb k hk _ (by rw [Gate.wires_eq]; exact List.mem_append_right _ (List.mem_singleton_self _))⟩
  exact allW_of_allAT (allAT_chainG c seq body hb' i n (fun k h1 h2 => ⟨hc k h1 h2, fun _ => hc k h1 h2⟩) hs) g hg
theorem allW_eventsG {P : Wire → Prop} (a out : Wire) (ps : List (Wire × Wire)) (ha : P a) (ho : P out)
    (hp : ∀ p ∈ ps, P p.1 ∧ P p.2) : AllW P (eventsG a out ps) :=
  allW_of_allAT (allAT_eventsG a out ps ha ho (fun p h => ⟨⟨(hp p h).1, (hp p h).1⟩, ⟨(hp p h).2, (hp p h).2⟩⟩))
theorem allW_swapsG {P : Wire → Prop} (ps : List (Wire × Wire)) (hp : ∀ p ∈ ps, P p.1 ∧ P p.2) :
    AllW P (swapsG ps) :=
  allW_of_allAT (allAT_swapsG ps (fun p h => ⟨⟨(hp p h).1, (hp p h).1⟩, ⟨(hp p h).2, (hp p h).2⟩⟩))

/-! No `make` in the frame gadgets. -/

theorem noMake_cxsG (q : Wire) (xs : List Wire) : NoMake (cxsG q xs) := noMake_map _ _ (fun _ _ => rfl)
theorem noMake_xsG (xs : List Wire) : NoMake (xsG xs) := noMake_map _ _ (fun _ _ => rfl)
theorem noMake_togglesG (c : Wire) (xs : List Wire) : NoMake (togglesG c xs) := noMake_map _ _ (fun _ _ => rfl)
theorem noMake_cswapG (c a b : Wire) : NoMake (cswapG c a b) := by
  intro g hg; simp only [cswapG, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl|rfl|rfl <;> rfl
theorem noMake_shiftG (c : Wire) (w : Nat → Wire) (d : Nat) : ∀ n, NoMake (shiftG c w d n)
  | 0 => noMake_nil
  | n+1 => noMake_append (noMake_cswapG _ _ _) (noMake_shiftG c w d n)
theorem noMake_stageG (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) : NoMake (stageG c w xs d n) :=
  noMake_append (noMake_togglesG _ _) (noMake_append (noMake_shiftG _ _ _ _) (noMake_togglesG _ _))
theorem noMake_digitsG (hot bank : Nat → Wire) (c d : Nat) : ∀ start n, NoMake (digitsG hot bank c d start n)
  | _, 0 => noMake_nil
  | start, n+1 => noMake_append (by intro g hg; simp only [clearG, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl|rfl <;> rfl)
      (noMake_digitsG hot bank c d (start+1) n)
theorem noMake_pairG (low : Bool) (a s t : Wire) : NoMake (pairG low a s t) := by
  intro g hg; cases low <;> simp only [pairG, List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true, if_false, if_true] at hg <;>
    rcases hg with rfl|rfl|rfl <;> rfl
theorem noMake_toggleG (a : Wire) (o : Option Wire) : NoMake (toggleG a o) := by
  cases o with
  | none => exact noMake_nil
  | some w => intro g hg; simp only [toggleG, List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; rfl
theorem noMake_wordG (a : Wire) : ∀ rows : List HighBankJoin.Column, NoMake (wordG a rows)
  | [] => noMake_nil
  | _::rs => noMake_append (noMake_toggleG _ _) (noMake_append (noMake_pairG _ _ _ _)
      (noMake_append (noMake_wordG a rs) (noMake_toggleG _ _)))
theorem noMake_swapsG (ps : List (Wire × Wire)) : NoMake (swapsG ps) :=
  noMake_flatMap _ _ (fun p _ => by intro g hg; simp only [swapG, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl|rfl|rfl <;> rfl)

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: freshness of `make` targets along a mirror-op list (the `Ready` premise of `GateMirror.invert`),
tracked through zero sets: `Safe gs Z Z'` says that from any state zero on `Z`, every `make` of `gs` finds its
target zero and the end state (run on the empty tape) is zero on `Z'`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def ZeroOn (s : State) (Z : Wire → Prop) : Prop := ∀ q, Z q → s.basis q = false

def Safe (gs : List Gate) (Z Z' : Wire → Prop) : Prop :=
  ∀ s, ZeroOn s Z → Ready s gs ∧ ZeroOn (run (GateMirror.forward gs) [] s) Z'

theorem transition_basis (g : Gate) (s : State) : ∃ v, (transition g s).basis = writeBit s.basis (target g) v := by
  cases g with
  | x t => exact ⟨_, rfl⟩
  | cx a t => exact ⟨_, rfl⟩
  | ccx a b t => exact ⟨_, rfl⟩
  | make a b t => exact ⟨_, rfl⟩
  | pop a b t => exact ⟨false, rfl⟩

theorem transition_ne (g : Gate) (s : State) (q : Wire) (h : q ≠ target g) :
    (transition g s).basis q = s.basis q := by
  obtain ⟨v, hv⟩ := transition_basis g s
  rw [hv]; unfold writeBit Function.update; rw [dif_neg h]

theorem transition_pop (a b t : Wire) (s : State) : (transition (.pop a b t) s).basis t = false := by
  show writeBit s.basis t false t = false
  unfold writeBit Function.update; rw [dif_pos rfl]

theorem run_forward_cons (g : Gate) (gs : List Gate) (s : State) :
    run (GateMirror.forward (g::gs)) [] s = run (GateMirror.forward gs) [] (transition g s) := by
  change run ([front g] ++ GateMirror.forward gs) [] s = _
  rw [run_append]; simp only [List.drop_nil, List.take_nil]; rfl

theorem run_forward_append (a b : List Gate) (s : State) :
    run (GateMirror.forward (a++b)) [] s = run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s) := by
  rw [fwAppend, run_append]; simp

theorem safe_nil {Z : Wire → Prop} : Safe [] Z Z := fun _ h => ⟨trivial, h⟩

theorem safe_mono {gs : List Gate} {Z Z' Y Y' : Wire → Prop} (h : Safe gs Z Z') (hy : ∀ q, Z q → Y q)
    (hy' : ∀ q, Y' q → Z' q) : Safe gs Y Y' :=
  fun s hs => let r := h s (fun q hq => hs q (hy q hq)); ⟨r.1, fun q hq => r.2 q (hy' q hq)⟩

theorem safe_append {a b : List Gate} {Z Z1 Z2 : Wire → Prop} (ha : Safe a Z Z1) (hb : Safe b Z1 Z2) :
    Safe (a++b) Z Z2 := by
  intro s hs
  obtain ⟨ra, za⟩ := ha s hs
  obtain ⟨rb, zb⟩ := hb _ za
  exact ⟨ready_append a b s ra rb, by rw [run_forward_append]; exact zb⟩

/-- Zero set after one gate: a `pop` zeroes its target, any other gate forgets it. -/
def stepZ (g : Gate) (Z : Wire → Prop) : Wire → Prop :=
  fun q => (WritesZero g = true ∧ q = target g) ∨ (q ≠ target g ∧ Z q)

theorem safe_cons {g : Gate} {gs : List Gate} {Z Z' : Wire → Prop} (hf : NeedsZero g = true → Z (target g))
    (hs : Safe gs (stepZ g Z) Z') : Safe (g::gs) Z Z' := by
  intro s hz
  have fr : Fresh s g := by
    cases g with
    | make a b t => exact hz _ (hf rfl)
    | _ => trivial
  have z1 : ZeroOn (transition g s) (stepZ g Z) := by
    intro q hq
    rcases hq with ⟨hw, rfl⟩ | ⟨hne, hq⟩
    · cases g <;> simp [WritesZero] at hw
      exact transition_pop _ _ _ _
    · rw [transition_ne g s q hne]; exact hz q hq
  obtain ⟨r, z⟩ := hs _ z1
  exact ⟨⟨fr, r⟩, by rw [run_forward_cons]; exact z⟩

/-- Frame: no `make`, and every target outside `Z` (or a `pop`). -/
theorem safe_frame {Z : Wire → Prop} : ∀ {gs : List Gate}, NoMake gs → (∀ g ∈ gs, WritesZero g = false → ¬ Z (target g)) →
    Safe gs Z Z
  | [], _, _ => safe_nil
  | g::gs, nm, ht => by
    refine safe_cons (fun h => by rw [nm g (by simp)] at h; cases h) (safe_mono (safe_frame (fun k hk => nm k (by simp [hk]))
      (fun k hk => ht k (by simp [hk]))) (fun q hq => ?_) (fun q h => h))
    by_cases hw : WritesZero g = true
    · by_cases e : q = target g
      · exact Or.inl ⟨hw, e⟩
      · exact Or.inr ⟨e, hq⟩
    · have hn := ht g (by simp) (by simpa using hw)
      exact Or.inr ⟨fun e => hn (e ▸ hq), hq⟩

theorem safe_frame' {Z : Wire → Prop} {gs : List Gate} (nm : NoMake gs) (ht : AllAT (fun _ => True) (fun q => ¬ Z q) gs) :
    Safe gs Z Z :=
  safe_frame nm (fun g hg _ => (ht g hg).2)

/-- One `make` whose target is in `Z`, then `Z` minus that target. -/
theorem safe_make {a b t : Wire} {Z : Wire → Prop} (h : Z t) : Safe [.make a b t] Z (fun q => q ≠ t ∧ Z q) :=
  safe_cons (fun _ => h) (safe_mono safe_nil (fun _ hq => hq) (fun _ hq => Or.inr hq))

theorem safe_pop {a b t : Wire} {Z : Wire → Prop} : Safe [.pop a b t] Z (fun q => q = t ∨ Z q) :=
  safe_cons (fun h => by cases h) (safe_mono safe_nil (fun q hq => hq) (fun q hq => by
    by_cases e : q = t
    · exact Or.inl ⟨rfl, e⟩
    · rcases hq with h'|h'
      · exact absurd h' e
      · exact Or.inr ⟨e, h'⟩))

theorem safe_single_frame {g : Gate} {Z : Wire → Prop} (hm : NeedsZero g = false) (ht : ¬ Z (target g)) : Safe [g] Z Z :=
  safe_frame (fun k hk => by simp at hk; subst hk; exact hm) (fun k hk _ => by simp at hk; subst hk; exact ht)

/-! Gadgets with `make`. -/

theorem safe_addG : ∀ (ys cs : List Wire) (cin : Wire) (Z : Wire → Prop),
    (∀ c ∈ cs, Z c) → cs.Nodup → (∀ y ∈ ys, ¬ Z y) → Safe (addG ys cs cin) Z Z
  | y::y'::ys, c::cs, cin, Z, hc, hn, hy => by
    have hcZ := hc c (by simp)
    have hc' : c ∉ cs := (List.nodup_cons.mp hn).1
    have inner := safe_addG (y'::ys) cs c (fun q => q ≠ c ∧ Z q)
      (fun q hq => ⟨fun e => hc' (e ▸ hq), hc q (by simp [hq])⟩) (List.nodup_cons.mp hn).2
      (fun q hq h => hy q (by simp [hq]) h.2)
    have hyZ := hy y (by simp)
    have hyc : y ≠ c := fun e => hyZ (e ▸ hcZ)
    show Safe ([.make y cin c] ++ (addG (y'::ys) cs c ++ ([.pop y cin c] ++ [.cx cin y]))) Z Z
    refine safe_append (safe_make hcZ) (safe_append inner (safe_append safe_pop
      (safe_mono (safe_single_frame rfl ?_) (fun q h => h) (fun q hq => ?_))))
    · rintro (h|h); exacts [hyc h, hyZ h.2]
    · by_cases e : q = c
      · exact Or.inl e
      · exact Or.inr ⟨e, hq⟩
  | [y], cs, cin, Z, _, _, hy => safe_single_frame rfl (hy y (by simp))
  | [], _, _, _, _, _, _ => by simp only [addG]; exact safe_nil
  | _::_::_, [], _, _, _, _, _ => by simp only [addG]; exact safe_nil

/-- The set left to the body of an AND chain: `Z` minus the chain carries `c (i+1) .. c (i+n)`. -/
def chainZ (c : Nat → Wire) (i n : Nat) (Z : Wire → Prop) : Wire → Prop :=
  fun q => Z q ∧ ∀ k, i < k → k ≤ i + n → q ≠ c k

theorem safe_chainG (c seq : Nat → Wire) (body : List Gate) : ∀ (i n : Nat) (Z : Wire → Prop),
    (∀ k, i < k → k ≤ i + n → Z (c k)) →
    (∀ k k', i < k → k ≤ i + n → i < k' → k' ≤ i + n → c k = c k' → k = k') →
    Safe body (chainZ c i n Z) (chainZ c i n Z) → Safe (chainG c seq body i n) Z Z
  | i, 0, Z, _, _, hb => safe_mono hb (fun q hq => hq.1) (fun q hq => ⟨hq, fun k h1 h2 => by omega⟩)
  | i, n+1, Z, hz, hinj, hb => by
    have h1 := hz (i+1) (by omega) (by omega)
    have inner := safe_chainG c seq body (i+1) n (fun q => q ≠ c (i+1) ∧ Z q)
      (fun k a b => ⟨fun e => by have := hinj k (i+1) (by omega) (by omega) (by omega) (by omega) e; omega,
        hz k (by omega) (by omega)⟩)
      (fun k k' a b a' b' e => hinj k k' (by omega) (by omega) (by omega) (by omega) e)
      (safe_mono hb (fun q hq => ⟨⟨hq.2 (i+1) (by omega) (by omega), hq.1⟩, fun k a b => hq.2 k (by omega) (by omega)⟩)
        (fun q hq => ⟨hq.1.2, fun k a b => by
          by_cases e : k = i+1
          · subst e; exact hq.1.1
          · exact hq.2 k (by omega) (by omega)⟩))
    show Safe ([.make (c i) (seq i) (c (i+1))] ++ (chainG c seq body (i+1) n ++ [.pop (c i) (seq i) (c (i+1))])) Z Z
    refine safe_append (safe_make h1) (safe_append inner (safe_mono safe_pop (fun q h => h) (fun q hq => ?_)))
    by_cases e : q = c (i+1)
    · exact Or.inl e
    · exact Or.inr ⟨e, hq⟩

theorem safe_eventsG : ∀ (a out : Wire) (ps : List (Wire × Wire)) (Z : Wire → Prop),
    (∀ p ∈ ps, ¬ Z p.1 ∧ Z p.2) → (ps.map Prod.snd).Nodup → ¬ Z out → Safe (eventsG a out ps) Z Z
  | a, out, [], Z, _, _, ho => safe_single_frame rfl ho
  | a, out, (x,t)::ps, Z, hp, hn, ho => by
    have h0 := hp (x,t) (by simp)
    have ht' : t ∉ ps.map Prod.snd := (List.nodup_cons.mp hn).1
    have inner := safe_eventsG t out ps (fun q => q ≠ t ∧ Z q)
      (fun p hp' => ⟨fun h => (hp p (by simp [hp'])).1 h.2, fun e => ht' (e ▸ List.mem_map_of_mem hp'),
        (hp p (by simp [hp'])).2⟩) (List.nodup_cons.mp hn).2 (fun h => ho h.2)
    have hxt : x ≠ t := fun e => h0.1 (e ▸ h0.2)
    show Safe ([.x x] ++ ([.make a x t] ++ (eventsG t out ps ++ ([.pop a x t] ++ [.x x])))) Z Z
    refine safe_append (safe_single_frame rfl h0.1) (safe_append (safe_make h0.2) (safe_append inner
      (safe_append safe_pop (safe_mono (safe_single_frame rfl ?_) (fun q h => h) (fun q hq => ?_)))))
    · rintro (h|h); exacts [hxt h, h0.1 h.2]
    · by_cases e : q = t
      · exact Or.inl e
      · exact Or.inr ⟨e, hq⟩

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: `proper` (no control equals its target) for every gate of the leave gadgets. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def Proper (gs : List Gate) : Prop := ∀ g ∈ gs, proper g = true

theorem proper_nil : Proper [] := by intro g hg; cases hg
theorem proper_append {a b : List Gate} (ha : Proper a) (hb : Proper b) : Proper (a ++ b) := by
  intro g hg; rcases List.mem_append.mp hg with h|h
  exacts [ha g h, hb g h]
theorem proper_cons {g : Gate} {gs : List Gate} (hg : proper g = true) (hs : Proper gs) : Proper (g :: gs) := by
  intro k hk; rcases List.mem_cons.mp hk with rfl|h
  exacts [hg, hs k h]
theorem proper_map {α} (f : α → Gate) (xs : List α) (h : ∀ x ∈ xs, proper (f x) = true) : Proper (xs.map f) := by
  intro g hg; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg; exact h x hx
theorem proper_flatMap {α} (f : α → List Gate) (xs : List α) (h : ∀ x ∈ xs, Proper (f x)) : Proper (xs.flatMap f) := by
  intro g hg; obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hg; exact h x hx g hgx

theorem pr_x (t : Wire) : proper (.x t) = true := rfl
theorem pr_cx {a t : Wire} (h : a ≠ t) : proper (.cx a t) = true := decide_eq_true h
theorem pr_ccx {a b t : Wire} (ha : a ≠ t) (hb : b ≠ t) : proper (.ccx a b t) = true := decide_eq_true ⟨ha, hb⟩
theorem pr_make {a b t : Wire} (ha : a ≠ t) (hb : b ≠ t) : proper (.make a b t) = true := decide_eq_true ⟨ha, hb⟩
theorem pr_pop {a b t : Wire} (ha : a ≠ t) (hb : b ≠ t) : proper (.pop a b t) = true := decide_eq_true ⟨ha, hb⟩

theorem proper_cxsG (q : Wire) (xs : List Wire) (h : ∀ x ∈ xs, q ≠ x) : Proper (cxsG q xs) :=
  proper_map _ _ (fun x hx => pr_cx (h x hx))
theorem proper_xsG (xs : List Wire) : Proper (xsG xs) := proper_map _ _ (fun _ _ => rfl)
theorem proper_togglesG (c : Wire) (xs : List Wire) (h : ∀ x ∈ xs, x ≠ c) : Proper (togglesG c xs) :=
  proper_map _ _ (fun x hx => pr_cx (h x hx))

theorem proper_addG : ∀ (ys cs : List Wire) (cin : Wire), (∀ y ∈ ys, y ∉ cs ∧ y ≠ cin) → cin ∉ cs → cs.Nodup →
    Proper (addG ys cs cin)
  | y::y'::ys, c::cs, cin, hy, hi, hn => by
    have hy0 := hy y (by simp)
    have hyc : y ≠ c := fun e => hy0.1 (by simp [e])
    have hic : cin ≠ c := fun e => hi (by simp [e])
    have inner := proper_addG (y'::ys) cs c (fun q hq => ⟨fun h => (hy q (by simp [hq])).1 (by simp [h]),
      fun e => (hy q (by simp [hq])).1 (by simp [e])⟩) (List.nodup_cons.mp hn).1 (List.nodup_cons.mp hn).2
    exact proper_cons (pr_make hyc hic) (proper_append inner (proper_cons (pr_pop hyc hic)
      (proper_cons (pr_cx (Ne.symm hy0.2)) proper_nil)))
  | [y], cs, cin, hy, _, _ => proper_cons (pr_cx (Ne.symm (hy y (by simp)).2)) proper_nil
  | [], _, _, _, _, _ => by simp only [addG]; exact proper_nil
  | _::_::_, [], _, _, _, _ => by simp only [addG]; exact proper_nil

theorem proper_adjustG (ys cs : List Wire) (cin neg : Wire) (hy : ∀ y ∈ ys, y ∉ cs ∧ y ≠ cin ∧ y ≠ neg)
    (hi : cin ∉ cs) (hn : cs.Nodup) : Proper (adjustG ys cs cin neg) :=
  proper_append (proper_cxsG _ _ (fun y h => Ne.symm (hy y h).2.2))
    (proper_append (proper_addG _ _ _ (fun y h => ⟨(hy y h).1, (hy y h).2.1⟩) hi hn)
      (proper_cxsG _ _ (fun y h => Ne.symm (hy y h).2.2)))

theorem proper_cswapG {c a b : Wire} (hab : a ≠ b) (hcb : c ≠ b) : Proper (cswapG c a b) :=
  proper_cons (pr_cx (Ne.symm hab)) (proper_cons (pr_ccx hcb hab) (proper_cons (pr_cx (Ne.symm hab)) proper_nil))

theorem proper_shiftG (c : Wire) (w : Nat → Wire) (d : Nat) :
    ∀ n, (∀ i, i < n → w (i+d) ≠ w i ∧ c ≠ w i) → Proper (shiftG c w d n)
  | 0, _ => proper_nil
  | n+1, h => proper_append (proper_cswapG (h n (by omega)).1 (h n (by omega)).2)
      (proper_shiftG c w d n (fun i hi => h i (by omega)))

theorem proper_stageG (c : Wire) (w : Nat → Wire) (xs : List Wire) (d n : Nat) (hx : ∀ x ∈ xs, x ≠ c)
    (hw : ∀ i, i < n → w (i+d) ≠ w i ∧ c ≠ w i) : Proper (stageG c w xs d n) :=
  proper_append (proper_togglesG _ _ hx) (proper_append (proper_shiftG _ _ _ _ hw) (proper_togglesG _ _ hx))

theorem proper_digitsG (hot bank : Nat → Wire) (c d : Nat) :
    ∀ start n, (∀ i, start ≤ i → i < start + n → hot i ≠ bank i ∧ c ≠ bank i ∧ hot i ≠ bank (i+1) ∧ d ≠ bank (i+1)) →
      Proper (digitsG hot bank c d start n)
  | _, 0, _ => proper_nil
  | start, n+1, h => by
    have h0 := h start (Nat.le_refl _) (by omega)
    exact proper_append (proper_cons (pr_ccx h0.1 h0.2.1) (proper_cons (pr_ccx h0.2.2.1 h0.2.2.2) proper_nil))
      (proper_digitsG hot bank c d (start+1) n (fun i h1 h2 => h i (by omega) (by omega)))

theorem proper_pairG (low : Bool) {a s t : Wire} (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t) :
    Proper (pairG low a s t) := by
  cases low
  · exact proper_cons (pr_cx hst) (proper_cons (pr_cx (Ne.symm hst)) (proper_cons (pr_ccx has (Ne.symm hst)) proper_nil))
  · exact proper_cons (pr_cx (Ne.symm hst)) (proper_cons (pr_ccx hat hst) proper_nil)

theorem proper_toggleG (a : Wire) (o : Option Wire) (h : ∀ w, o = some w → w ≠ a) : Proper (toggleG a o) := by
  cases o with
  | none => exact proper_nil
  | some w => exact proper_cons (pr_cx (h w rfl)) proper_nil

theorem proper_wordG (a : Wire) : ∀ rows : List HighBankJoin.Column,
    (∀ r ∈ rows, (∀ w, r.hot = some w → w ≠ a) ∧ a ≠ r.shadow ∧ a ≠ r.tube ∧ r.shadow ≠ r.tube) →
      Proper (wordG a rows)
  | [], _ => proper_nil
  | r::rs, h => by
    have h0 := h r (by simp)
    exact proper_append (proper_toggleG _ _ h0.1) (proper_append (proper_pairG _ h0.2.1 h0.2.2.1 h0.2.2.2)
      (proper_append (proper_wordG a rs (fun x hx => h x (List.mem_cons_of_mem _ hx))) (proper_toggleG _ _ h0.1)))

theorem proper_chainG (c seq : Nat → Wire) (body : List Gate) (hb : Proper body) :
    ∀ i n, (∀ k, i ≤ k → k < i + n → c k ≠ c (k+1) ∧ seq k ≠ c (k+1)) → Proper (chainG c seq body i n)
  | _, 0, _ => hb
  | i, n+1, h => by
    have h0 := h i (Nat.le_refl _) (by omega)
    exact proper_cons (pr_make h0.1 h0.2) (proper_append (proper_chainG c seq body hb (i+1) n
      (fun k h1 h2 => h k (by omega) (by omega))) (proper_cons (pr_pop h0.1 h0.2) proper_nil))
termination_by _ n => n

theorem proper_eventsG : ∀ (a out : Wire) (ps : List (Wire × Wire)),
    (∀ p ∈ ps, p.1 ≠ p.2) → (a :: ps.map Prod.snd).Nodup → (∀ p ∈ ps, p.2 ≠ out) → a ≠ out →
      Proper (eventsG a out ps)
  | a, out, [], _, _, _, ho => proper_cons (pr_cx ho) proper_nil
  | a, out, (x,t)::ps, hp, hn, hto, ho => by
    have hxt := hp (x,t) (by simp)
    have hat : a ≠ t := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
    have inner := proper_eventsG t out ps (fun p h => hp p (by simp [h])) (List.nodup_cons.mp hn).2
      (fun p h => hto p (by simp [h])) (hto (x,t) (by simp))
    exact proper_append (proper_cons rfl (proper_cons (pr_make hat hxt) proper_nil))
      (proper_append inner (proper_cons (pr_pop hat hxt) (proper_cons rfl proper_nil)))

theorem proper_swapsG (ps : List (Wire × Wire)) (h : ∀ p ∈ ps, p.1 ≠ p.2) : Proper (swapsG ps) :=
  proper_flatMap _ _ (fun p hp => proper_cons (pr_cx (h p hp)) (proper_cons (pr_cx (Ne.symm (h p hp)))
    (proper_cons (pr_cx (h p hp)) proper_nil)))

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: generic leave Mirror, part 1. The leave split at dadon's checkpoints and the zero masks of the
freshness chain. Fixed segments are checked by `bitCheck` (Fixed.lean); the far zero regions (scratch above 1597,
carry pool) are bits of the same masks. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Splits. `leaveHeadOps` ends after the low store's sign close (dadon's `core` checkpoint, cut 27);
`leaveMidOps` runs to the close (dadon's `post` checkpoint, cut 33). -/

def lowSign (s : Nat) : List Gate := [.cx (e0P s + 3) 1560, .cx 1559 1560, .pop (e0P s + 3) (e0P s + 4) 1559]
def lowRest (s : Nat) : List Gate :=
  (List.range (lowsP s)).map (fun i => .ccx 1556 (a0P s + i) (b0P s + i)) ++ xsG ((List.range (lowsP s)).map (b0P s + ·)) ++
  addG ((List.range (lowsP s)).map (b0P s + ·)) ((List.range (lowsP s - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (lowsP s)).map (b0P s + ·)) ++
  [.pop (b0P s - 1) 1557 1558, .cx (a0P s - 1) 1557, .x 1557]
theorem leaveLowStore_split (s : Nat) : leaveLowStore s = lowSign s ++ lowRest s := rfl

def leaveHeadOps (s : Nat) : List Gate :=
  leaveFix0 s (sbP s) ++ leaveFix1 s (sbP s) ++ leaveFix2 s (sbP s) ++ leaveFix3 s (sbP s) ++
  leaveFix4 s (sbP s) ++ leaveFix5 s (sbP s) ++ leaveAdjust s ++ leaveBarrel s ++
  leaveFix8 s (sbP s) ++ leaveJoin s ++ leaveFix10 s (sbP s) ++ leaveFix11 s (sbP s) ++
  leaveFix12 s (sbP s) ++ lowSign s
def leaveMidOps (s : Nat) : List Gate := lowRest s ++ leaveStoreMapped s ++ leaveLowClose s

theorem leaveOps_split (s : Nat) : leaveOps s = leaveHeadOps s ++ leaveMidOps s ++ leaveClose s := by
  simp only [leaveOps, leaveHeadOps, leaveMidOps, leaveLowStore_split, List.append_assoc]

/-! Masks. `Zm m q`: bit `q` of `m` is set. -/

def Zm (m : Nat) (q : Nat) : Prop := m.testBit q = true

theorem testBit_interval (lo w q : Nat) : (interval lo w).testBit q = true ↔ lo ≤ q ∧ q < lo + w := by
  simp only [interval, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq]
  ((try unfold Wire at *); omega)
theorem testBit_maskSites (ws : List Wire) (q : Nat) : (maskSites ws).testBit q = true ↔ q ∈ ws := by
  induction ws with
  | nil => simp [maskSites]
  | cons a as ih =>
    change (addBit (maskSites as) a).testBit q = true ↔ _
    rw [add_bit, Bool.or_eq_true, ih, decide_eq_true_iff, List.mem_cons]
theorem zm_or (a b : Nat) (q : Nat) : Zm (a ||| b) q ↔ Zm a q ∨ Zm b q := by
  unfold Zm; rw [Nat.testBit_or, Bool.or_eq_true]
theorem zm_sites (ws : List Wire) (q : Nat) : Zm (maskSites ws) q ↔ q ∈ ws := testBit_maskSites ws q

/-- Far zeros before the barrel: scratch `1598 .. e0-1` and the pool overflow `e0+10 ..`. -/
def far1M (s : Nat) : Nat := interval 1598 (e0P s - 1598) ||| interval (e0P s + 10) (wpP s - 1 - (e0P s - 1598))
/-- Far zeros from the barrel on: `1615 .. e0-1`. -/
def far2M (s : Nat) : Nat := interval 1615 (e0P s - 1615)

theorem far1_iff (s : Nat) (q : Nat) :
    Zm (far1M s) q ↔ (1598 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + (wpP s - 1 - (e0P s - 1598))) := by
  unfold far1M; rw [zm_or]; unfold Zm; rw [testBit_interval, testBit_interval]
  constructor <;> rintro (⟨a, b⟩|⟨a, b⟩) <;> first | (left; constructor <;> ((try unfold Wire at *); omega)) | (right; constructor <;> ((try unfold Wire at *); omega))
theorem far2_iff (s : Nat) (q : Nat) : Zm (far2M s) q ↔ 1615 ≤ q ∧ q < e0P s := by
  unfold far2M Zm; rw [testBit_interval]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> ((try unfold Wire at *); omega)

/-! Constant zero lists between the fixed segments (`checked` lists, identical at all blocks). -/

def cA : List Wire := List.range' 1561 15 ++ List.range' 1577 19 ++ [1597]
def cB : List Wire := List.range' 1577 19 ++ [1597]
def cC : List Wire := List.range' 1557 19 ++ List.range' 1577 19 ++ [1597]
def cK : List Wire := 1559 :: cA
/-- dadon's `core` wires at the head's end. -/
def coreW : List Wire := [1560, 1576, 1596, 1613, 1614]

theorem mem_cA (q : Nat) : q ∈ cA ↔ (1561 ≤ q ∧ q < 1576) ∨ (1577 ≤ q ∧ q < 1596) ∨ q = 1597 := by
  simp only [cA, List.mem_append, List.mem_range'_1, List.mem_singleton]
  ((try unfold Wire at *); omega)
theorem mem_cB (q : Nat) : q ∈ cB ↔ (1577 ≤ q ∧ q < 1596) ∨ q = 1597 := by
  simp only [cB, List.mem_append, List.mem_range'_1, List.mem_singleton]
theorem mem_cC (q : Nat) : q ∈ cC ↔ (1557 ≤ q ∧ q < 1576) ∨ (1577 ≤ q ∧ q < 1596) ∨ q = 1597 := by
  simp only [cC, List.mem_append, List.mem_range'_1, List.mem_singleton]
  ((try unfold Wire at *); omega)
theorem mem_cK (q : Nat) : q ∈ cK ↔ q = 1559 ∨ (1561 ≤ q ∧ q < 1576) ∨ (1577 ≤ q ∧ q < 1596) ∨ q = 1597 := by
  unfold cK; rw [List.mem_cons, mem_cA]
theorem mem_coreW (q : Nat) : q ∈ coreW ↔ q = 1560 ∨ q = 1576 ∨ q = 1596 ∨ q = 1613 ∨ q = 1614 := by
  simp only [coreW, List.mem_cons, List.not_mem_nil, or_false]

/-! From a `bitCheck` to `Safe` and `Proper`. -/

theorem preserve (gs : List Gate) (s : State) (q : Nat) (h : ∀ g ∈ gs, target g ≠ q) :
    (run (GateMirror.forward gs) [] s).basis q = s.basis q := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [run_forward_cons, ih _ (fun k hk => h k (by simp [hk])), transition_ne g s q (fun e => h g (by simp) e.symm)]

theorem safe_bit {gs : List Gate} {pre post : Nat} (hc : bitCheck gs post = some pre) :
    Safe gs (Zm pre) (Zm post) ∧ Proper gs :=
  ⟨fun s hs => let r := bit_sound gs s pre post hc hs; ⟨r.2.1, r.2.2⟩,
   fun g hg => (bit_sound gs ⟨false, fun _ => false⟩ pre post hc (fun _ _ => rfl)).1 g hg⟩

/-- A list without `make` is always fresh-ready (its end zero set can be dropped). -/
theorem safe_drop : ∀ {gs : List Gate} {Z : Wire → Prop}, NoMake gs → Safe gs Z (fun _ => False)
  | [], _, _ => fun s _ => ⟨trivial, fun _ h => h.elim⟩
  | g::gs, _, nm => safe_cons (fun h => by rw [nm g (by simp)] at h; cases h) (safe_drop (fun k hk => nm k (by simp [hk])))

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: fixed leave segments: one `bitCheck` per segment over the window blocks `j ∈ [1,21]` (each evaluates
only its own segment, at most 150 gates, never a whole leave; ~1 s of kernel time for all 19 blocks of the largest). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem fix0_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix0 (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel
theorem fix1_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix1 (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel
theorem fix2_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix2 (start j) (sbP (start j))) (maskSites cK ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel
theorem fix3_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix3 (start j) (sbP (start j))) (maskSites cA ||| far1M (start j)) = some (maskSites cK ||| far1M (start j)) := by
  decide +kernel
theorem fix4_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix4 (start j) (sbP (start j))) (maskSites cB ||| far1M (start j)) = some (maskSites cA ||| far1M (start j)) := by
  decide +kernel
theorem fix5_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix5 (start j) (sbP (start j))) (far1M (start j)) = some (maskSites cB ||| far1M (start j)) := by
  decide +kernel
theorem fix8_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix8 (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel
theorem fix10_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix10 (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel
theorem fix11_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix11 (start j) (sbP (start j))) (maskSites cB ||| far2M (start j)) = some (far2M (start j)) := by
  decide +kernel
theorem fix12_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (leaveFix12 (start j) (sbP (start j))) (maskSites cA ||| far2M (start j)) = some (maskSites cB ||| far2M (start j)) := by
  decide +kernel
theorem lowSign_bit : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    bitCheck (lowSign (start j)) (maskSites cK ||| far2M (start j)) = some (maskSites cA ||| far2M (start j)) := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: generic leave Mirror, part 2. Layout facts of the window blocks (symbolic `s`, `90 ≤ s ≤ 390`),
freshness and `proper` for the variable segments of the head (adjust, barrel, join). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Linear facts about the rail of a window block (and the closed forms of its derived wires). -/
theorem rail_win {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    railP s ≤ 258 ∧ sbP s + 47 ≤ railP s ∧ railP s ≤ 2 * sbP s + 1 ∧ 61 ≤ sbP s ∧ sbP s ≤ 211 ∧
    sbP (s+15) + 7 ≤ sbP s ∧ sbP s ≤ sbP (s+15) + 8 ∧ railP (s+15) ≤ railP s ∧
    railP (s+15) ≤ 2 * sbP (s+15) + 1 ∧ sbP (s+15) + 50 ≤ railP (s+15) ∧
    wpP s + sbP s + 16 = railP s ∧ wpP (s+15) + sbP (s+15) + 16 = railP (s+15) ∧
    e0P s = 1574 + sbP s ∧ e0P (s+15) = 1574 + sbP (s+15) ∧ bTopP s = 785 + railP s ∧
    bTopP (s+15) = 785 + railP (s+15) ∧ a0P s = s + sbP s + 32 ∧ b0P s = 787 + sbP s ∧
    lowsP s = 18 + sbP (s+15) - sbP s ∧ 2 * sbP s + s ≤ 513 ∧ 512 ≤ 2 * sbP s + s := by
  unfold wpP e0P bTopP a0P b0P lowsP railP sbP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try split_ifs) <;> omega

/-- The bank wires `bankW s i`, `i < wp+15`: three disjoint runs. -/
theorem bank_cases {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) :
    (i < 3 ∧ (bankW s i : Nat) = e0P s + i) ∨ (3 ≤ i ∧ i < wpP s ∧ (bankW s i : Nat) = bTopP s + 1 + i - wpP s ∧
      (bankW s i : Nat) ≤ 1043 ∧ 790 ≤ (bankW s i : Nat)) ∨
    (wpP s ≤ i ∧ (bankW s i : Nat) = 1598 + i - wpP s ∧ (bankW s i : Nat) ≤ 1612) := by
  have r := rail_win h1 h2
  unfold bankW; unfold wpP bTopP e0P at *
  split_ifs <;> ((try unfold Wire at *); omega)

theorem bank_inj {s i k : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) (hk : k < wpP s + 15)
    (e : bankW s i = bankW s k) : i = k := by
  have r := rail_win h1 h2
  have a := bank_cases h1 h2 hi; have b := bank_cases h1 h2 hk
  unfold wpP bTopP e0P at *
  ((try unfold Wire at *); omega)

theorem pool_cases {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    (1598 + i < e0P s ∧ (poolW s i : Nat) = 1598 + i) ∨ (e0P s ≤ 1598 + i ∧ (poolW s i : Nat) = 1608 + i) := by
  unfold poolW; split_ifs <;> ((try unfold Wire at *); omega)

theorem pool_nodup (s n : Nat) (h1 : 90 ≤ s) (h2 : s ≤ 390) : ((List.range n).map (poolW s)).Nodup := by
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have a := pool_cases (i := x) h1 h2; have b := pool_cases (i := y) h1 h2
  ((try unfold Wire at *); omega)

theorem storeW_cases (k : Nat) :
    (1558 + k < 1598 ∧ (storeW k : Nat) = 1558 + k) ∨ (1598 ≤ 1558 + k ∧ (storeW k : Nat) = 1573 + k) := by
  unfold storeW; split_ifs <;> ((try unfold Wire at *); omega)

theorem tags_range : ∀ i, i < 16 → 1556 ≤ tagsP.getD i 0 ∧ tagsP.getD i 0 ≤ 1576 := by decide

/-! Stage 1: the adjust (bank-wide sign fan-out and AND-chain add into the carry pool), on `far1M`. -/

theorem adjust_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveAdjust s) (Zm (far1M s)) (Zm (far1M s)) ∧ Proper (leaveAdjust s) := by
  have r := rail_win h1 h2
  have ys_far : ∀ y ∈ (List.range (wpP s)).map (bankW s), ¬ Zm (far1M s) y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    rw [List.mem_range] at hi
    have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
    rw [far1_iff]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
  have cs_in : ∀ c ∈ (List.range (wpP s - 1)).map (poolW s), Zm (far1M s) c := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    rw [List.mem_range] at hi
    have p := pool_cases (i := i) h1 h2
    rw [far1_iff]; unfold wpP e0P at *; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · unfold leaveAdjust adjustG
    exact safe_append (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far))
      (safe_append (safe_addG _ _ _ _ cs_in (pool_nodup s _ h1 h2) ys_far)
        (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far)))
  · unfold leaveAdjust
    refine proper_adjustG _ _ _ _ (fun y hy => ?_) (fun hc => ?_) (pool_nodup s _ h1 h2)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range] at hi
      have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
      refine ⟨fun hc => ?_, ?_, ?_⟩
      · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc
        rw [List.mem_range] at hk
        have p := pool_cases (i := k) h1 h2; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
    · obtain ⟨k, _, e⟩ := List.mem_map.mp hc
      have p := pool_cases (i := k) h1 h2; unfold e0P at *; ((try unfold Wire at *); omega)

/-! Stage 2: barrel, join (frames on `far2M`). -/

theorem bank_far2 {s i : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hi : i < wpP s + 15) : ¬ Zm (far2M s) (bankW s i) := by
  have r := rail_win h1 h2
  have b := bank_cases h1 h2 hi
  rw [far2_iff]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)

theorem barrel_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveBarrel s) (Zm (far2M s)) (Zm (far2M s)) ∧ Proper (leaveBarrel s) := by
  have r := rail_win h1 h2
  have c_far : ¬ Zm (far2M s) 1613 := by rw [far2_iff]; ((try unfold Wire at *); omega)
  have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 →
      AllAT (fun _ => True) (fun q => ¬ Zm (far2M s) q) (stageG 1613 (bankW s) xs d n) :=
    fun xs d n hn => allAT_stageG _ _ _ _ _ ⟨trivial, c_far⟩ (fun _ _ => trivial)
      (fun i hi => ⟨⟨trivial, bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩, ⟨trivial, bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩⟩)
  have pr : ∀ (xs : List Wire) (d n : Nat), 0 < d → n + d ≤ wpP s + 15 → (∀ x ∈ xs, x ≠ 1613) →
      Proper (stageG 1613 (bankW s) xs d n) := by
    intro xs d n hd hn hx
    refine proper_stageG _ _ _ _ _ hx (fun i hi => ⟨fun e => ?_, fun e => ?_⟩)
    · have := bank_inj h1 h2 (i := i+d) (k := i) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)) e; ((try unfold Wire at *); omega)
    · have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega)); unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · unfold leaveBarrel
    exact safe_append (safe_append (safe_append (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega)))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega)))))
      (safe_frame' (noMake_stageG _ _ _ _ _) (st _ _ _ (by ((try unfold Wire at *); omega))))
  · unfold leaveBarrel
    refine proper_append (proper_append (proper_append ?_ ?_) ?_) ?_ <;>
      exact pr _ _ _ (by decide) (by ((try unfold Wire at *); omega)) (by decide)

theorem join_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveJoin s) (Zm (far2M s)) (Zm (far2M s)) ∧ Proper (leaveJoin s) := by
  have r := rail_win h1 h2
  have a_far : ∀ i, i ≤ 18 → ¬ Zm (far2M s) (a0P s + i) := by
    intro i hi; rw [far2_iff]; unfold a0P e0P; ((try unfold Wire at *); omega)
  have rows : ∀ r ∈ columnsP s, ∃ i, i < 18 ∧ r.shadow = a0P s + i ∧ r.tube = bankW s i ∧
      (∀ w, r.hot = some w → 1556 ≤ w ∧ w ≤ 1576) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    rw [List.mem_range] at hi
    refine ⟨i, hi, rfl, rfl, fun w hw => ?_⟩
    dsimp only at hw
    split at hw
    · cases hw; exact tags_range i (by ((try unfold Wire at *); omega))
    · cases hw
  refine ⟨?_, ?_⟩
  · unfold leaveJoin
    refine safe_append (safe_frame' (noMake_digitsG _ _ _ _ _ _) (allAT_digitsG _ _ _ _ trivial trivial _ _
      (fun i _ hi => ⟨trivial, a_far i (by ((try unfold Wire at *); omega)), a_far (i+1) (by ((try unfold Wire at *); omega))⟩)))
      (safe_frame' (noMake_wordG _ _) (allAT_wordG _ ⟨trivial, ?_⟩ _ (fun r hr => ?_)))
    · rw [far2_iff]; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hs, ht, _⟩ := rows r hr
      exact ⟨fun _ _ => trivial, ⟨trivial, hs ▸ a_far i (by ((try unfold Wire at *); omega))⟩, ⟨trivial, ht ▸ bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩⟩
  · unfold leaveJoin
    refine proper_append (proper_digitsG _ _ _ _ _ _ (fun i _ hi => ?_)) (proper_wordG _ _ (fun r hr => ?_))
    · have t := tags_range i (by ((try unfold Wire at *); omega))
      ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hs, ht, hh⟩ := rows r hr
      have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
      refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
      · have := hh w hw; ((try unfold Wire at *); omega)
      · rw [hs]; unfold a0P; ((try unfold Wire at *); omega)
      · rw [ht]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · rw [hs, ht]; unfold a0P wpP bTopP e0P at *; ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: generic leave Mirror, part 3. The head chain, the mid part (low store, StoreMapped, low close) and the
close, then the generic replacement of dadon's per-block `Leave{s}Mirror.inverts`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem far2_sub {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (q : Wire) (h : Zm (far2M s) q) : Zm (far1M s) q := by
  rw [far2_iff] at h; rw [far1_iff]; ((try unfold Wire at *); omega)

theorem start_win (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : 90 ≤ start j ∧ start j ≤ 390 := by
  unfold start; ((try unfold Wire at *); omega)

/-! The head: fixed segments by `bitCheck`, variable ones generic. -/

theorem head_ok (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    Safe (leaveHeadOps (start j)) (Zm (maskSites cC ||| far1M (start j))) (Zm (maskSites cK ||| far2M (start j))) ∧
    Proper (leaveHeadOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have f0 := safe_bit (fix0_bit j h0 h1); have f1 := safe_bit (fix1_bit j h0 h1)
  have f2 := safe_bit (fix2_bit j h0 h1); have f3 := safe_bit (fix3_bit j h0 h1)
  have f4 := safe_bit (fix4_bit j h0 h1); have f5 := safe_bit (fix5_bit j h0 h1)
  have f8 := safe_bit (fix8_bit j h0 h1); have f10 := safe_bit (fix10_bit j h0 h1)
  have f11 := safe_bit (fix11_bit j h0 h1); have f12 := safe_bit (fix12_bit j h0 h1)
  have fl := safe_bit (lowSign_bit j h0 h1)
  have ad := adjust_ok w1 w2; have ba := barrel_ok w1 w2; have jo := join_ok w1 w2
  refine ⟨?_, ?_⟩
  · unfold leaveHeadOps
    exact safe_append (safe_append (safe_append (safe_append (safe_append (safe_append (safe_append (safe_append
      (safe_append (safe_append (safe_append (safe_append (safe_append f0.1 f1.1) f2.1) f3.1) f4.1) f5.1) ad.1)
      (safe_mono ba.1 (far2_sub w1 w2) (fun _ h => h))) f8.1) jo.1) f10.1) f11.1) f12.1) fl.1
  · unfold leaveHeadOps
    exact proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append f0.2 f1.2) f2.2) f3.2)
      f4.2) f5.2) ad.2) ba.2) f8.2) jo.2) f10.2) f11.2) f12.2) fl.2

/-! The mid part runs on `midZ`: the carries `1559..1597` and the scratch `1613 .. e0-1`. -/

def midZ (s q : Nat) : Prop := (1559 ≤ q ∧ q ≤ 1597) ∨ (1613 ≤ q ∧ q < e0P s)

theorem to_mid {s : Nat} (st : State) (hz : ZeroOn st (Zm (maskSites cK ||| far2M s)))
    (hc : ∀ q ∈ coreW, st.basis q = false) : ZeroOn st (midZ s) := by
  intro q hq
  by_cases hk : q ∈ cK
  · exact hz q ((zm_or _ _ _).mpr (Or.inl ((zm_sites _ _).mpr hk)))
  by_cases hw : q ∈ coreW
  · exact hc q hw
  · apply hz q; apply (zm_or _ _ _).mpr; right; rw [far2_iff]
    rw [mem_cK] at hk; rw [mem_coreW] at hw; unfold midZ at hq; ((try unfold Wire at *); omega)

theorem safe_app (Z : Wire → Prop) {a b : List Gate} (ha : Safe a Z Z) (hb : Safe b Z Z) : Safe (a ++ b) Z Z :=
  safe_append ha hb

/-- A literal frame list: no `make`, every target outside `Z`. -/
theorem safe_lit {Z : Wire → Prop} {gs : List Gate} (nm : NoMake gs) (ht : ∀ g ∈ gs, ¬ Z (target g)) : Safe gs Z Z :=
  safe_frame nm (fun g hg _ => ht g hg)

theorem lowRest_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (lowRest s) (midZ s) (fun q => q = 1558 ∨ midZ s q) ∧ Proper (lowRest s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, _, _, ea, eb, el, _, _⟩ := r
  have hL : lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bs_out : ∀ y ∈ (List.range (lowsP s)).map (b0P s + ·), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have cs_in : ∀ c ∈ (List.range (lowsP s - 1)).map (1559 + ·), midZ s c := by
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have cs_nd : ((List.range (lowsP s - 1)).map (1559 + ·)).Nodup :=
    List.Nodup.map (fun a b e => by ((try unfold Wire at *); omega)) List.nodup_range
  refine ⟨?_, ?_⟩
  · unfold lowRest
    have tail : Safe ([.pop (b0P s - 1) 1557 1558] ++ [.cx (a0P s - 1) 1557, .x 1557]) (midZ s)
        (fun q => q = 1558 ∨ midZ s q) :=
      safe_append safe_pop (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> unfold midZ <;> ((try unfold Wire at *); omega)))
    refine safe_append (safe_app (midZ s) (safe_app (midZ s) (safe_app (midZ s) ?_ ?_) ?_) ?_) tail
    · exact safe_lit (noMake_map _ _ (fun _ _ => rfl)) (fun g hg => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp only [target]; unfold midZ; ((try unfold Wire at *); omega))
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
    · exact safe_addG _ _ _ _ cs_in cs_nd bs_out
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
  · unfold lowRest
    refine proper_append (proper_append (proper_append (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_
    · exact proper_map _ _ (fun i hi => by rw [List.mem_range] at hi; exact pr_ccx (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · refine proper_addG _ _ _ (fun y hy => ?_) (fun hc => ?_) cs_nd
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
        refine ⟨fun hc => ?_, by ((try unfold Wire at *); omega)⟩
        obtain ⟨k, hk, e⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk; ((try unfold Wire at *); omega)
      · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc; ((try unfold Wire at *); omega)
    · exact proper_cons (pr_pop (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil))

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: generic leave Mirror, part 4. StoreMapped, the low close, the close; then the generic
`leave_inverts` (replaces dadon's per-block `Leave{s}Mirror.inverts`, about 4.2k lines per block). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem safe_then {a b : List Gate} {Z : Wire → Prop} (M : Wire → Prop) (ha : Safe a Z M) (hb : Safe b M M) :
    Safe (a ++ b) Z M := safe_append ha hb

theorem storeMapped_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveStoreMapped s) (fun q => q = 1558 ∨ midZ s q) (midZ s) ∧ Proper (leaveStoreMapped s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  have hL : 10 ≤ lowsP s ∧ lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank_out : ∀ i, lowsP s ≤ i → i < wpP s + 15 → ¬ midZ s (bankW s i) ∧ (bankW s i : Nat) ≠ 1558 ∧
      (bankW s i : Nat) ≠ 1557 ∧ (bankW s i : Nat) ≠ 1556 ∧ ∀ k, (storeW k : Nat) ≠ bankW s i := by
    intro i a b
    have bc := bank_cases h1 h2 b
    refine ⟨?_, ?_, ?_, ?_, fun k => ?_⟩
    · unfold midZ; ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · ((try unfold Wire at *); omega)
    · have sc := storeW_cases k; ((try unfold Wire at *); omega)
  have hi_out : ∀ y ∈ (List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i)), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    exact (bank_out _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).1
  have hir_out : ∀ y ∈ ((List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i))).reverse, ¬ midZ s y :=
    fun y hy => hi_out y (List.mem_reverse.mp hy)
  have s2_out : ∀ y ∈ (List.range (lowsP s + 1)).map (b0P s - 1 + ·), ¬ midZ s y := by
    intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
    unfold midZ; ((try unfold Wire at *); omega)
  have s2r_out : ∀ y ∈ ((List.range (lowsP s + 1)).map (b0P s - 1 + ·)).reverse, ¬ midZ s y :=
    fun y hy => s2_out y (List.mem_reverse.mp hy)
  have st_in : ∀ k, 0 < k → k ≤ 0 + (wpP s + 15 - lowsP s + 1) → midZ s (storeW k) := by
    intro k a b; have sc := storeW_cases k; unfold midZ; ((try unfold Wire at *); omega)
  have st_inj : ∀ k k', 0 < k → k ≤ 0 + (wpP s + 15 - lowsP s + 1) → 0 < k' → k' ≤ 0 + (wpP s + 15 - lowsP s + 1) →
      storeW k = storeW k' → k = k' := by
    intro k k' _ _ _ _ e; have a := storeW_cases k; have b := storeW_cases k'; ((try unfold Wire at *); omega)
  have c2_in : ∀ k, 0 < k → k ≤ 0 + (lowsP s + 1) → midZ s (1558 + k) := by
    intro k a b; unfold midZ; ((try unfold Wire at *); omega)
  have c2_inj : ∀ k k', 0 < k → k ≤ 0 + (lowsP s + 1) → 0 < k' → k' ≤ 0 + (lowsP s + 1) →
      (1558 + k : Wire) = 1558 + k' → k = k' := by
    intro k k' _ _ _ _ e; ((try unfold Wire at *); omega)
  have top_out : ¬ midZ s (a0P s + lowsP s - 1) := by unfold midZ; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · simp only [leaveStoreMapped]
    have p1 : Safe ([.make (a0P s + lowsP s - 1 - 2) (a0P s + lowsP s - 1 - 1) 1558] ++
        [.x 1558, .x (a0P s + lowsP s - 1)]) (fun q => q = 1558 ∨ midZ s q) (midZ s) :=
      safe_append (safe_make (Or.inl rfl)) (safe_mono (Z := midZ s)
        (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
          (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> first | exact top_out | (unfold midZ; ((try unfold Wire at *); omega))))
        (fun q hq => ⟨fun e => by subst e; unfold midZ at hq; ((try unfold Wire at *); omega), Or.inr hq⟩) (fun _ h => h))
    have p2a : Safe [.x (a0P s + lowsP s - 1), .x 1558] (midZ s) (midZ s) :=
      safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target] <;> first | exact top_out | (unfold midZ; ((try unfold Wire at *); omega)))
    have p2b : Safe [.x 1558] (fun q => q ≠ 1558 ∧ (q = 1558 ∨ midZ s q)) (midZ s) :=
      safe_mono (Z := midZ s) (safe_lit (fun g hg => by simp at hg; subst hg; rfl)
          (fun g hg => by simp at hg; subst hg; simp only [target]; unfold midZ; ((try unfold Wire at *); omega)))
        (fun q hq => ⟨fun e => by subst e; unfold midZ at hq; ((try unfold Wire at *); omega), Or.inr hq⟩) (fun _ h => h)
    have p2 : Safe ([.x (a0P s + lowsP s - 1), .x 1558] ++ [.pop (a0P s + lowsP s - 1 - 2) (a0P s + lowsP s - 1 - 1) 1558] ++
        [.make 1556 1557 1558] ++ [.x 1558]) (midZ s) (midZ s) :=
      safe_append (safe_append (safe_append p2a safe_pop) (safe_make (Or.inl rfl))) p2b
    have ch1 := safe_chainG storeW (fun i => if i = 0 then a0P s + lowsP s - 1 else bankW s (lowsP s + i - 1))
      [.cx (storeW (wpP s + 15 - lowsP s + 1)) 1557, .x 1557] 0 (wpP s + 15 - lowsP s + 1) (midZ s) st_in st_inj
      (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target, chainZ] <;> intro h <;> unfold midZ at h <;> ((try unfold Wire at *); omega)))
    have ch2 := safe_chainG (fun k => (1558 + k : Wire)) (fun k => b0P s - 1 + k) [.cx (1558 + (lowsP s + 1)) 1556, .x 1556]
      0 (lowsP s + 1) (midZ s) c2_in c2_inj
      (safe_lit (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> rfl)
        (fun g hg => by simp at hg; rcases hg with rfl|rfl <;> simp only [target, chainZ] <;> intro h <;> unfold midZ at h <;> ((try unfold Wire at *); omega)))
    have x58 : Safe [GateMirror.Gate.x 1558] (midZ s) (midZ s) :=
      safe_lit (fun g hg => by simp at hg; subst hg; rfl) (fun g hg => by simp at hg; subst hg; simp only [target]; unfold midZ; ((try unfold Wire at *); omega))
    have q1 := safe_then (midZ s) p1 (safe_frame' (noMake_xsG _) (allAT_xsG _ hi_out))
    have q2 := safe_then (midZ s) q1 ch1
    have q3 := safe_then (midZ s) q2 (safe_frame' (noMake_xsG _) (allAT_xsG _ hir_out))
    have q4 := safe_then (midZ s) q3 p2
    have q5 := safe_then (midZ s) q4 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2_out))
    have q6 := safe_then (midZ s) q5 ch2
    have q7 := safe_then (midZ s) q6 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2r_out))
    exact safe_then (midZ s) q7 x58
  · simp only [leaveStoreMapped]
    refine proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) (proper_cons rfl proper_nil)
    · exact proper_cons (pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons rfl (proper_cons rfl proper_nil))
    · refine proper_chainG _ _ _ (proper_cons (pr_cx ?_) (proper_cons rfl proper_nil)) _ _ (fun k _ hk => ⟨?_, ?_⟩)
      · have sc := storeW_cases (wpP s + 15 - lowsP s + 1); ((try unfold Wire at *); omega)
      · intro e; have := st_inj k (k+1) ; have a := storeW_cases k; have b := storeW_cases (k+1); ((try unfold Wire at *); omega)
      · dsimp only
        split
        · have sc := storeW_cases (k+1); ((try unfold Wire at *); omega)
        · exact Ne.symm ((bank_out (lowsP s + k - 1) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).2.2.2.2 (k+1))
    · exact proper_cons rfl (proper_cons rfl (proper_cons (pr_pop (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
        (proper_cons (pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil))))
    · exact proper_chainG _ _ _ (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil)) _ _
        (fun k _ hk => ⟨by ((try unfold Wire at *); omega), by ((try unfold Wire at *); omega)⟩)

theorem lowClose_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveLowClose s) (midZ s) (midZ s) ∧ Proper (leaveLowClose s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  refine ⟨?_, ?_⟩
  · simp only [leaveLowClose]
    refine safe_app (midZ s) (safe_app (midZ s) (safe_frame' (noMake_xsG _) (allAT_xsG _ (fun y hy => ?_)))
      (safe_lit (noMake_map _ _ (fun _ _ => rfl)) (fun g hg => ?_)))
      (safe_lit (noMake_flatMap _ _ (fun _ _ => noMake_cswapG _ _ _)) (fun g hg => ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold midZ; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg; rw [List.mem_range] at hi; simp only [target]; unfold midZ; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hg⟩ := List.mem_flatMap.mp hg; rw [List.mem_range] at hi
      simp only [cswapG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl|rfl|rfl <;> simp only [target] <;> unfold midZ <;> ((try unfold Wire at *); omega)
  · simp only [leaveLowClose]
    refine proper_append (proper_append (proper_xsG _) (proper_map _ _ (fun i hi => pr_cx ?_)))
      (proper_flatMap _ _ (fun i hi => proper_cswapG ?_ ?_))
    all_goals (rw [List.mem_range] at hi; ((try unfold Wire at *); omega))

/-- History wires of the block in the `OB5.sig (s+14)` frame: raw below 1301, else moved above `e0+10`. -/
theorem sig_hist {s c : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    ((OB5.sig (s+14) (s+c) : Nat) = s + c ∧ s + c ≤ 1300) ∨
    ((OB5.sig (s+14) (s+c) : Nat) = 3113 - (s + c) ∧ e0P s + 10 ≤ 3113 - (s + c) ∧ 3113 - (s + c) ≤ 1812) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  unfold OB5.sig; split_ifs <;> ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.Partial

end


/-! par-c1: generic leave Mirror, part 5. The close and the generic `leave_inverts`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem moves_ne {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) : ∀ p ∈ movesP s, p.1 ≠ p.2 := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · obtain ⟨i, hi, e⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    have bc := bank_cases (i := lowsP s + i) h1 h2 (by ((try unfold Wire at *); omega))
    rw [← e]; show (bankW s (lowsP s + i) : Nat) ≠ bTopP (s+15) + 4 + i - wpP (s+15)
    ((try unfold Wire at *); omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with e|e|e|e|e|e <;> rw [e] <;> show (_ : Nat) ≠ _ <;> ((try unfold Wire at *); omega)

theorem close_ok {s : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) :
    Safe (leaveClose s) (fun q => q = 1556 ∨ midZ s q) (fun _ => False) ∧ Proper (leaveClose s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  have e44 := sig_hist (c := 1044) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e45 := sig_hist (c := 1045) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e46 := sig_hist (c := 1046) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e47 := sig_hist (c := 1047) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have e48 := sig_hist (c := 1048) h1 h2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  refine ⟨?_, ?_⟩
  · unfold leaveClose
    refine safe_append (safe_eventsG _ _ _ _ ?_ ?_ ?_) (safe_drop (noMake_swapsG _))
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> unfold midZ <;> ((try unfold Wire at *); omega)
    · show [1556, 1559, 1560, 1561, 1562].Nodup
      decide
    · unfold midZ; ((try unfold Wire at *); omega)
  · unfold leaveClose
    refine proper_append (proper_eventsG _ _ _ ?_ ?_ ?_ (by ((try unfold Wire at *); omega))) (proper_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold Wire at *); omega)
    · show ((e0P s + 7) :: [1556, 1559, 1560, 1561, 1562]).Nodup
      refine List.nodup_cons.mpr ⟨?_, by decide⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]; ((try unfold Wire at *); omega)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> ((try unfold Wire at *); omega)
    · exact moves_ne h1 h2

/-! The generic Mirror. -/

theorem leaveMidOps_eq (s : Nat) : leaveMidOps s = lowRest s ++ leaveStoreMapped s ++ leaveLowClose s := rfl

attribute [local irreducible] leaveOps leaveHeadOps leaveMidOps leaveClose lowRest leaveStoreMapped leaveLowClose
  GateMirror.Ready

theorem leave_ready (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false) :
    Ready s (leaveOps (start j)) ∧ (∀ g ∈ leaveOps (start j), proper g = true) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have hd := head_ok j h0 h1
  have lr := lowRest_ok w1 w2; have sm := storeMapped_ok w1 w2; have lc := lowClose_ok w1 w2
  have cl := close_ok w1 w2
  have z0 : ZeroOn s (Zm (maskSites cC ||| far1M (start j))) := by
    intro q hq
    rcases (zm_or _ _ _).mp hq with h|h
    · rw [zm_sites, mem_cC] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ee, _⟩ := rail_win w1 w2
      exact initial q (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    · rw [far1_iff] at h
      rcases h with ⟨a, b⟩|⟨a, b⟩
      · exact initial q (by ((try unfold Wire at *); omega)) b
      · exact extra q a b
  obtain ⟨r1, z1⟩ := hd.1 s z0
  have mid : Safe (leaveMidOps (start j)) (midZ (start j)) (midZ (start j)) := by
    rw [leaveMidOps_eq]; exact safe_append (Z1 := midZ (start j)) (safe_append (Z1 := fun q => q = 1558 ∨ midZ (start j) q) lr.1 sm.1) lc.1
  obtain ⟨r2, z2⟩ := mid _ (to_mid _ z1 core)
  have z2' : ZeroOn (run (GateMirror.forward (leaveMidOps (start j))) []
      (run (GateMirror.forward (leaveHeadOps (start j))) [] s)) (fun q => q = 1556 ∨ midZ (start j) q) := by
    intro q hq
    rcases hq with rfl|hq
    · rw [← run_forward_append]; exact post
    · exact z2 q hq
  obtain ⟨r3, _⟩ := cl.1 _ z2'
  refine ⟨?_, ?_⟩
  · rw [leaveOps_split]
    refine ready_append _ _ _ (ready_append _ _ _ r1 r2) ?_
    rw [run_forward_append]; exact r3
  · rw [leaveOps_split]
    rw [leaveMidOps_eq]; exact proper_append (proper_append hd.2 (proper_append (proper_append lr.2 sm.2) lc.2)) cl.2

/-- The generic leave Mirror: `leaveInvP j` undoes `leaveP j` (dadon's `Leave{s}Mirror.inverts`, all blocks). -/
theorem leave_inverts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (phase : ∀ m, (run (leaveP j) m s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false)
    (m n : List Bool) :
    run (leaveInvP j) n (run (leaveP j) m s) = s := by
  obtain ⟨ready, phys⟩ := leave_ready j h0 h1 s initial extra core post
  exact invert (leaveOps (start j)) s phys (all_prepared _ s phys phase) ready m n

end ECDSAAdd.Entrant.StairPacket.Partial

end

section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror Challenge
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! The move bridge: generic in the block tick `s ∈ [90, 390]`. -/

/-- A control that never reads a join cell. -/
def MoveA (s q : Nat) : Prop := ¬ (a0P s ≤ q ∧ q < a0P s + 16)
/-- A target that is no join cell, no tag and not the crossing wire. -/
def MoveT (s q : Nat) : Prop := MoveA s q ∧ (q < 1556 ∨ 1576 < q) ∧ q ≠ e0P s + 6

theorem mem_moveRows {s : Nat} {r : MoveChain.Row} (hr : r ∈ moveRows s) :
    ∃ i, i < 16 ∧ r = (tagsP.getD i 0, a0P s + i) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem cell_lt {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : a0P s + 16 ≤ 500 ∧ 1641 ≤ e0P s + 6 := by
  have r := rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  omega

theorem calm_of {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) {r : MoveChain.Row} (hr : r ∈ moveRows s) (g : Gate)
    (hg : (∀ q ∈ g.controls, MoveA s q) ∧ MoveT s (target g)) : calmGate (e0P s + 6) r g = true := by
  obtain ⟨i, hi, rfl⟩ := mem_moveRows hr
  have t := tags_range i hi
  have cl := cell_lt w1 w2
  obtain ⟨hc, ⟨ht0, ht1, ht2⟩⟩ := hg
  unfold MoveA at hc ht0
  cases g <;>
  simp only [Gate.controls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies,
    implies_true, target] at hc ht0 ht1 ht2 <;>
  simp only [calmGate, MoveChain.quiet, front, erase, plainGate, MoveChain.corrFree, target, Bool.true_or,
    Bool.false_or, Bool.or_true, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;> (try unfold Wire at *) <;> omega

theorem fix5_tail (s h : Nat) : (leaveFix5 s h).drop 43 =
    [.cx 1589 1596, .cx 1590 1596, .cx 1591 1596, .cx 1592 1596, .cx 1593 1596, .cx 1594 1596, .cx 1595 1596,
     .cx 1569 1596, .cx 1570 1596, .cx 1571 1596, .cx 1572 1596, .cx 1573 1596, .cx 1574 1596, .cx 1575 1596,
     .cx 1560 1596, .make (h+1580) 1596 1597] := rfl

/-- The segment between the mux and the digit pass never writes a tag or the crossing wire and never reads a cell. -/
theorem moveB_away {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : AllAT (MoveA s) (MoveT s) (moveB s) := by
  have r := rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have cl := cell_lt w1 w2
  have far : ∀ q : Nat, 786 ≤ q → MoveA s q := by intro q h; unfold MoveA; omega
  have farT : ∀ q : Nat, 786 ≤ q → (q < 1556 ∨ 1576 < q) → q ≠ e0P s + 6 → MoveT s q :=
    fun q h a b => ⟨far q h, a, b⟩
  have bank : ∀ i, i < wpP s + 15 → MoveA s (bankW s i) ∧ MoveT s (bankW s i) := by
    intro i hi
    rcases bank_cases w1 w2 hi with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩ <;>
      (rw [e] at *; exact ⟨far _ (by omega), farT _ (by omega) (by omega) (by omega)⟩)
  have tagsA : ∀ x ∈ [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560, 1563, 1567, 1571, 1575, 1565, 1573, 1569],
      MoveA s x := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply far; rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have ctl : ∀ xs : List Wire, (∀ x ∈ xs, 1556 ≤ x) → ∀ x ∈ xs, MoveA s x := fun xs h x hx => far x (by
    have := h x hx; unfold Wire at *; omega)
  unfold moveB
  refine allAT_append (allAT_append (allAT_append ?_ ?_) ?_) ?_
  · rw [fix5_tail]
    have c6 : MoveA s (sbP s + 1580) := far _ (by omega)
    have t96 : MoveT s 1596 := farT _ (by omega) (by omega) (by omega)
    have t97 : MoveT s 1597 := farT _ (by omega) (by omega) (by omega)
    have a96 : MoveA s 1596 := far _ (by omega)
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    refine allAT_cons (ok_cx (far _ (by omega)) t96) ?_
    exact allAT_cons (ok_make c6 a96 t97) allAT_nil
  · unfold leaveAdjust
    refine allAT_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (far _ (by omega)) (far _ (by omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := pool_cases (i := i) w1 w2
      exact ⟨far _ (by unfold Wire at *; omega), farT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)
        (by unfold Wire at *; omega)⟩
  · unfold leaveBarrel
    have c13 : MoveA s 1613 ∧ MoveT s 1613 := ⟨far _ (by omega), farT _ (by omega) (by omega) (by omega)⟩
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x) →
        AllAT (MoveA s) (MoveT s) (stageG 1613 (bankW s) xs d n) :=
      fun xs d n hn hx => allAT_stageG _ _ _ _ _ c13 (ctl xs hx)
        (fun i hi => ⟨bank i (by omega), bank (i+d) (by omega)⟩)
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    exact allAT_append (st _ _ _ (by omega) (by decide)) (st _ _ _ (by omega) (by decide))
  · show AllAT (MoveA s) (MoveT s) [.x 1613, .cx 1597 1613]
    exact allAT_cons (ok_x (farT _ (by omega) (by omega) (by omega)))
      (allAT_cons (ok_cx (far _ (by omega)) (farT _ (by omega) (by omega) (by omega))) allAT_nil)

theorem calmB {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    (moveRows s).all (fun r => (moveB s).all (calmGate (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro g hg
  exact calm_of w1 w2 hr g (h g hg)

theorem stillB {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    (moveRows s).all (fun r => (GateMirror.forward (moveB s)).all (MoveChain.quiet (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro i hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
  exact (Bool.and_eq_true_iff.mp (calm_of w1 w2 hr g (h g hg))).1

theorem apart_move {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : MoveChain.apart (e0P s + 6) (moveRows s) = true := by
  have cl := cell_lt w1 w2
  unfold MoveChain.apart
  rw [List.all_eq_true]; intro r hr
  obtain ⟨i, hi, rfl⟩ := mem_moveRows hr
  have t := tags_range i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨by unfold Wire at *; omega, by unfold Wire at *; omega, by unfold Wire at *; omega, fun r' hr' => ?_⟩
  obtain ⟨i', hi', rfl⟩ := mem_moveRows hr'
  have t' := tags_range i' hi'
  simp only [decide_eq_true_eq]; unfold Wire at *; omega

theorem lone_of_nodup : ∀ rs : List MoveChain.Row, (rs.map Prod.snd).Nodup → MoveChain.lone rs = true
  | [] => fun _ => rfl
  | r :: rs => fun h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [MoveChain.lone, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun r' hr' e => h.1 r' hr' e, lone_of_nodup rs h.2⟩

theorem lone_move (s : Nat) : MoveChain.lone (moveRows s) = true := by
  apply lone_of_nodup
  simp only [moveRows, List.map_map]
  exact List.Nodup.map (fun a b e => by simpa using e) List.nodup_range

theorem woven_of (c : Wire) : ∀ (rs : List MoveChain.Row) (ks : Program), rs.length = ks.length →
    (∀ k ∈ ks, ∀ r ∈ rs, MoveChain.quiet c r k = true) → MoveChain.woven c rs ks = true
  | [], [], _, _ => rfl
  | r :: rs, k :: ks, hl, h => by
    simp only [MoveChain.woven, Bool.and_eq_true, List.all_eq_true, List.mem_singleton, forall_eq]
    refine ⟨fun x hx => h k (by simp) x (by simp [hx]),
      woven_of c rs ks (by simpa using hl) (fun k' hk' x hx => h k' (by simp [hk']) x (by simp [hx]))⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem mem_keptG (hot bank : Nat → Wire) (d : Nat) : ∀ start n g, g ∈ keptG hot bank d start n →
    ∃ i, start ≤ i ∧ i < start + n ∧ g = .ccx (hot i) d (bank (i+1))
  | _, 0, g, h => by simp [keptG] at h
  | start, n+1, g, h => by
    simp only [keptG, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨start, le_refl _, by omega, rfl⟩
    · obtain ⟨i, a, b, e⟩ := mem_keptG hot bank d (start+1) n g h
      exact ⟨i, by omega, by omega, e⟩

theorem keptG_length (hot bank : Nat → Wire) (d : Nat) : ∀ start n, (keptG hot bank d start n).length = n
  | _, 0 => rfl
  | start, n+1 => by simp [keptG, keptG_length hot bank d (start+1) n]

theorem woven_move {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) :
    MoveChain.woven (e0P s + 6) (moveRows s) (GateMirror.forward (moveKept s)) = true := by
  have cl := cell_lt w1 w2
  apply woven_of
  · simp [moveRows_length, GateMirror.forward, moveKept, keptG_length]
  · intro k hk r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
    obtain ⟨i, _, hi, rfl⟩ := mem_keptG _ _ _ _ _ g hg
    obtain ⟨i', hi', rfl⟩ := mem_moveRows hr
    have t := tags_range i (by omega)
    have t' := tags_range i' hi'
    simp only [front, MoveChain.quiet, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try unfold Wire at *) <;> omega

theorem kept_plain (hot bank : Nat → Wire) (d : Nat) : ∀ start n, (keptG hot bank d start n).all plainGate = true
  | _, 0 => rfl
  | start, n+1 => by
    show (plainGate (.ccx (hot start) d (bank (start+1))) && (keptG hot bank d (start+1) n).all plainGate) = true
    rw [kept_plain hot bank d (start+1) n]; rfl

/-- The move leave runs exactly like the reference leave whenever, in front of the mux, the crossing wire is clean
and every hot tag selects the same cell. -/
theorem leaveMove_same {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) (v : State) (m : List Bool) (a0 : Wire)
    (clean : (run (GateMirror.forward (moveA s)) m v).basis (e0P s + 6) = false)
    (sel : ∀ r ∈ moveRows s, (run (GateMirror.forward (moveA s)) m v).basis r.1 = true → r.2 = a0) :
    run (GateMirror.forward (leaveMoveOps s)) m v = run (GateMirror.forward (leaveOps s)) m v := by
  rw [leaveMoveOps_shape, leaveOps_shape]
  simp only [forward_app]
  rw [rowGates_forward, mux_forward, dig_forward]
  exact MoveChain.splice (e0P s + 6) (moveRows s) (GateMirror.forward (moveA s)) (GateMirror.forward (moveB s))
    (GateMirror.forward (moveC s)) (GateMirror.forward (moveKept s)) v m a0 (apart_move w1 w2) (lone_move s)
    (stillB w1 w2) (woven_move w1 w2) clean sel

theorem rowGates_proper (c : Wire) : ∀ (rs : List MoveChain.Row), (∀ r ∈ rs, r.1 ≠ c ∧ r.2 ≠ c ∧ r.1 ≠ r.2) →
    ∀ g ∈ rowGates c rs, proper g = true
  | [], _, g, hg => by simp [rowGates] at hg
  | r :: rs, sep, g, hg => by
    have hr := sep r (by simp)
    simp only [rowGates, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | hg
    · simp only [proper, decide_eq_true_eq]; exact hr.2.1
    · simp only [proper, decide_eq_true_eq]; exact ⟨hr.2.2, fun e => hr.2.1 e.symm⟩
    · simp only [proper, decide_eq_true_eq]; exact hr.2.1
    · exact rowGates_proper c rs (fun x hx => sep x (List.mem_cons_of_mem _ hx)) g hg

theorem kept_proper {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) : ∀ g ∈ moveKept s, proper g = true := by
  have cl := cell_lt w1 w2
  intro g hg
  obtain ⟨i, _, hi, rfl⟩ := mem_keptG _ _ _ _ _ g hg
  have t := tags_range i (by omega)
  simp only [proper, decide_eq_true_eq]
  constructor <;> (try unfold Wire at *) <;> omega

/-! Footprint: every operand of the move leave is an operand of the reference leave. -/

def muxG (c : Wire) (rs : List MoveChain.Row) : List Gate := rs.map (fun r => Gate.ccx r.1 r.2 c)

theorem moveMux_eq (s : Nat) : moveMux s = muxG (e0P s + 6) (moveRows s) := by
  have e : sbP s + 1580 = e0P s + 6 := by unfold e0P; omega
  unfold moveMux
  rw [← e]
  rfl

theorem allW_rowGates {P : Wire → Prop} (c : Wire) (rs : List MoveChain.Row) (h : AllW P (muxG c rs)) :
    AllW P (rowGates c rs) := by
  induction rs with
  | nil => exact allW_nil
  | cons r rs ih =>
    have hr : ∀ q ∈ (Gate.ccx r.1 r.2 c).wires, P q := h _ (by simp [muxG])
    have a : P r.1 := hr _ (by simp [Gate.wires])
    have b : P r.2 := hr _ (by simp [Gate.wires])
    have d : P c := hr _ (by simp [Gate.wires])
    have rest : AllW P (muxG c rs) := fun g hg => h g (by simp only [muxG, List.map_cons, List.mem_cons]; exact Or.inr hg)
    refine allW_cons (by simp [Gate.wires]; exact ⟨b, d⟩) (allW_cons (by simp [Gate.wires]; exact ⟨a, d, b⟩)
      (allW_cons (by simp [Gate.wires]; exact ⟨b, d⟩) (ih rest)))

theorem allW_keptG {P : Wire → Prop} (hot bank : Nat → Wire) (c d : Nat) : ∀ start n,
    AllW P (digitsG hot bank c d start n) → AllW P (keptG hot bank d start n)
  | _, 0, _ => allW_nil
  | start, n+1, h => by
    have h' : AllW P (clearG (hot start) c d (bank start) (bank (start+1)) ++ digitsG hot bank c d (start+1) n) := h
    rw [allW_append_iff] at h'
    have g2 : ∀ q ∈ (Gate.ccx (hot start) d (bank (start+1))).wires, P q := h'.1 _ (by simp [clearG])
    exact allW_cons g2 (allW_keptG hot bank c d (start+1) n h'.2)

theorem allW_leaveMove {P : Wire → Prop} (s : Nat) (h : AllW P (leaveOps s)) : AllW P (leaveMoveOps s) := by
  rw [leaveOps_shape] at h
  rw [leaveMoveOps_shape]
  simp only [allW_append_iff] at h ⊢
  obtain ⟨hA, hM, hB, hD, hC⟩ := h
  rw [moveMux_eq] at hM
  exact ⟨hA, allW_rowGates _ _ hM, hB, allW_keptG _ _ _ _ _ _ hD, hC⟩

end ECDSAAdd.Entrant.StairPacket.Partial
end

section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror Challenge
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem leaveMove_proper_of {s : Nat} (w1 : 90 ≤ s) (w2 : s ≤ 390) (p : ∀ g ∈ leaveOps s, proper g = true) :
    ∀ g ∈ leaveMoveOps s, proper g = true := by
  rw [leaveOps_shape] at p
  rw [leaveMoveOps_shape]
  intro g hg
  simp only [List.mem_append] at hg p
  rcases hg with h | h | h | h | h
  · exact p g (Or.inl h)
  · exact rowGates_proper _ _ (MoveChain.apart_sep _ _ (apart_move w1 w2)) g h
  · exact p g (Or.inr (Or.inr (Or.inl h)))
  · exact kept_proper w1 w2 g h
  · exact p g (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The move leave's mirror undoes it (c9cc6a76's `Leave{s}Mirror.invertsMove`, all blocks): `leave_inverts`'s
hypotheses plus the clean crossing wire and the one-hot tags in front of the mux, on every tape. -/
theorem leaveMove_inverts (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State)
    (phase : ∀ m, (run (leaveP j) m s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
      s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false)
    (a0 : Wire)
    (hot : ∀ o, (run (GateMirror.forward (moveA (start j))) o s).basis (e0P (start j) + 6) = false ∧
      ∀ r ∈ moveRows (start j), (run (GateMirror.forward (moveA (start j))) o s).basis r.1 = true → r.2 = a0)
    (m n : List Bool) :
    run (leaveMoveInvP j) n (run (leaveMoveP j) m s) = s := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  obtain ⟨ready, phys⟩ := leave_ready j h0 h1 s initial extra core post
  generalize hs : start j = t at *
  have same (o : List Bool) : run (GateMirror.forward (leaveMoveOps t)) o s = run (GateMirror.forward (leaveOps t)) o s :=
    leaveMove_same w1 w2 s o a0 (hot o).1 (hot o).2
  have physM : ∀ g ∈ leaveMoveOps t, proper g = true := leaveMove_proper_of w1 w2 phys
  have ready' : Ready s (moveA t ++ (moveMux t ++ (moveB t ++ (moveDig t ++ moveC t)))) := by
    rw [← leaveOps_shape]; exact ready
  have readyM : Ready s (moveA t ++ (rowGates (e0P t + 6) (moveRows t) ++ (moveB t ++ (moveKept t ++ moveC t)))) :=
    GateMirror.ready_move (e0P t + 6) (moveRows t) (moveA t) (moveB t) (moveC t) (moveMux t) (moveDig t) (moveKept t)
      s a0 (mux_forward t) (dig_forward t) (kept_plain _ _ _ _ _)
      (apart_move w1 w2) (lone_move t) (stillB w1 w2) (calmB w1 w2) (woven_move w1 w2) (hot []).1 (hot []).2 ready'
  rw [← leaveMoveOps_shape] at readyM
  have ph : ∀ o, (run (GateMirror.forward (leaveMoveOps t)) o s).phase = s.phase := by
    intro o; rw [same o]; have := phase o; rw [leaveP, hs] at this; exact this
  rw [leaveMoveP, leaveMoveInvP, hs]
  exact invert _ s physM (all_prepared _ s physM ph) readyM m n

end ECDSAAdd.Entrant.StairPacket.Partial
end


/-! par-c1: operand footprint of the leave (for par-c2's NativePack writes): every operand of every gate of
`leaveOps s` lies in `leaveBox s`, for the window blocks `j ∈ [1,21]`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The leave's wires: the A rail `s+15 .. min (s+288) 529`, the B rail `786..1043`, the scratch `1556..1812`, and the
history cells `s+1044 .. s+1058` (in the `OB5.sig (s+14)` frame the moved cells land in the scratch range). -/
def leaveBox (s q : Nat) : Prop :=
  (s+15 ≤ q ∧ q ≤ min (s+288) 529) ∨ (786 ≤ q ∧ q ≤ 1043) ∨ (1556 ≤ q ∧ q ≤ 1812) ∨ (1044+s ≤ q ∧ q < 1059+s ∧ q ≤ 1300)
def leaveBoxB (s q : Nat) : Bool :=
  (decide (s+15 ≤ q) && decide (q ≤ min (s+288) 529)) || (decide (786 ≤ q) && decide (q ≤ 1043)) ||
    (decide (1556 ≤ q) && decide (q ≤ 1812)) || (decide (1044+s ≤ q) && decide (q < 1059+s) && decide (q ≤ 1300))
theorem leaveBoxB_iff (s q : Nat) : leaveBoxB s q = true ↔ leaveBox s q := by
  unfold leaveBoxB leaveBox; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc, and_assoc]

def segBox (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => g.wires.all (leaveBoxB s))
theorem allW_of_segBox {s : Nat} {gs : List Gate} (h : segBox s gs = true) : AllW (leaveBox s) gs := by
  intro g hg q hq
  unfold segBox at h; rw [List.all_eq_true] at h
  have := h g hg; rw [List.all_eq_true] at this
  exact (leaveBoxB_iff s q).mp (this q hq)

theorem allW_iff_flat {P : Wire → Prop} {gs : List Gate} : AllW P gs ↔ ∀ q ∈ gs.flatMap Gate.wires, P q := by
  constructor
  · intro h q hq; obtain ⟨g, hg, hq⟩ := List.mem_flatMap.mp hq; exact h g hg q hq
  · intro h g hg q hq; exact h q (List.mem_flatMap.mpr ⟨g, hg, hq⟩)

theorem sig_box {s c : Nat} (h1 : 90 ≤ s) (h2 : s ≤ 390) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    leaveBox s (OB5.sig (s+14) (s+c)) := by
  have e := sig_hist h1 h2 hc1 hc2
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  unfold leaveBox; ((try unfold Wire at *); omega)

theorem fixed_box : ∀ j : Fin 23, 1 ≤ j.val → j.val ≤ 21 →
    segBox (start j) (leaveFix0 (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j)) ++
      leaveFix2 (start j) (sbP (start j)) ++ leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j)) ++ leaveFix8 (start j) (sbP (start j)) ++ leaveFix10 (start j) (sbP (start j)) ++
      leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) = true := by
  decide +kernel

theorem leaveOps_box (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    AllW (leaveBox (start j)) (leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have fb := allW_of_segBox (fixed_box j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := rail_win w1 w2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  have hL : 10 ≤ lowsP s ∧ lowsP s ≤ 11 := by ((try unfold Wire at *); omega)
  have bank : ∀ i, i < wpP s + 15 → leaveBox s (bankW s i) := by
    intro i hi; have bc := bank_cases w1 w2 hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have tags : ∀ i, i < 16 → leaveBox s (tagsP.getD i 0) := by
    intro i hi; have t := tags_range i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have aside : ∀ i, i ≤ 19 → leaveBox s (a0P s - 1 + i) := by intro i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have bside : ∀ i, i ≤ 12 → leaveBox s (b0P s - 1 + i) := by intro i hi; unfold leaveBox; ((try unfold Wire at *); omega)
  have scr : ∀ q, 1556 ≤ q → q ≤ 1812 → leaveBox s q := by intro q a b; unfold leaveBox; ((try unfold Wire at *); omega)
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1812) → ∀ x ∈ xs, leaveBox s x :=
    fun xs h x hx => scr x (h x hx).1 (h x hx).2
  have adj : AllW (leaveBox s) (leaveAdjust s) := by
    unfold leaveAdjust
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := pool_cases (i := i) w1 w2; exact scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
  have bar : AllW (leaveBox s) (leaveBarrel s) := by
    unfold leaveBarrel
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1812) →
        AllW (leaveBox s) (stageG 1613 (bankW s) xs d n) :=
      fun xs d n hn hx => allW_stageG _ _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (ctl xs hx)
        (fun i hi => ⟨bank i (by ((try unfold Wire at *); omega)), bank (i+d) (by ((try unfold Wire at *); omega))⟩)
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    refine allW_append ?_ (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
    exact allW_append (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide)) (st _ _ _ (by ((try unfold Wire at *); omega)) (by decide))
  have joi : AllW (leaveBox s) (leaveJoin s) := by
    unfold leaveJoin
    refine allW_append (allW_digitsG _ _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ _
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordG _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
    · have := aside (i+1) (by ((try unfold Wire at *); omega)); rwa [show a0P s - 1 + (i+1) = a0P s + i by ((try unfold Wire at *); omega)] at this
    · have := aside (i+2) (by ((try unfold Wire at *); omega)); rwa [show a0P s - 1 + (i+2) = a0P s + (i+1) by ((try unfold Wire at *); omega)] at this
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr; rw [List.mem_range] at hi
      refine ⟨fun w hw => ?_, ?_, bank i (by ((try unfold Wire at *); omega))⟩
      · dsimp only at hw; split at hw
        · cases hw; exact tags i (by ((try unfold Wire at *); omega))
        · cases hw
      · have := aside (i+1) (by ((try unfold Wire at *); omega)); dsimp only; rwa [show a0P s - 1 + (i+1) = a0P s + i by ((try unfold Wire at *); omega)] at this
  have lr : AllW (leaveBox s) (lowRest s) := by
    unfold lowRest
    refine allW_append (allW_append (allW_append (allW_append ?_ (allW_xsG _ ?_)) (allW_addG _ _ _ ?_ ?_ ?_))
      (allW_xsG _ ?_)) ?_
    · refine allW_map _ _ (fun i hi q hq => ?_); rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl|rfl <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    all_goals try (intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega))
    · unfold leaveBox; ((try unfold Wire at *); omega)
    · rw [allW_iff_flat]
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
  have sm : AllW (leaveBox s) (leaveStoreMapped s) := by
    simp only [leaveStoreMapped]
    have lit : ∀ (gs : List Gate), (∀ q ∈ gs.flatMap Gate.wires, leaveBox s q) → AllW (leaveBox s) gs :=
      fun gs h => allW_iff_flat.mpr h
    have hi : ∀ y ∈ (List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i)), leaveBox s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank _ (by ((try unfold Wire at *); omega))
    have s2 : ∀ y ∈ (List.range (lowsP s + 1)).map (b0P s - 1 + ·), leaveBox s y := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bside i (by ((try unfold Wire at *); omega))
    refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
      ?_ (allW_xsG _ hi)) ?_) (allW_xsG _ (fun y h => hi y (List.mem_reverse.mp h)))) ?_) (allW_xsG _ s2)) ?_)
      (allW_xsG _ (fun y h => s2 y (List.mem_reverse.mp h)))) ?_
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        have sc := storeW_cases (wpP s + 15 - lowsP s + 1)
        split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
      · have sc := storeW_cases k; unfold leaveBox; ((try unfold Wire at *); omega)
      · dsimp only; split
        · unfold leaveBox; ((try unfold Wire at *); omega)
        · exact bank _ (by ((try unfold Wire at *); omega))
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    · refine allW_chainG _ _ _ ?_ _ _ (fun k _ hk => ?_) (fun k _ hk => ?_)
      · apply lit
        simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
      · unfold leaveBox; ((try unfold Wire at *); omega)
      · unfold leaveBox; ((try unfold Wire at *); omega)
    · apply lit
      simp only [List.flatMap_cons, List.flatMap_nil, Gate.wires, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      unfold leaveBox; ((try unfold Wire at *); omega)
  have lc : AllW (leaveBox s) (leaveLowClose s) := by
    simp only [leaveLowClose]
    refine allW_append (allW_append (allW_xsG _ (fun y hy => ?_)) (allW_map _ _ (fun i hi q hq => ?_)))
      (allW_flatMap _ _ (fun i hi => allW_cswapG _ _ _ ?_ ?_ ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega)
    · rw [List.mem_range] at hi
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl|rfl <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
    all_goals (rw [List.mem_range] at hi; unfold leaveBox; ((try unfold Wire at *); omega))
  have cl : AllW (leaveBox s) (leaveClose s) := by
    unfold leaveClose
    refine allW_append (allW_eventsG _ _ _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) ?_) (allW_swapsG _ ?_)
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> dsimp only <;>
        exact ⟨sig_box w1 w2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)), scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))⟩
    · intro p hp
      unfold movesP at hp
      rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
        exact ⟨bank _ (by ((try unfold Wire at *); omega)), by unfold leaveBox; ((try unfold Wire at *); omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> unfold leaveBox <;> ((try unfold Wire at *); omega)
  rw [leaveOps_split]
  refine allW_append (allW_append ?_ (allW_append (allW_append lr sm) lc)) cl
  unfold leaveHeadOps
  refine allW_append ?_ fl; refine allW_append ?_ f12; refine allW_append ?_ f11; refine allW_append ?_ f10
  refine allW_append ?_ joi; refine allW_append ?_ f8; refine allW_append ?_ bar; refine allW_append ?_ adj
  refine allW_append ?_ f5; refine allW_append ?_ f4; refine allW_append ?_ f3; refine allW_append ?_ f2
  exact allW_append f0 f1

end ECDSAAdd.Entrant.StairPacket.Partial

end

/-! par-c1: generic leave families, batch 1 (dadon's `Leave{s}Shift/Control/Barrel/High/Join/Word`), for every
window block `j ∈ [1,21]`, over par-b's segments: barrel = `leaveBarrel`, adjust = `leaveAdjust`, join = `leaveJoin`.
The bank wire function is `bankW s` (dadon's `bank3.getD · 0` / `wire`), its width `wpP s + 15`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

/-- The bank register read by the adjust (dadon's `Leave{s}High.ys`). -/
def ys (j : Fin 23) : List Wire := (List.range (wpP (start j))).map (bankW (start j))
/-- The adjust's carry pool (dadon's `Leave{s}High.carries`). -/
def carries (j : Fin 23) : List Wire := (List.range (wpP (start j) - 1)).map (poolW (start j))
theorem tags_mem (i : Nat) (hi : i < 16) : tagsP.getD i 0 ∈ tagsP := by
  rw [List.getD_eq_getElem _ _ (show i < tagsP.length by simp [tagsP]; omega)]; exact List.getElem_mem _
theorem tags_range' : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide

theorem layout (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : HighBankShift.Layout 1613 (bankW (start j)) (wpP (start j) + 15) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  refine ⟨fun i hi k hk e => bank_inj w1 w2 hi hk e, fun i hi e => ?_⟩
  have r := rail_win w1 w2; have b := bank_cases w1 w2 hi
  unfold wpP bTopP e0P at *; unfold Wire at *; omega

/-! Control: the one-hot tag parity selects the key bits (constant lists, decided once). -/

theorem selection0 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP0 = key.val.testBit 0 := by
  revert key; decide +kernel
theorem selection1 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP1 = key.val.testBit 1 := by
  revert key; decide +kernel
theorem selection2 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP2 = key.val.testBit 2 := by
  revert key; decide +kernel
theorem selection3 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP3 = key.val.testBit 3 := by
  revert key; decide +kernel

theorem controls_range : ∀ xs ∈ [controlsP0, controlsP1, controlsP2, controlsP3], 1613 ∉ xs ∧
    (∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ xs, q ∈ tagsP := by decide +kernel

theorem controls_out (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (xs : List Wire) (hx : ∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) :
    ∀ q ∈ xs, HighBankBarrel.outside (bankW (start j)) (wpP (start j) + 15) q := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  intro q hq i hi e
  have r := rail_win w1 w2; have b := bank_cases w1 w2 hi; have := hx q hq
  unfold wpP bTopP e0P at *; unfold Wire at *; omega

/-! Barrel: four stages shift the bank by the key (dadon's `Leave{s}Barrel.value`). -/

theorem barrel_shape (s : Nat) : GateMirror.forward (leaveBarrel s) =
    HighBankBarrel.stage 1613 (bankW s) controlsP0 1 (wpP s) ++ HighBankBarrel.stage 1613 (bankW s) controlsP1 2 (wpP s + 1) ++
    HighBankBarrel.stage 1613 (bankW s) controlsP2 4 (wpP s + 3) ++ HighBankBarrel.stage 1613 (bankW s) controlsP3 8 (wpP s + 7) := by
  simp only [leaveBarrel, forward_app, forward_stageG]

/-- dadon's `Leave{s}BarrelBits.byDigits`: the four stages shift by the key read from the control parities. -/
theorem barrel_bits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^(wpP (start j))) (h : HighBankBarrel.holds (bankW (start j)) (wpP (start j) + 15) x s) (clean : s.basis 1613 = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< key.val) s (run (GateMirror.forward (leaveBarrel (start j))) m s) := by
  rw [barrel_shape]
  have L := layout j h0 h1
  obtain ⟨c0, c1, c2, c3⟩ : (1613 ∉ controlsP0 ∧ (∀ q ∈ controlsP0, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP0, q ∈ tagsP) ∧
      (1613 ∉ controlsP1 ∧ (∀ q ∈ controlsP1, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP1, q ∈ tagsP) ∧
      (1613 ∉ controlsP2 ∧ (∀ q ∈ controlsP2, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP2, q ∈ tagsP) ∧
      (1613 ∉ controlsP3 ∧ (∀ q ∈ controlsP3, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP3, q ∈ tagsP) :=
    ⟨controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp)⟩
  have beginPass : ∀ m, HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< 0) s (run [] m s) := HighBankBarrel.start h
  have p1 : ∀ m, HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< (key.val % 2)) s
      (run ([] ++ HighBankBarrel.stage 1613 (bankW (start j)) controlsP0 1 (wpP (start j))) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c0.1 (controls_out j h0 h1 _ c0.2.1) clean
      (HighBankBarrel.room small (by omega)) _ beginPass
    rw [bit0]
    exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< (key.val % 4)) s
      (run ([] ++ HighBankBarrel.stage 1613 (bankW (start j)) controlsP0 1 (wpP (start j)) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP1 2 (wpP (start j) + 1)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c1.1 (controls_out j h0 h1 _ c1.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 2 by decide); omega)) _ p1
    rw [bit1]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< (key.val % 8)) s
      (run ([] ++ HighBankBarrel.stage 1613 (bankW (start j)) controlsP0 1 (wpP (start j)) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP1 2 (wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP2 4 (wpP (start j) + 3)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c2.1 (controls_out j h0 h1 _ c2.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 4 by decide); omega)) _ p2
    rw [bit2]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< key.val) s
      (run ([] ++ HighBankBarrel.stage 1613 (bankW (start j)) controlsP0 1 (wpP (start j)) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP1 2 (wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP2 4 (wpP (start j) + 3) ++
        HighBankBarrel.stage 1613 (bankW (start j)) controlsP3 8 (wpP (start j) + 7)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c3.1 (controls_out j h0 h1 _ c3.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 8 by decide); omega)) _ p3
    rw [bit3]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  simpa only [List.nil_append] using p4 m

theorem controls_tags : (∀ q ∈ controlsP0, q ∈ tagsP) ∧ (∀ q ∈ controlsP1, q ∈ tagsP) ∧ (∀ q ∈ controlsP2, q ∈ tagsP) ∧
    (∀ q ∈ controlsP3, q ∈ tagsP) := by decide +kernel

/-- dadon's `Leave{s}Barrel.value`. -/
theorem barrel_value (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^(wpP (start j))) (h : HighBankBarrel.holds (bankW (start j)) (wpP (start j) + 15) x s) (clean : s.basis 1613 = false)
    (tags : ∀ q ∈ tagsP, s.basis q = decide (q = tagsP.getD key 0)) :
    HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< key.val) s (run (GateMirror.forward (leaveBarrel (start j))) m s) := by
  have par : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity s.basis xs = HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => tags q (hx q hq))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  exact barrel_bits j h0 h1 key x s m small h clean ((par _ t0).trans (selection0 key)) ((par _ t1).trans (selection1 key))
    ((par _ t2).trans (selection2 key)) ((par _ t3).trans (selection3 key))

/-! High: the adjust then the barrel (dadon's `Leave{s}High.result`). -/

theorem ys_length (j : Fin 23) : (ys j).length = wpP (start j) := by simp [ys]
theorem ys_getD (j : Fin 23) (i : Nat) (hi : i < wpP (start j)) : (ys j).getD i 0 = bankW (start j) i := by
  simp [ys, List.getD_eq_getElem?_getD, hi]

theorem adjust_nodup (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ((e0P (start j) + 6) :: (ys j ++ carries j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, ?_, pool_nodup _ _ w1 w2, ?_⟩
  · intro hm; rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have b := bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have p := pool_cases (i := i) w1 w2; unfold Wire at *; omega
  · exact List.Nodup.map_on (fun a ha b hb e => bank_inj w1 w2 (by rw [List.mem_range] at ha; omega)
      (by rw [List.mem_range] at hb; omega) e) List.nodup_range
  · intro a ha b hb e
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hi hk
    have bb := bank_cases w1 w2 (i := i) (by omega); have p := pool_cases (i := k) w1 w2
    unfold Wire at *; omega

theorem high_bits (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, wpP (start j) ≤ i → i < wpP (start j) + 15 → s.basis (bankW (start j) i) = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (leaveAdjust (start j) ++ leaveBarrel (start j))) m s) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  let p := HighBankAdjust.adjust (ys j) (carries j) (e0P (start j) + 6) 1597
  have pe : GateMirror.forward (leaveAdjust (start j)) = p := by
    simp only [leaveAdjust, forward_adjustG, p, ys, carries]
  let t := run p m s
  let x := regValue (ys j) t.basis
  have negOut : (1597:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have size : (carries j).length + 1 = (ys j).length := by simp [ys, carries]; omega
  have ht := HighBankAdjust.correct (ys j) (carries j) (e0P (start j) + 6) 1597 (adjust_nodup j h0 h1) negOut size s m clean
  have small : x < 2^(wpP (start j)) := by have := regValue_lt (ys j) t.basis; rwa [ys_length] at this
  have notYs : ∀ i, wpP (start j) ≤ i → i < wpP (start j) + 15 → bankW (start j) i ∉ ys j := by
    intro i a b hm; obtain ⟨k, hk, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hk
    have := bank_inj w1 w2 (i := k) (k := i) (by omega) b e; omega
  have data : HighBankBarrel.holds (bankW (start j)) (wpP (start j) + 15) x t := by
    intro i hi
    by_cases lo : i < wpP (start j)
    · rw [← ys_getD j i lo]
      exact HighBankAdjust.bit_read (ys j) i t.basis (by rw [ys_length]; exact lo)
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (notYs i (by omega) hi)).trans (padding i (by omega) hi)
  have t1613 : (1613:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have cold : t.basis 1613 = false := (ht.2.1 _ t1613).trans selectZero
  have untouched : ∀ q ∈ tagsP, q ∉ ys j := by
    intro q hq hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := bank_cases w1 w2 (i := i) (by omega)
    have tr := tags_range' q hq
    unfold Wire at *; omega
  have same : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity t.basis xs = HighBankControl.parity s.basis xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => ht.2.1 q (untouched q (hx q hq)))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have action := barrel_bits j h0 h1 key x t (m.drop (measurementCount p)) small data cold
    ((same _ t0).trans bit0) ((same _ t1).trans bit1) ((same _ t2).trans bit2) ((same _ t3).trans bit3)
  have initial : x = HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6))
      (s.basis 1597) := by rw [← ys_length j]; exact ht.2.2
  dsimp only
  rw [forward_app, pe, run_append, run_take, ← initial]
  refine ⟨action.bits, action.phase.trans ht.1, fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i, hi, e⟩ := List.mem_map.mp member; rw [List.mem_range] at hi
  exact h i (by omega) e.symm

/-- dadon's `Leave{s}High.result`. -/
theorem high_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, wpP (start j) ≤ i → i < wpP (start j) + 15 → s.basis (bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = decide (q = tagsP.getD key 0)) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (leaveAdjust (start j) ++ leaveBarrel (start j))) m s) := by
  have par : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity s.basis xs = HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => one q (hx q hq))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  exact high_bits j h0 h1 key s m clean selectZero padding ((par _ t0).trans (selection0 key))
    ((par _ t1).trans (selection1 key)) ((par _ t2).trans (selection2 key)) ((par _ t3).trans (selection3 key))

/-- dadon's `Leave{s}NearHigh.result`: all tags off, no shift. -/
theorem nearHigh_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, wpP (start j) ≤ i → i < wpP (start j) + 15 → s.basis (bankW (start j) i) = false)
    (off : ∀ q ∈ tagsP, s.basis q = false) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6)) (s.basis 1597)
    HighBankBarrel.Result (bankW (start j)) (wpP (start j) + 15) x s
      (run (GateMirror.forward (leaveAdjust (start j) ++ leaveBarrel (start j))) m s) := by
  have quiet : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) → HighBankControl.parity s.basis xs = false := by
    intro xs sub
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [HighBankControl.parity, off q (sub _ (by simp)), Bool.false_xor,
        ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have h := high_bits j h0 h1 0 s m clean selectZero padding (quiet _ t0) (quiet _ t1) (quiet _ t2) (quiet _ t3)
  simpa only [Fin.val_zero, Nat.shiftLeft_zero] using h

/-! Join and Word: the digit pass and the word reassembly (dadon's `Leave{s}Join` / `Leave{s}Word.combine`). -/

def hot (key : Fin 16) (q : Wire) := decide (q = tagsP.getD key 0)
abbrev cols (j : Fin 23) : List Column := columnsP (start j)
theorem cols_length (j : Fin 23) : (cols j).length = 18 := by simp [cols, columnsP]
/-- dadon's `Leave{s}Word.row`. -/
abbrev row (j : Fin 23) (i : Fin 18) : Column := (cols j)[i.val]'(by rw [cols_length]; exact i.isLt)

theorem row_eq (j : Fin 23) (i : Fin 18) : (row j i).shadow = a0P (start j) + i.val ∧ (row j i).tube = bankW (start j) i.val ∧
    (row j i).low = decide (i.val < lowsP (start j)) ∧ (row j i).hot = if i.val < 16 then some (tagsP.getD i.val 0) else none := by
  simp [row, cols, columnsP]

/-- The schedule only reads the `hot` fields (identical at every block). -/
theorem schedule_hot (ref : BasisState) (key : Nat) : ∀ (a : Bool) (k : Nat) (rs rs' : List Column),
    rs.map (·.hot) = rs'.map (·.hot) → schedule ref key a k rs = schedule ref key a k rs'
  | _, _, [], [], _ => rfl
  | _, _, [], _::_, h => by simp at h
  | _, _, _::_, [], h => by simp at h
  | a, k, r::rs, r'::rs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [schedule, h.1, schedule_hot ref key _ (k+1) rs rs' h.2]

theorem hots (j : Fin 23) : (cols j).map (·.hot) = (columnsP 225).map (·.hot) := by
  simp only [cols, columnsP, List.map_map]; rfl

theorem schedule_ok (j : Fin 23) (key : Fin 16) : schedule (hot key) key false 0 (cols j) = true := by
  rw [schedule_hot _ _ _ _ _ (columnsP 225) (hots j)]
  revert key; decide +kernel

theorem digitSites (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    DigitLayout (tagsP.getD · 0) (fun i => a0P (start j) + i) (e0P (start j) + 6) 1613 0 16 := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  refine ⟨fun i _ hi => ?_, fun i _ hi k _ hk => ?_⟩
  · have t := tags_range' _ (tags_mem i hi)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · have t := tags_range' _ (tags_mem i hi); unfold Wire at *; omega

theorem colSites (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : WellPlaced 1614 (cols j) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  refine ⟨fun c hc => ?_, fun c hc h hh => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have b := bank_cases w1 w2 (i := i) (by omega)
    dsimp only
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have th : 1556 ≤ h ∧ h ≤ 1576 := by
      simp only at hh; split at hh
      · simp only [Option.mem_def, Option.some.injEq] at hh; subst hh; exact tags_range' _ (tags_mem i (by omega))
      · simp at hh
    refine ⟨by unfold Wire at *; omega, fun v hv => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv; rw [List.mem_range] at hk
    have b := bank_cases w1 w2 (i := k) (by omega)
    dsimp only; unfold Wire at *; omega

theorem disjoint (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : (cols j).Pairwise Apart := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  unfold cols columnsP
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) (List.pairwise_lt_range (n := 18))
  rw [List.mem_range] at ha hb
  have ba := bank_cases w1 w2 (i := a) (by omega); have bb := bank_cases w1 w2 (i := b) (by omega)
  have ne : bankW (start j) a ≠ bankW (start j) b := fun e => by have := bank_inj w1 w2 (by omega) (by omega) e; omega
  unfold Apart; dsimp only
  refine ⟨?_, ?_, ?_, ne⟩ <;> unfold Wire at * <;> omega

theorem join_shape (s : Nat) : GateMirror.forward (leaveJoin s) =
    digits (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16 ++ word 1614 (columnsP s) := by
  simp only [leaveJoin, forward_app, forward_digitsG, forward_wordG]

theorem combine (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 18, s.basis (bankW (start j) i) = (2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis (e0P (start j) + 6)).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  let ref := hot key
  let dp := digits (tagsP.getD · 0) (fun i => a0P (start j) + i) (e0P (start j) + 6) 1613 0 16
  let u := run dp m s
  have unique : ∀ i t : Fin 16, hot t (tagsP.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i < 0+16) : s.basis (tagsP.getD i 0) = decide (i = key.val) :=
    (tagsOn _ (tags_mem i hi)).trans (unique ⟨i, hi⟩ key)
  have z := digits_remainder (digitSites j h0 h1) s m key.val (by omega) key.isLt sel X 18 (by decide)
    (fun i _ k _ eq => Nat.add_left_cancel eq) shadow digit
  have hits : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have members : ∀ q ∈ tagsP, ∀ i : Nat, i ≤ 17 → q ≠ a0P (start j) + i := by
    intro q hq i hi; have := tags_range' q hq; unfold Wire at *; omega
  have ctrl : ∀ c ∈ cols j, ∀ q ∈ c.hot, u.basis q = ref q := by
    intro c hc q hq
    have mem := hits c hc q hq
    exact (z.2.2 q (members q mem key.val (by omega)) (members q mem (key.val+1) (by omega))).trans (tagsOn q mem)
  have inputs : columnsRead (cols j) u.basis X H key.val 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change u.basis (row j ⟨i, hi⟩).shadow = _ ∧ u.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.zero_add]
    have b := bank_cases w1 w2 (i := i) (by omega)
    refine ⟨z.2.1 i hi, (z.2.2 _ ?_ ?_).trans (tube i hi)⟩ <;> unfold Wire at * <;> omega
  have rz : u.basis 1614 = false := (z.2.2 _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans scratch
  have word := reassemble 1614 (cols j) ref u m X H key.val (colSites j h0 h1) (disjoint j h0 h1) ctrl rz
    (schedule_ok j key) inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero]
  refine ⟨word.1.trans z.1, fun i => word.2.1 i.val (by rw [cols_length]; exact i.isLt), ?_⟩
  intro q away
  have safe (k : Nat) (hk : k < 18) : q ≠ a0P (start j) + k := by
    have g := row_eq j ⟨k, hk⟩
    rw [← g.1]
    exact (away _ (List.getElem_mem _)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe key.val (by omega)) (safe (key.val+1) (by omega)))



/-- dadon's `Leave{s}NearWord.combine`: no tag hot, the word passes the shadows through. -/
theorem nearWord_combine (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (X : Nat) (bound : X < 2^18) (s : State)
    (m : List Bool) (off : ∀ q ∈ tagsP, s.basis q = false)
    (shadow : ∀ i < 18, s.basis (a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 18, s.basis (bankW (start j) i) = false)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = X.testBit i.val ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  let ref : BasisState := fun _ => false
  let dp := digits (tagsP.getD · 0) (fun i => a0P (start j) + i) (e0P (start j) + 6) 1613 0 16
  have none : run dp m s = s := by
    apply digits_quiet (digitSites j h0 h1)
    intro i _ hi
    exact off _ (tags_mem i hi)
  have sch : schedule ref 18 false 0 (cols j) = true := by
    rw [schedule_hot _ _ _ _ _ (columnsP 225) (hots j)]; decide +kernel
  have members : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have inputs : columnsRead (cols j) s.basis X 0 18 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change s.basis (row j ⟨i, hi⟩).shadow = _ ∧ s.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.mod_eq_of_lt bound, Nat.zero_add, Nat.mul_zero, Nat.zero_testBit]
    exact ⟨shadow i hi, tube i hi⟩
  have v := reassemble 1614 (cols j) ref s m X 0 18 (colSites j h0 h1) (disjoint j h0 h1)
    (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero, none]
  refine ⟨v.1, fun i => ?_, v.2.2⟩
  have hv := v.2.1 i.val (by rw [cols_length]; exact i.isLt)
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt bound] using hv

/-! Middle: adjust, barrel, sign bit, join (dadon's `Leave{s}Middle.result`; `middle` = cuts 8..24). -/

def middleOps (s : Nat) : List Gate := leaveAdjust s ++ leaveBarrel s ++ leaveFix8 s (sbP s) ++ leaveJoin s
theorem fix8_forward (s h : Nat) : GateMirror.forward (leaveFix8 s h) = [.X 1613, .CX 1597 1613] := rfl

theorem middle_result (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, wpP (start j) ≤ i → i < wpP (start j) + 15 → s.basis (bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (a0P (start j) + i) = X.testBit i)
    (digit : X/2^key.val = (s.basis (e0P (start j) + 6)).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614 = false) :
    let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6)) (s.basis 1597)
    let out := run (GateMirror.forward (middleOps (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 18, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      (∀ i : Nat, 18 ≤ i → i < wpP (start j) + 15 → out.basis (bankW (start j) i) = (2^key.val*H).testBit i) ∧
      (∀ q, q ≠ 1613 → HighBankBarrel.outside (bankW (start j)) (wpP (start j) + 15) q → (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) →
        out.basis q = s.basis q) := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  have r := rail_win w1 w2
  let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (wpP (start j)) (s.basis (e0P (start j) + 6)) (s.basis 1597)
  let early := GateMirror.forward (leaveAdjust (start j) ++ leaveBarrel (start j))
  let signBit : Program := [.X 1613, .CX 1597 1613]
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := high_result j h0 h1 key s m clean selectZero padding one
  have bits (i : Nat) (hi : i < wpP (start j) + 15) : v.basis (bankW (start j) i) = (2^key.val*H).testBit i := by
    rw [Nat.mul_comm (2^key.val) H, ← Nat.shiftLeft_eq]
    exact a.bits i hi
  have unchanged (q : Wire) (ne : q ≠ 1613) : u.basis q = v.basis q := by simp [u, signBit, run, writeBit, Function.update, ne]
  have old (q : Wire) (ne : q ≠ 1613) (ext : HighBankBarrel.outside (bankW (start j)) (wpP (start j) + 15) q) : u.basis q = s.basis q :=
    (unchanged q ne).trans (a.frame q ext)
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) ∨ (e0P (start j) + 3 ≤ q ∧ q ≤ e0P (start j) + 9) →
      HighBankBarrel.outside (bankW (start j)) (wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := bank_cases w1 w2 hi
    unfold Wire at *; omega
  have stable : ∀ i, i < wpP (start j) + 15 → (1613:Wire) ≠ bankW (start j) i := fun i hi => (layout j h0 h1).separate i hi
  have readTags (q : Wire) (hq : q ∈ tagsP) : u.basis q = hot key q := by
    have t := tags_range' q hq
    exact (old q (by unfold Wire at *; omega) (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (one q hq)
  have readShadow (i : Nat) (hi : i < 18) : u.basis (a0P (start j) + i) = X.testBit i :=
    (old _ (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inl (by omega))))).trans (shadow i hi)
  have readTube (i : Nat) (hi : i < 18) : u.basis (bankW (start j) i) = (2^key.val*H).testBit i :=
    (unchanged _ (stable i (by omega)).symm).trans (bits i (by omega))
  have select : v.basis 1613 = false := (a.frame _ (layout j h0 h1).separate).trans selectZero
  have neg : v.basis 1597 = s.basis 1597 := a.frame _ (bankOut 1597 (Or.inl (by omega)))
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u, signBit, run, writeBit, Function.update, select, neg]
  have cross := old (e0P (start j) + 6) (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inr (by omega))))
  have zero := (old 1614 (by decide) (fun i hi e => by
    have b := bank_cases w1 w2 hi; unfold Wire at *; omega)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis (e0P (start j) + 6)).toNat + 2*(u.basis 1613).toNat := by
    rw [cross, d1]; exact digit
  have word := combine j h0 h1 key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  have parts : GateMirror.forward (middleOps (start j)) = early ++ (signBit ++ GateMirror.forward (leaveJoin (start j))) := by
    simp only [middleOps, early, signBit, forward_app, fix8_forward, List.append_assoc]
  rw [parts, run_append, run_take, run_append, run_take, show measurementCount signBit = 0 from rfl, List.drop_zero]
  refine ⟨word.1.trans a.phase, word.2.1, ?_, ?_⟩
  · intro i lo hi
    have outsideRows : ∀ c ∈ cols j, bankW (start j) i ≠ c.shadow ∧ bankW (start j) i ≠ c.tube := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      have b := bank_cases w1 w2 hi
      refine ⟨by dsimp only; unfold Wire at *; omega, fun e => ?_⟩
      have := bank_inj w1 w2 hi (by omega) e; omega
    exact (word.2.2 _ outsideRows).trans ((unchanged _ (stable i hi).symm).trans (bits i hi))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ==== w4: step 9: par-b footprints ParB_foot2 + ParB_archfoot (build-w4b enabler BFoot) ====
/-! build-w4b ENABLER: par-b footprints helpers/par-b/ParB_foot2.lean + ParB_archfoot.lean (portal/enter/park/archive/exit wires), on the record. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! par-b on top of par-c1's `AllW` (Foot section): portal gadgets, programs, and the footprints of the portal,
enter and park, generic in the tick. `footP s q`: `q ∈ [s+15, s+15+R] ∪ [786, 785+R] ∪ [s+1044, 1300] ∪ [1556, 1812]`
with `R = railP s` (also holds for every leave wire, blocks 90..390, and portals 90..405, checked against the emitter). -/

def footP (s q : Nat) : Prop :=
  (s+15 ≤ q ∧ q ≤ s+15+railP s) ∨ (786 ≤ q ∧ q ≤ 785+railP s) ∨ (s+1044 ≤ q ∧ q ≤ 1300) ∨ (1556 ≤ q ∧ q ≤ 1812)
/-- Park and stock-form exit flags sit just above the B rail: `[786, 788+R] ∪ [1556, 1812]`. -/
def parkFootP (e q : Nat) : Prop := (786 ≤ q ∧ q ≤ 788+railP e) ∨ (1556 ≤ q ∧ q ≤ 1812)

/-- Footprints of the ops are footprints of both programs. -/
theorem allW_programs {P : Wire → Prop} {ops : List Gate} (h : AllW P ops) :
    (∀ q ∈ wires (GateMirror.forward ops), P q) ∧ (∀ q ∈ wires (inverse ops), P q) := by
  constructor
  · induction ops with
    | nil => intro q hq; simp [GateMirror.forward, wires] at hq
    | cons g gs ih =>
      intro q hq
      rw [forward_cons] at hq
      simp only [wires, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have hg := h g List.mem_cons_self
        cases g <;> simp [front, erase, Instr.wires, correctionWires, Gate.wires] at hq hg <;>
          rcases hq with h1 | h1 | h1 <;> simp_all
      · exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) q hq
  · rw [inverse, wires_reverse]
    induction ops with
    | nil => intro q hq; simp [wires] at hq
    | cons g gs ih =>
      intro q hq
      simp only [List.map_cons, wires, Finset.mem_union] at hq
      rcases hq with hq | hq
      · have hg := h g List.mem_cons_self
        cases g <;> simp [back, erase, Instr.wires, correctionWires, Gate.wires] at hq hg <;>
          rcases hq with h1 | h1 | h1 <;> simp_all
      · exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) q hq

theorem allW_exchangeG {P : Wire → Prop} (c : Wire) (ps : List (Wire × Wire)) (hc : P c)
    (h : ∀ p ∈ ps, P p.1 ∧ P p.2) : AllW P (exchangeG c ps) :=
  allW_flatMap _ ps (fun p hp g hg q hq => by
    obtain ⟨h1, h2⟩ := h p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption)
theorem allW_transferG {P : Wire → Prop} (ps : List (Wire × Wire)) (h : ∀ p ∈ ps, P p.1 ∧ P p.2) :
    AllW P (transferG ps) :=
  allW_flatMap _ ps (fun p hp g hg q hq => by
    obtain ⟨h1, h2⟩ := h p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> assumption)
theorem allW_latchChainG {P : Wire → Prop} (e : Option Wire) (out : Wire) (he : ∀ w, e = some w → P w) (ho : P out) :
    ∀ (a : Wire) (ps : List (Wire × Wire)), P a → (∀ p ∈ ps, P p.1 ∧ P p.2) → AllW P (latchChainG e out a ps)
  | a, [], ha, _ => by
    cases e with
    | none =>
      intro g hg q hq
      simp only [latchChainG, targetG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        rcases hq with rfl | rfl <;> assumption
    | some w =>
      have hw := he w rfl
      intro g hg q hq
      simp only [latchChainG, targetG, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
        rcases hq with rfl | rfl | rfl <;> assumption
  | a, (x,t)::ps, ha, hp => by
    obtain ⟨hx, ht⟩ := hp (x,t) List.mem_cons_self
    have ih := allW_latchChainG e out he ho t ps ht (fun p h => hp p (List.mem_cons_of_mem _ h))
    have e1 : latchChainG e out a ((x,t)::ps) = .make a x t :: (latchChainG e out t ps ++ [.pop a x t]) := rfl
    rw [e1]
    refine allW_cons ?_ (allW_append ih (allW_cons ?_ allW_nil)) <;> intro q hq <;>
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> rcases hq with rfl | rfl | rfl <;>
      assumption
theorem allW_latchG {P : Wire → Prop} (rev : Bool) (e : Option Wire) (out a : Wire) (ps : List (Wire × Wire))
    (he : ∀ w, e = some w → P w) (ho : P out) (ha : P a) (hp : ∀ p ∈ ps, P p.1 ∧ P p.2) :
    AllW P (latchG rev e out a ps) := by
  have hds : ∀ x ∈ a :: ps.map Prod.fst, P x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx; exact (hp p hp').1
  refine allW_append (allW_xsG _ hds) (allW_append (allW_latchChainG e out he ho a ps ha hp) (allW_xsG _ ?_))
  cases rev
  · exact hds
  · intro x hx; exact hds x (List.mem_reverse.mp hx)

theorem foot_hist (s q : Nat) (hs : s ≤ 405) (h1 : s+1044 ≤ q) (h2 : q ≤ s+1058) : footP s (OB5.sig (s+14) q) := by
  show footP s (if (1301 ≤ q ∧ q ≤ 1044+(s+14)) ∨ (2069 ≤ q+(s+14) ∧ q ≤ 1812) then 3113-q else q)
  by_cases hq : 1301 ≤ q
  · rw [if_pos (Or.inl ⟨hq, by omega⟩)]; unfold footP; right; right; right; constructor <;> omega
  · rw [if_neg (by omega)]; unfold footP; right; right; left; constructor <;> omega

/-! Footprints. -/

theorem portal_foot (t : Nat) (h0 : 90 ≤ t) (h1 : t ≤ 405) : AllW (footP t) (portalOps t) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts t h0 h1
  have hw : wpP t = railP t - sbP t - 16 := rfl
  have he : e0P t = 1574 + sbP t := rfl
  have hb : bTopP t = 785 + railP t := rfl
  have ha : a0P t = t + sbP t + 32 := rfl
  have pA : ∀ i, i < wpP t → footP t (a0P t + i) := by intro i hi; unfold footP; omega
  have pB : ∀ i, i < wpP t → footP t (802 + sbP t + i) := by intro i hi; unfold footP; omega
  have pC : ∀ i, i ≤ 250 → footP t (1556 + i) := by intro i hi; unfold footP; omega
  have pE : ∀ k, k ≤ 9 → footP t (e0P t + k) := by intro k hk; unfold footP; omega
  have pG : footP t (t+15) := by unfold footP; omega
  have pT : footP t (bTopP t) := by unfold footP; omega
  have pAt : footP t (a0P t + wpP t - 1) := by unfold footP; omega
  have mA : ∀ x ∈ (List.range (wpP t)).map (a0P t + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact pA i (List.mem_range.mp hi)
  have mB : ∀ x ∈ (List.range (wpP t)).map (802 + sbP t + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact pB i (List.mem_range.mp hi)
  have mA3 : ∀ x ∈ (List.range (wpP t - 3)).map (a0P t + 3 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show a0P t + 3 + i = a0P t + (3+i) by omega]; exact pA _ (by omega)
  have mB3 : ∀ x ∈ (List.range (wpP t - 3)).map (802 + sbP t + 3 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show 802 + sbP t + 3 + i = 802 + sbP t + (3+i) by omega]; exact pB _ (by omega)
  have zip : ∀ (l1 l2 : List Wire), (∀ x ∈ l1, footP t x) → (∀ x ∈ l2, footP t x) →
      ∀ p ∈ l1.zip l2, footP t p.1 ∧ footP t p.2 := by
    intro l1 l2 h1 h2 p hp; exact ⟨h1 _ (List.of_mem_zip hp).1, h2 _ (List.of_mem_zip hp).2⟩
  have thr : ∀ p ∈ (List.range (wpP t - 2)).map (fun i => (a0P t + 2 + i, 1558 + i)), footP t p.1 ∧ footP t p.2 := by
    intro p hp; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; have := List.mem_range.mp hi
    exact ⟨by rw [show a0P t + 2 + i = a0P t + (2+i) by omega]; exact pA _ (by omega),
      by rw [show 1558 + i = 1556 + (2+i) by omega]; exact pC _ (by omega)⟩
  have ori : ∀ p ∈ (List.range (wpP t - 1)).map (fun i => (802 + sbP t + 1 + i, 1556 + i)),
      footP t p.1 ∧ footP t p.2 := by
    intro p hp; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; have := List.mem_range.mp hi
    exact ⟨by rw [show 802 + sbP t + 1 + i = 802 + sbP t + (1+i) by omega]; exact pB _ (by omega), pC _ (by omega)⟩
  have car : ∀ x ∈ (List.range (wpP t - 4)).map (1557 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show 1557 + i = 1556 + (1+i) by omega]; exact pC _ (by omega)
  have p0 : footP t (a0P t) := by have := pA 0 (by omega); simpa using this
  have p1 : footP t (a0P t + 1) := pA 1 (by omega)
  have p2 : footP t (a0P t + 2) := pA 2 (by omega)
  have q0 : footP t (802 + sbP t) := by have := pB 0 (by omega); simpa using this
  have q1 : footP t (802 + sbP t + 1) := pB 1 (by omega)
  have q2 : footP t (802 + sbP t + 2) := pB 2 (by omega)
  have c56 : footP t 1556 := by have := pC 0 (by omega); simpa using this
  have c57 : footP t 1557 := pC 1 (by omega)
  have e3 : footP t (e0P t + 3) := pE 3 (by omega)
  have e4 : footP t (e0P t + 4) := pE 4 (by omega)
  have e5 : footP t (e0P t + 5) := pE 5 (by omega)
  unfold portalOps
  refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append
    (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_) ?_
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> assumption
  · exact allW_exchangeG _ _ pG (zip _ _ mA mB)
  · exact allW_cxsG _ _ e5 mB
  · refine allW_cons ?_ allW_nil
    intro q hq; simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_latchG _ _ _ _ _ (fun w h => by cases h) c56 c57 thr
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_latchG _ _ _ _ _ (fun w h => by cases h; exact e3) e4 q0 ori
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_addG _ _ _ mB3 car c56
  · exact allW_map _ _ (fun p hp q hq => by
      obtain ⟨h1, h2⟩ := zip _ _ mA3 mB3 p hp
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> assumption)
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl | rfl <;> assumption
  · exact allW_transferG _ (zip _ _ mA3 mB3)
  · refine allW_cxsG _ _ e5 ?_
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · refine allW_exchangeG _ _ pG ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by assumption, by assumption⟩

theorem park_foot (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) : AllW (parkFootP e) (parkOps e) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts e h0 h1
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  apply allW_swapsG
  intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> unfold parkFootP <;> omega

theorem enter_foot (s : Nat) (h0 : 90 ≤ s) (h1 : s ≤ 405) : AllW (footP s) (enterOps s) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix AllW
  simp only [List.forall_mem_cons, List.forall_mem_nil, Gate.wires, and_true, implies_true]
  and_intros <;> first | (intro x hx; cases hx) | (unfold footP; omega)
theorem enter_wires (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 22) :
    (∀ q ∈ wires (enterP j), footP (start j) q) ∧ (∀ q ∈ wires (enterInvP j), footP (start j) q) :=
  allW_programs (enter_foot (start j) (by simp [start]; omega) (by simp [start]; omega))

/-- Wires of the parametric programs (portal, park), for `Covered`. -/
theorem portal_wires (t : Nat) (h0 : 90 ≤ t) (h1 : t ≤ 405) :
    (∀ q ∈ wires (portalP t), footP t q) ∧ (∀ q ∈ wires (portalInvP t), footP t q) :=
  allW_programs (portal_foot t h0 h1)
theorem park_wires (e : Nat) (h0 : 90 ≤ e) (h1 : e ≤ 405) :
    (∀ q ∈ wires (parkP e), parkFootP e q) ∧ (∀ q ∈ wires (parkInvP e), parkFootP e q) :=
  allW_programs (park_foot e h0 h1)

end ECDSAAdd.Entrant.StairPacket.Partial

end


section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror MappedCompressed StairArchiveGates
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! Archive footprints, generic in the archive tick `t`. The codec programs use ports `0..154` (load) and `0..149`
(restore) (one decide per codec program); renamed through the port lists they land in
`archFootP t f q`: `q ∈ [t+6, t+15] ∪ [t+1034, 1300] ∪ [1556, 1812] ∪ [f, f+2] ∪ [1302-t, 933]` (`f` = first flag
wire; the last interval holds the scratch ports beyond the stock carry, on released B-rail wires, from tick 369). -/

def archFootP (t f q : Nat) : Prop :=
  (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ 1300) ∨ (1556 ≤ q ∧ q ≤ 1812) ∨ (f ≤ q ∧ q ≤ f+2) ∨
  (369 ≤ t ∧ 1302 ≤ q+t ∧ q ≤ 933)

def corrWiresL : Correction → List Wire
  | .Z t => [t]
  | .CZ a b => [a, b]
def instrWiresL : Instr → List Wire
  | .X t => [t]
  | .CX a t => [a, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c0 c1 => t :: ((c0 ++ c1).flatMap corrWiresL)

theorem mem_correctionWires {q : Wire} : ∀ {cs : List Correction}, q ∈ correctionWires cs → q ∈ cs.flatMap corrWiresL
  | [], h => by simp [correctionWires] at h
  | .Z t :: cs, h => by
    simp only [correctionWires, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with rfl | h
    · simp [corrWiresL]
    · exact List.mem_append_right _ (mem_correctionWires h)
  | .CZ a b :: cs, h => by
    simp only [correctionWires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (rfl | rfl) | h
    · simp [corrWiresL]
    · simp [corrWiresL]
    · exact List.mem_append_right _ (mem_correctionWires h)
theorem mem_instrWires {q : Wire} {i : Instr} (h : q ∈ i.wires) : q ∈ instrWiresL i := by
  cases i with
  | X t => simpa [Instr.wires, instrWiresL] using h
  | CX a t => simpa [Instr.wires, instrWiresL] using h
  | CCX a b t => simpa [Instr.wires, instrWiresL] using h
  | measureX t c0 c1 =>
    simp only [Instr.wires, Finset.mem_union, Finset.mem_singleton] at h
    simp only [instrWiresL, List.mem_cons, List.flatMap_append, List.mem_append]
    rcases h with (rfl | h) | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (mem_correctionWires h))
    · exact Or.inr (Or.inr (mem_correctionWires h))
/-- A list check bounds every wire of a program. -/
theorem wires_lt_of_check (P : Program) (n : Nat) (h : P.all (fun i => (instrWiresL i).all (· < n)) = true) :
    ∀ q ∈ wires P, q < n := by
  induction P with
  | nil => intro q hq; simp [wires] at hq
  | cons i p ih =>
    intro q hq
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [wires, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have := List.all_eq_true.mp h.1 q (mem_instrWires hq); simpa using this
    · exact ih h.2 q hq
theorem mem_wires_rename (f : Wire → Wire) {q : Wire} : ∀ {P : Program}, q ∈ wires (renameProgram f P) →
    ∃ p ∈ wires P, q = f p
  | [], h => by simp [renameProgram, wires] at h
  | i :: P, h => by
    simp only [renameProgram, List.map_cons, wires, Finset.mem_union] at h
    rcases h with h | h
    · have hi : ∀ q ∈ (renameInstr f i).wires, ∃ p ∈ i.wires, q = f p := by
        intro q hq
        cases i with
        | X t => simp [renameInstr, Instr.wires] at hq ⊢; exact hq
        | CX a t => simp [renameInstr, Instr.wires] at hq ⊢; rcases hq with rfl | rfl <;> simp
        | CCX a b t => simp [renameInstr, Instr.wires] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp
        | measureX t c0 c1 =>
          have hc : ∀ cs : List Correction, q ∈ correctionWires (cs.map (renameCorrection f)) →
              ∃ p ∈ correctionWires cs, q = f p := by
            intro cs
            induction cs with
            | nil => simp [correctionWires]
            | cons c cs ihc =>
              intro hq'
              cases c with
              | Z w =>
                simp only [List.map_cons, renameCorrection, correctionWires, Finset.mem_union,
                  Finset.mem_singleton] at hq' ⊢
                rcases hq' with rfl | hq'
                · exact ⟨w, Or.inl rfl, rfl⟩
                · obtain ⟨p, hp, rfl⟩ := ihc hq'; exact ⟨p, Or.inr hp, rfl⟩
              | CZ a b =>
                simp only [List.map_cons, renameCorrection, correctionWires, Finset.mem_union,
                  Finset.mem_insert, Finset.mem_singleton] at hq' ⊢
                rcases hq' with (rfl | rfl) | hq'
                · exact ⟨a, Or.inl (Or.inl rfl), rfl⟩
                · exact ⟨b, Or.inl (Or.inr rfl), rfl⟩
                · obtain ⟨p, hp, rfl⟩ := ihc hq'; exact ⟨p, Or.inr hp, rfl⟩
          simp only [renameInstr, Instr.wires, Finset.mem_union, Finset.mem_singleton] at hq ⊢
          rcases hq with (rfl | hq) | hq
          · exact ⟨t, Or.inl (Or.inl rfl), rfl⟩
          · obtain ⟨p, hp, rfl⟩ := hc c0 hq; exact ⟨p, Or.inl (Or.inr hp), rfl⟩
          · obtain ⟨p, hp, rfl⟩ := hc c1 hq; exact ⟨p, Or.inr hp, rfl⟩
      obtain ⟨p, hp, rfl⟩ := hi q h
      exact ⟨p, Finset.mem_union_left _ hp, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := mem_wires_rename f h
      exact ⟨p, Finset.mem_union_right _ hp, rfl⟩

theorem load0_ports : ∀ q ∈ wires ReducedWindowArchives.load0, q < 155 :=
  wires_lt_of_check _ _ (by decide +kernel)
theorem load1_ports : ∀ q ∈ wires ReducedWindowArchives.load1, q < 155 :=
  wires_lt_of_check _ _ (by decide +kernel)
theorem restore0_ports : ∀ q ∈ wires ReducedWindowArchives.restore0, q < 150 :=
  wires_lt_of_check _ _ (by decide +kernel)
theorem restore1_ports : ∀ q ∈ wires ReducedWindowArchives.restore1, q < 150 :=
  wires_lt_of_check _ _ (by decide +kernel)

/-! Port lists stay in the footprint. -/

/-- A history cell `n ∈ [t+1034, t+1043]` placed by `OB5.sig t` stays in the footprint. -/
theorem cell_foot (t f n : Nat) (h1 : t+1034 ≤ n) (h2 : n ≤ t+1043) (ht : t ≤ 512) : archFootP t f (OB5.sig t n) := by
  show archFootP t f (if (1301 ≤ n ∧ n ≤ 1044+t) ∨ (2069 ≤ n+t ∧ n ≤ 1812) then 3113-n else n)
  by_cases h : 1301 ≤ n
  · rw [if_pos (Or.inl ⟨h, by omega⟩)]; unfold archFootP; omega
  · rw [if_neg (by omega)]; unfold archFootP; omega
theorem cellsLoad_foot (t f q : Nat) (ht : t ≤ 512) (h : q ∈ cellsLoadP t) : archFootP t f q := by
  unfold cellsLoadP at h
  obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp h
  have hk' := List.mem_range.mp hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · unfold archFootP; omega
  · exact cell_foot t f _ (by omega) (by omega) ht
theorem cellsRestore_foot (t f : Nat) (ht : t ≤ 512) : ∀ q ∈ cellsRestoreP t, archFootP t f q := by
  unfold cellsRestoreP
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), (by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), (by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), (by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega), fun _ h => by cases h⟩

theorem scratch_foot (t f k : Nat) (ht : t < 512) (hk : k < 134) : archFootP t f (scratchS t k) := by
  have := scratchS_cases t k ht hk; unfold archFootP; omega
theorem plain_foot (t f k : Nat) (hk : k < 134) : archFootP t f (1556 + k) := by
  unfold archFootP; omega
theorem scratchX_foot (e f k : Nat) (he : e < 512) (hk : k < 134) : archFootP e f (scratchX e k) := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩
  · rw [e1]; exact scratch_foot e f k he hk
  · rw [e1]; unfold archFootP; omega
  · rw [e1]; unfold archFootP; omega

theorem loadPortsWP_foot (t f p : Nat) (ht : t < 512) (hp : p < 155) :
    archFootP t f ((loadPortsWP t f).getD p 0) := by
  by_cases h1 : p < 20
  · rw [loadPortsWP_cell t f p h1]
    have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsLoad_foot t f _ (by omega) (List.getElem_mem _)
  by_cases h2 : p < 23
  · obtain ⟨i, rfl⟩ : ∃ i, p = 20 + i := ⟨p - 20, by omega⟩
    rw [loadPortsWP_flag t f i (by omega)]; unfold archFootP; omega
  · obtain ⟨k, rfl⟩ : ∃ k, p = 23 + k := ⟨p - 23, by omega⟩
    rw [loadPortsWP_scratch t f k (by omega)]; exact scratch_foot t f k (by omega) (by omega)
theorem restorePortsWP_foot (t f p : Nat) (ht : t < 512) (hp : p < 150) :
    archFootP t f ((restorePortsWP t).getD p 0) := by
  by_cases h1 : p < 16
  · rw [restorePortsWP_cell t p h1]
    have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsRestore_foot t f (by omega) _ (List.getElem_mem _)
  · obtain ⟨k, rfl⟩ : ∃ k, p = 16 + k := ⟨p - 16, by omega⟩
    rw [restorePortsWP_scratch t k (by omega)]; exact scratch_foot t f k (by omega) (by omega)
theorem moves_foot (t f : Nat) (ht : t ≤ 512) :
    AllW (archFootP t f) (swapsG (moveLoadPairs t)) ∧ AllW (archFootP t f) (swapsG (moveRestorePairs t f)) := by
  constructor <;> apply allW_swapsG
  · simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, fun _ h => by cases h⟩
  · simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(cell_foot t f _ (by omega) (by omega) ht), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (cell_foot t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, ⟨(by unfold archFootP; omega), (by unfold archFootP; omega)⟩, fun _ h => by cases h⟩

theorem renamed_foot (P : Program) (ports : List Wire) (n t f : Nat) (hP : ∀ q ∈ wires P, q < n)
    (hports : ∀ p < n, archFootP t f (ports.getD p 0)) :
    ∀ q ∈ wires (renameProgram (fun q => ports.getD q 0) P), archFootP t f q := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_wires_rename _ hq
  exact hports p (hP p hp)

attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
/-- Window-form archives of block `j` (tick `t = start j + 15`, flags `e0(t)+6..8`). -/
theorem archiveLoadP_wires (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveLoadP j d), archFootP (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsWP_foot _ _ p ht hp) q hq
  · exact (allW_programs (moves_foot _ (e0P (start j + 15) + 6) (by omega)).1).1 q hq
theorem archiveRestoreP_wires (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveRestoreP j d), archFootP (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsWP_foot _ _ p ht hp) q hq
  · exact (allW_programs (moves_foot _ (e0P (start j + 15) + 6) (by omega)).2).1 q hq
theorem loadPortsXP_foot (e f p : Nat) (he : e < 512) (hp : p < 155) :
    archFootP e f ((loadPortsXP e f).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [loadPortsXP_low e f h]; exact loadPortsWP_foot e f p he hp
  · have len := loadPortsXP_length e f
    have mem : (loadPortsXP e f).getD p 0 ∈ loadPortsXP e f := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (loadPortsXP e f).getD p 0 = x at mem ⊢
    simp only [loadPortsXP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at mem
    rcases mem with (m | m) | ⟨k, hk, rfl⟩
    · exact cellsLoad_foot e f x (by omega) m
    · rcases m with rfl | rfl | rfl <;> (unfold archFootP; omega)
    · exact scratchX_foot e f k he (by omega)
theorem restorePortsXP_foot (e f p : Nat) (he : e < 512) (hp : p < 150) :
    archFootP e f ((restorePortsXP e).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [restorePortsXP_low e h]; exact restorePortsWP_foot e f p he hp
  · have len := restorePortsXP_length e
    have mem : (restorePortsXP e).getD p 0 ∈ restorePortsXP e := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (restorePortsXP e).getD p 0 = x at mem ⊢
    simp only [restorePortsXP, List.mem_append, List.mem_map, List.mem_range] at mem
    rcases mem with m | ⟨k, hk, rfl⟩
    · exact cellsRestore_foot e f (by omega) x m
    · exact scratchX_foot e f k he hk
/-- Stock-form exit archives at tick `e` (flags `bTop(e)+1..3`). -/
theorem exitLoadP_wires (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitLoadP e d), archFootP e (bTopP e + 1) q := by
  intro q hq
  rw [exitLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsXP_foot _ _ p he hp) q hq
  · exact (allW_programs (moves_foot e (bTopP e + 1) (by omega)).1).1 q hq
theorem exitRestoreP_wires (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitRestoreP e d), archFootP e (bTopP e + 1) q := by
  intro q hq
  rw [exitRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_foot _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsXP_foot _ _ p he hp) q hq
  · exact (allW_programs (moves_foot e (bTopP e + 1) (by omega)).2).1 q hq

end ECDSAAdd.Entrant.StairPacket.Partial

end

-- ==== w4: step 9: build-w4b SA_BFootW (sharp archive footprints for t <= 369) ====
section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic GateMirror MappedCompressed StairArchiveGates
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1

/-- build-w4b's sharp footprint, now the same set as `archFootP`: cells, flags, the carry block and, from tick 369
on, the released B-rail wires `[1302-t, 933]` hosting the scratch beyond the stock carry. -/
def archFootW (t f q : Nat) : Prop :=
  (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ 1300) ∨ (1556 ≤ q ∧ q ≤ 1812) ∨ (f ≤ q ∧ q ≤ f+2) ∨
  (369 ≤ t ∧ 1302 ≤ q+t ∧ q ≤ 933)

theorem cell_footW (t f n : Nat) (h1 : t+1034 ≤ n) (h2 : n ≤ t+1043) (ht : t ≤ 512) : archFootW t f (OB5.sig t n) := by
  show archFootW t f (if (1301 ≤ n ∧ n ≤ 1044+t) ∨ (2069 ≤ n+t ∧ n ≤ 1812) then 3113-n else n)
  by_cases h : 1301 ≤ n
  · rw [if_pos (Or.inl ⟨h, by omega⟩)]; unfold archFootW; omega
  · rw [if_neg (by omega)]; unfold archFootW; omega
theorem cellsLoad_footW (t f q : Nat) (ht : t ≤ 512) (h : q ∈ cellsLoadP t) : archFootW t f q := by
  unfold cellsLoadP at h
  obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp h
  have hk' := List.mem_range.mp hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · unfold archFootW; omega
  · exact cell_footW t f _ (by omega) (by omega) ht
theorem cellsRestore_footW (t f : Nat) (ht : t ≤ 512) : ∀ q ∈ cellsRestoreP t, archFootW t f q := by
  unfold cellsRestoreP
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  exact ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), (by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), (by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), (by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega), fun _ h => by cases h⟩

theorem scratch_footW (t f k : Nat) (ht : t < 512) (hk : k < 134) : archFootW t f (scratchS t k) := by
  have := scratchS_cases t k ht hk; unfold archFootW; omega
theorem plain_footW (t f k : Nat) (hk : k < 134) : archFootW t f (1556 + k) := by
  unfold archFootW; omega
theorem scratchX_footW (e f k : Nat) (he : e < 512) (hk : k < 134) : archFootW e f (scratchX e k) := by
  rcases scratchX_cases e k he hk with ⟨a, e1⟩ | ⟨a, b, e1⟩ | ⟨a, b, e1⟩
  · rw [e1]; exact scratch_footW e f k he hk
  · rw [e1]; unfold archFootW; omega
  · rw [e1]; unfold archFootW; omega

theorem loadPortsWP_footW (t f p : Nat) (ht : t < 512) (hp : p < 155) :
    archFootW t f ((loadPortsWP t f).getD p 0) := by
  by_cases h1 : p < 20
  · rw [loadPortsWP_cell t f p h1]
    have hc : (cellsLoadP t).length = 20 := by simp [cellsLoadP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsLoad_footW t f _ (by omega) (List.getElem_mem _)
  by_cases h2 : p < 23
  · obtain ⟨i, rfl⟩ : ∃ i, p = 20 + i := ⟨p - 20, by omega⟩
    rw [loadPortsWP_flag t f i (by omega)]; unfold archFootW; omega
  · obtain ⟨k, rfl⟩ : ∃ k, p = 23 + k := ⟨p - 23, by omega⟩
    rw [loadPortsWP_scratch t f k (by omega)]; exact scratch_footW t f k (by omega) (by omega)
theorem restorePortsWP_footW (t f p : Nat) (ht : t < 512) (hp : p < 150) :
    archFootW t f ((restorePortsWP t).getD p 0) := by
  by_cases h1 : p < 16
  · rw [restorePortsWP_cell t p h1]
    have hc : (cellsRestoreP t).length = 16 := by simp [cellsRestoreP]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact cellsRestore_footW t f (by omega) _ (List.getElem_mem _)
  · obtain ⟨k, rfl⟩ : ∃ k, p = 16 + k := ⟨p - 16, by omega⟩
    rw [restorePortsWP_scratch t k (by omega)]; exact scratch_footW t f k (by omega) (by omega)
theorem moves_footW (t f : Nat) (ht : t ≤ 512) :
    AllW (archFootW t f) (swapsG (moveLoadPairs t)) ∧ AllW (archFootW t f) (swapsG (moveRestorePairs t f)) := by
  constructor <;> apply allW_swapsG
  · simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, fun _ h => by cases h⟩
  · simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(cell_footW t f _ (by omega) (by omega) ht), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (cell_footW t f _ (by omega) (by omega) ht)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, ⟨(by unfold archFootW; omega), (by unfold archFootW; omega)⟩, fun _ h => by cases h⟩

theorem renamed_footW (P : Program) (ports : List Wire) (n t f : Nat) (hP : ∀ q ∈ wires P, q < n)
    (hports : ∀ p < n, archFootW t f (ports.getD p 0)) :
    ∀ q ∈ wires (renameProgram (fun q => ports.getD q 0) P), archFootW t f q := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_wires_rename _ hq
  exact hports p (hP p hp)

/-- Window-form archives of block `j` (tick `t = start j + 15`, flags `e0(t)+6..8`). -/
theorem archiveLoadP_wiresW (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveLoadP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsWP_footW _ _ p ht hp) q hq
  · exact (allW_programs (moves_footW _ (e0P (start j + 15) + 6) (by omega)).1).1 q hq
theorem archiveRestoreP_wiresW (j : Fin 23) (d : Bool) (hj : j.val ≤ 21) :
    ∀ q ∈ wires (archiveRestoreP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start]; omega
  intro q hq
  rw [archiveRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsWP_footW _ _ p ht hp) q hq
  · exact (allW_programs (moves_footW _ (e0P (start j + 15) + 6) (by omega)).2).1 q hq
theorem loadPortsXP_footW (e f p : Nat) (he : e < 512) (hp : p < 155) :
    archFootW e f ((loadPortsXP e f).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [loadPortsXP_low e f h]; exact loadPortsWP_footW e f p (by omega) hp
  · have len := loadPortsXP_length e f
    have mem : (loadPortsXP e f).getD p 0 ∈ loadPortsXP e f := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (loadPortsXP e f).getD p 0 = x at mem ⊢
    simp only [loadPortsXP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at mem
    rcases mem with (m | m) | ⟨k, hk, rfl⟩
    · exact cellsLoad_footW e f x (by omega) m
    · rcases m with rfl | rfl | rfl <;> (unfold archFootW; omega)
    · exact scratchX_footW e f k (by omega) (by omega)
theorem restorePortsXP_footW (e f p : Nat) (he : e < 512) (hp : p < 150) :
    archFootW e f ((restorePortsXP e).getD p 0) := by
  by_cases h : e ≤ 369
  · rw [restorePortsXP_low e h]; exact restorePortsWP_footW e f p (by omega) hp
  · have len := restorePortsXP_length e
    have mem : (restorePortsXP e).getD p 0 ∈ restorePortsXP e := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    generalize (restorePortsXP e).getD p 0 = x at mem ⊢
    simp only [restorePortsXP, List.mem_append, List.mem_map, List.mem_range] at mem
    rcases mem with m | ⟨k, hk, rfl⟩
    · exact cellsRestore_footW e f (by omega) x m
    · exact scratchX_footW e f k (by omega) hk
/-- Stock-form exit archives at tick `e` (flags `bTop(e)+1..3`). -/
theorem exitLoadP_wiresW (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitLoadP e d), archFootW e (bTopP e + 1) q := by
  intro q hq
  rw [exitLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsXP_footW _ _ p he hp) q hq
  · exact (allW_programs (moves_footW e (bTopP e + 1) (by omega)).1).1 q hq
theorem exitRestoreP_wiresW (e : Nat) (d : Bool) (he : e < 512) :
    ∀ q ∈ wires (exitRestoreP e d), archFootW e (bTopP e + 1) q := by
  intro q hq
  rw [exitRestoreP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 150 _ _ (by cases d <;> first | exact restore0_ports | exact restore1_ports)
      (fun p hp => restorePortsXP_footW _ _ p he hp) q hq
  · exact (allW_programs (moves_footW e (bTopP e + 1) (by omega)).2).1 q hq

end ECDSAAdd.Entrant.StairPacket.Partial
end

-- ==== w4: step 9: build-w4b drop-in SA_WindowFold (par-d2 WindowFold, additive measure, record lit) ====
-- BEGIN par-d WindowFold
section

namespace ECDSAAdd.Entrant.StairPacket.WindowFold
open Arithmetic MappedCompressed StairArchiveGates Baselines Challenge
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! The walk window as a fold over its block list (par-d, Job D).
Blocks are `j : Fin 23` with start `start j = 75+15j`, listed in order and consecutive. The first block opens the
window after the entry portal at its own start; every later block `k` loads, after its first tick, the window-form
archive of its predecessor `i` (`load i`); the window closes at `exitTick = start last+15` with park, exit portal, one
stock tick and the stock-form exit archive. `Pieces α` holds one value per piece, so the same fold gives the program
(`α = Program`) and any additive measure of it (`α = Nat`, via `Pieces.map`). -/

structure Pieces (α : Type) where
  enter : Fin 23 → α
  enterInv : Fin 23 → α
  leave : Fin 23 → α
  leaveInv : Fin 23 → α
  load : Fin 23 → Bool → α
  restore : Fin 23 → Bool → α
  portal : Nat → α
  portalInv : Nat → α
  park : Nat → α
  parkInv : Nat → α
  exitLoad : Nat → Bool → α
  exitRestore : Nat → Bool → α
  routed : Fin 23 → Nat → Nat → α
  unrouted : Fin 23 → Nat → Nat → α
  pack : Bool → Nat → Nat → α
  unpack : Bool → Nat → Nat → α
  tick : Nat → α
  receiver : Nat → α

def Pieces.map {α β : Type} (f : α → β) (P : Pieces α) : Pieces β where
  enter j := f (P.enter j)
  enterInv j := f (P.enterInv j)
  leave j := f (P.leave j)
  leaveInv j := f (P.leaveInv j)
  load j d := f (P.load j d)
  restore j d := f (P.restore j d)
  portal t := f (P.portal t)
  portalInv t := f (P.portalInv t)
  park t := f (P.park t)
  parkInv t := f (P.parkInv t)
  exitLoad t d := f (P.exitLoad t d)
  exitRestore t d := f (P.exitRestore t d)
  routed j a n := f (P.routed j a n)
  unrouted j a n := f (P.unrouted j a n)
  pack d s t := f (P.pack d s t)
  unpack d s t := f (P.unpack d s t)
  tick t := f (P.tick t)
  receiver t := f (P.receiver t)

section fold
variable {α : Type}

def firstF (P : Pieces α) (d : Bool) (j : Fin 23) : List α :=
  [P.enter j, P.routed j 0 1, P.pack d (start j) (start j), P.routed j 1 14, P.leave j]
def nextF (P : Pieces α) (d : Bool) (i j : Fin 23) : List α :=
  [P.enter j, P.routed j 0 1, P.pack d (start j) (start j-10), P.load i d, P.routed j 1 14, P.leave j]
def chainF (P : Pieces α) (d : Bool) : Fin 23 → List (Fin 23) → List α
  | _, [] => []
  | i, j :: js => nextF P d i j ++ chainF P d j js
def lastStart : Fin 23 → List (Fin 23) → Nat
  | j, [] => start j
  | _, j :: js => lastStart j js
def exitTick (j : Fin 23) (js : List (Fin 23)) : Nat := lastStart j js+15
def exitF (P : Pieces α) (d : Bool) (e : Nat) : List α :=
  [P.park e, P.portalInv e, P.tick e, P.pack d e (e-10), P.exitLoad e d]
def forwardL (P : Pieces α) (d : Bool) (j : Fin 23) (js : List (Fin 23)) : List α :=
  P.portal (start j) :: (firstF P d j ++ (chainF P d j js ++ exitF P d (exitTick j js)))

def firstR (P : Pieces α) (d : Bool) (j : Fin 23) : List α :=
  [P.leaveInv j, P.unrouted j 1 14, P.unpack d (start j) (start j), P.unrouted j 0 1, P.enterInv j]
def nextR (P : Pieces α) (d : Bool) (i j : Fin 23) : List α :=
  [P.leaveInv j, P.unrouted j 1 14, P.restore i d, P.unpack d (start j) (start j-10), P.unrouted j 0 1, P.enterInv j]
def chainR (P : Pieces α) (d : Bool) : Fin 23 → List (Fin 23) → List α
  | _, [] => []
  | i, j :: js => chainR P d j js ++ nextR P d i j
def exitR (P : Pieces α) (d : Bool) (e : Nat) : List α :=
  [P.exitRestore e d, P.unpack d e (e-10), P.receiver e, P.portal e, P.parkInv e]
def reverseL (P : Pieces α) (d : Bool) (j : Fin 23) (js : List (Fin 23)) : List α :=
  exitR P d (exitTick j js) ++ (chainR P d j js ++ (firstR P d j ++ [P.portalInv (start j)]))

end fold

section maps
variable {α β : Type} (f : α → β) (P : Pieces α) (d : Bool)

theorem chainF_map : ∀ (i : Fin 23) (js : List (Fin 23)), chainF (P.map f) d i js = (chainF P d i js).map f
  | _, [] => rfl
  | i, j :: js => by
    rw [chainF, chainF, List.map_append, chainF_map j js]
    all_goals rfl

theorem chainR_map : ∀ (i : Fin 23) (js : List (Fin 23)), chainR (P.map f) d i js = (chainR P d i js).map f
  | _, [] => rfl
  | i, j :: js => by
    rw [chainR, chainR, List.map_append, chainR_map j js]
    all_goals rfl

theorem forwardL_map (j : Fin 23) (js : List (Fin 23)) :
    forwardL (P.map f) d j js = (forwardL P d j js).map f := by
  simp only [forwardL, List.map_cons, List.map_append, chainF_map]
  all_goals rfl

theorem reverseL_map (j : Fin 23) (js : List (Fin 23)) :
    reverseL (P.map f) d j js = (reverseL P d j js).map f := by
  simp only [reverseL, List.map_cons, List.map_append, chainR_map]
  all_goals rfl

end maps

/-- Programs of a window. -/
def forwardW (P : Pieces Program) (d : Bool) (j : Fin 23) (js : List (Fin 23)) : Program :=
  (forwardL P d j js).flatten
def reverseW (P : Pieces Program) (d : Bool) (j : Fin 23) (js : List (Fin 23)) : Program :=
  (reverseL P d j js).flatten

/-- Generic over any additive measure (d9 layout: `Stair44Resources.Cost` lives in Tail8dd, not imported here;
instantiate with `c.measure c.append`). -/
theorem measure_flatten (m : Program → Nat) (append : ∀ a b : Program, m (a ++ b) = m a + m b) :
    ∀ L : List Program, m L.flatten = (L.map m).sum
  | [] => by
    have h := append [] []
    rw [List.nil_append] at h
    simp only [List.flatten_nil, List.map_nil, List.sum_nil]
    omega
  | P :: L => by
    rw [List.flatten_cons, append, measure_flatten m append L, List.map_cons, List.sum_cons]

/-- Every additive measure of a window is the sum of the same fold over the measured pieces. -/
theorem measure_forward (m : Program → Nat) (append : ∀ a b : Program, m (a ++ b) = m a + m b)
    (P : Pieces Program) (d : Bool) (j : Fin 23)
    (js : List (Fin 23)) : m (forwardW P d j js) = (forwardL (P.map m) d j js).sum := by
  rw [forwardW, measure_flatten m append, forwardL_map]

theorem measure_reverse (m : Program → Nat) (append : ∀ a b : Program, m (a ++ b) = m a + m b)
    (P : Pieces Program) (d : Bool) (j : Fin 23)
    (js : List (Fin 23)) : m (reverseW P d j js) = (reverseL (P.map m) d j js).sum := by
  rw [reverseW, measure_flatten m append, reverseL_map]

/-- Program pieces from the block-keyed parts; ticks, codecs and routing are the stock ones. -/
def ofParts (enter enterInv leave leaveInv : Fin 23 → Program) (load restore : Fin 23 → Bool → Program)
    (portal portalInv park parkInv : Nat → Program) (exitLoad exitRestore : Nat → Bool → Program) :
    Pieces Program where
  enter := enter
  enterInv := enterInv
  leave := leave
  leaveInv := leaveInv
  load := load
  restore := restore
  portal := portal
  portalInv := portalInv
  park := park
  parkInv := parkInv
  exitLoad := exitLoad
  exitRestore := exitRestore
  routed := StairPacket.routed
  unrouted := StairPacket.unrouted
  pack d s t := renameProgram (OB5.sig s) (Rolling1588.packAtTick d t)
  unpack d s t := renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t)
  tick e := renameProgram (OB5.sig e) (TickRanges.tick base e)
  receiver e := renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e)

/-! Generic counts of the stock pieces. -/

theorem routed_counts (j : Fin 23) (a n : Nat) (bound : a+n≤15) :
    toffoliCount (StairPacket.routed j a n)=n*(2*(smallBits j+18)) ∧
    measurementCount (StairPacket.routed j a n)=n*(smallBits j+18) ∧
    toffoliCount (StairPacket.unrouted j a n)=n*(2*(smallBits j+18)) ∧
    measurementCount (StairPacket.unrouted j a n)=n*(smallBits j+18) := by
  obtain ⟨f,r⟩ := fixed_route j a n bound
  have hs := IntegerPacket.metrics (shape j) a n bound
  have mid : (shape j).mid+1=smallBits j+18 := rfl
  rw [mid] at hs
  rw [f,r,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2]
  exact hs

theorem pack_counts (d : Bool) (s t : Nat) (five : t≠5) (due : History5.packDue t=true) :
    toffoliCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))=9 ∧
    measurementCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))=4 ∧
    toffoliCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))=11 ∧
    measurementCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))=2 := by
  have c := Rolling1588.code_counts d
  simp only [Rolling1588.packAtTick,Rolling1588.unpackAtTick,five,due,if_false,if_true,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  exact c

theorem pack_slots (d : Bool) (s t : Nat) (five : t≠5) (due : History5.packDue t=true) :
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))=144+(if d then 24 else 12) ∧
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))=142+(if d then 24 else 12) := by
  have c := Rolling1588.code_slots d
  simp only [Rolling1588.packAtTick,Rolling1588.unpackAtTick,five,due,if_false,if_true,
    Baselines.rename_gateSlots]
  exact c

/-- Every pack/unpack tick of a window inside 105..420 is a due tick other than 5. -/
theorem packDue_window (t : Nat) (lo : 105 ≤ t) (hi : t ≤ 420) (five : t%5=0) :
    t≠5 ∧ History5.packDue t=true := by
  refine ⟨by omega,?_⟩
  simp only [History5.packDue,decide_eq_true_eq]
  omega

end ECDSAAdd.Entrant.StairPacket.WindowFold

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFold
open Arithmetic MappedCompressed StairArchiveGates Partial

/-! build-w4b K3: dadon's literal pieces on the RECORD (window 225..255, exit 270) as a `Pieces` instance.
par-d's own `lit` is the +210 tree's (block 9 = 210); the record has blocks 10..12 only. -/

def litEnter : Fin 23 → Program
  | ⟨10,_⟩ => enter225 | ⟨11,_⟩ => enter240 | ⟨12,_⟩ => enter255 | _ => []
def litEnterInv : Fin 23 → Program
  | ⟨10,_⟩ => enter225Inv | ⟨11,_⟩ => enter240Inv | ⟨12,_⟩ => enter255Inv | _ => []
def litLeave : Fin 23 → Program
  | ⟨10,_⟩ => leave225 | ⟨11,_⟩ => leave240 | ⟨12,_⟩ => leave255 | _ => []
def litLeaveInv : Fin 23 → Program
  | ⟨10,_⟩ => leave225Inv | ⟨11,_⟩ => leave240Inv | ⟨12,_⟩ => leave255Inv | _ => []
def litLoad : Fin 23 → Bool → Program
  | ⟨10,_⟩, d => archiveLoad240 d | ⟨11,_⟩, d => archiveLoad255 d | _, _ => []
def litRestore : Fin 23 → Bool → Program
  | ⟨10,_⟩, d => archiveRestore240 d | ⟨11,_⟩, d => archiveRestore255 d | _, _ => []
def litPortal : Nat → Program
  | 225 => portal225 | 270 => portal270 | _ => []
def litPortalInv : Nat → Program
  | 225 => portal225Inv | 270 => portal270Inv | _ => []
def litPark : Nat → Program
  | 270 => park270 | _ => []
def litParkInv : Nat → Program
  | 270 => park270Inv | _ => []
def litExitLoad : Nat → Bool → Program
  | 270, d => archiveLoad270 d | _, _ => []
def litExitRestore : Nat → Bool → Program
  | 270, d => archiveRestore270 d | _, _ => []

def lit : Pieces Program :=
  ofParts litEnter litEnterInv litLeave litLeaveInv litLoad litRestore litPortal litPortalInv litPark litParkInv
    litExitLoad litExitRestore

def b10 : Fin 23 := ⟨10,by decide⟩
def b11 : Fin 23 := ⟨11,by decide⟩
def b12 : Fin 23 := ⟨12,by decide⟩

attribute [local irreducible] portal225 portal225Inv portal270 portal270Inv park270 park270Inv
  enter225 enter240 enter255 enter225Inv enter240Inv enter255Inv
  leave225 leave240 leave255 leave225Inv leave240Inv leave255Inv
  archiveLoad240 archiveLoad255 archiveLoad270
  archiveRestore240 archiveRestore255 archiveRestore270
  StairPacket.routed StairPacket.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick

end ECDSAAdd.Entrant.StairPacket.WindowFold

end
-- END par-d WindowFold

-- BEGIN par-d WindowFold bounds
section

namespace ECDSAAdd.Entrant.StairPacket.WindowFold
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Pointwise order on measured pieces. -/
structure Pieces.Le (P V : Pieces Nat) : Prop where
  enter : ∀ j, P.enter j ≤ V.enter j
  enterInv : ∀ j, P.enterInv j ≤ V.enterInv j
  leave : ∀ j, P.leave j ≤ V.leave j
  leaveInv : ∀ j, P.leaveInv j ≤ V.leaveInv j
  load : ∀ j d, P.load j d ≤ V.load j d
  restore : ∀ j d, P.restore j d ≤ V.restore j d
  portal : ∀ t, P.portal t ≤ V.portal t
  portalInv : ∀ t, P.portalInv t ≤ V.portalInv t
  park : ∀ t, P.park t ≤ V.park t
  parkInv : ∀ t, P.parkInv t ≤ V.parkInv t
  exitLoad : ∀ t d, P.exitLoad t d ≤ V.exitLoad t d
  exitRestore : ∀ t d, P.exitRestore t d ≤ V.exitRestore t d
  routed : ∀ j a n, P.routed j a n ≤ V.routed j a n
  unrouted : ∀ j a n, P.unrouted j a n ≤ V.unrouted j a n
  pack : ∀ d s t, P.pack d s t ≤ V.pack d s t
  unpack : ∀ d s t, P.unpack d s t ≤ V.unpack d s t
  tick : ∀ t, P.tick t ≤ V.tick t
  receiver : ∀ t, P.receiver t ≤ V.receiver t

private theorem sum_le_cons {a b : Nat} {l r : List Nat} (h : a ≤ b) (t : l.sum ≤ r.sum) :
    (a::l).sum ≤ (b::r).sum := by
  simp only [List.sum_cons]; omega
private theorem sum_app' : ∀ l r : List Nat, (l++r).sum = l.sum+r.sum
  | [], r => by simp only [List.nil_append, List.sum_nil, Nat.zero_add]
  | a::l, r => by simp only [List.cons_append, List.sum_cons, sum_app' l r]; omega
private theorem sum_append_le {l r l' r' : List Nat} (h : l.sum ≤ l'.sum) (t : r.sum ≤ r'.sum) :
    (l++r).sum ≤ (l'++r').sum := by
  rw [sum_app', sum_app']; omega

variable {P V : Pieces Nat} (h : P.Le V) (d : Bool)
include h

theorem chainF_le : ∀ (i : Fin 23) (js : List (Fin 23)), (chainF P d i js).sum ≤ (chainF V d i js).sum
  | _, [] => by simp [chainF]
  | i, j :: js => by
    simp only [chainF]
    apply sum_append_le _ (chainF_le j js)
    simp only [nextF, List.sum_cons, List.sum_nil]
    have := h.enter j; have := h.routed j 0 1; have := h.pack d (start j) (start j-10); have := h.load i d
    have := h.routed j 1 14; have := h.leave j
    omega

theorem chainR_le : ∀ (i : Fin 23) (js : List (Fin 23)), (chainR P d i js).sum ≤ (chainR V d i js).sum
  | _, [] => by simp [chainR]
  | i, j :: js => by
    simp only [chainR]
    apply sum_append_le (chainR_le j js)
    simp only [nextR, List.sum_cons, List.sum_nil]
    have := h.leaveInv j; have := h.unrouted j 1 14; have := h.restore i d; have := h.unpack d (start j) (start j-10)
    have := h.unrouted j 0 1; have := h.enterInv j
    omega

/-- Pointwise piece bounds bound the window: one fold, then a Nat evaluation. -/
theorem forwardL_le (j : Fin 23) (js : List (Fin 23)) : (forwardL P d j js).sum ≤ (forwardL V d j js).sum := by
  simp only [forwardL]
  apply sum_le_cons (h.portal _)
  apply sum_append_le
  · simp only [firstF, List.sum_cons, List.sum_nil]
    have := h.enter j; have := h.routed j 0 1; have := h.pack d (start j) (start j); have := h.routed j 1 14
    have := h.leave j
    omega
  · apply sum_append_le (chainF_le h d j js)
    simp only [exitF, List.sum_cons, List.sum_nil]
    have := h.park (exitTick j js); have := h.portalInv (exitTick j js); have := h.tick (exitTick j js)
    have := h.pack d (exitTick j js) (exitTick j js-10); have := h.exitLoad (exitTick j js) d
    omega

theorem reverseL_le (j : Fin 23) (js : List (Fin 23)) : (reverseL P d j js).sum ≤ (reverseL V d j js).sum := by
  simp only [reverseL]
  apply sum_append_le
  · simp only [exitR, List.sum_cons, List.sum_nil]
    have := h.exitRestore (exitTick j js) d; have := h.unpack d (exitTick j js) (exitTick j js-10)
    have := h.receiver (exitTick j js); have := h.portal (exitTick j js); have := h.parkInv (exitTick j js)
    omega
  · apply sum_append_le (chainR_le h d j js)
    simp only [firstR, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
    have := h.leaveInv j; have := h.unrouted j 1 14; have := h.unpack d (start j) (start j)
    have := h.unrouted j 0 1; have := h.enterInv j; have := h.portalInv (start j)
    omega

omit h in
/-- Two-sided piece bounds give the exact window sum. Use `V` = closed forms on the window's arguments and
`P`'s own value elsewhere (an `if`), so both orders hold for every argument and `decide` never evaluates a program. -/
theorem forwardL_eq {P V : Pieces Nat} (h₁ : P.Le V) (h₂ : V.Le P) (j : Fin 23) (js : List (Fin 23)) :
    (forwardL P d j js).sum = (forwardL V d j js).sum :=
  Nat.le_antisymm (forwardL_le h₁ d j js) (forwardL_le h₂ d j js)
omit h in
theorem reverseL_eq {P V : Pieces Nat} (h₁ : P.Le V) (h₂ : V.Le P) (j : Fin 23) (js : List (Fin 23)) :
    (reverseL P d j js).sum = (reverseL V d j js).sum :=
  Nat.le_antisymm (reverseL_le h₁ d j js) (reverseL_le h₂ d j js)

end ECDSAAdd.Entrant.StairPacket.WindowFold

end
-- END par-d WindowFold bounds

-- BEGIN par-d WindowFold On
section

namespace ECDSAAdd.Entrant.StairPacket.WindowFold
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `Q` holds for every piece that a window inside blocks `lo..hi` uses (exit tick at block `hi+1`). -/
structure Pieces.On {α : Type} (Q : α → Prop) (P : Pieces α) (d : Bool) (lo hi : Nat) : Prop where
  block : ∀ j : Fin 23, lo ≤ j.val → j.val ≤ hi →
    Q (P.enter j) ∧ Q (P.enterInv j) ∧ Q (P.leave j) ∧ Q (P.leaveInv j) ∧
    Q (P.routed j 0 1) ∧ Q (P.routed j 1 14) ∧ Q (P.unrouted j 0 1) ∧ Q (P.unrouted j 1 14) ∧
    Q (P.pack d (start j) (start j)) ∧ Q (P.unpack d (start j) (start j)) ∧
    Q (P.pack d (start j) (start j-10)) ∧ Q (P.unpack d (start j) (start j-10)) ∧
    Q (P.load j d) ∧ Q (P.restore j d) ∧ Q (P.portal (start j)) ∧ Q (P.portalInv (start j))
  exit : ∀ j : Fin 23, lo < j.val → j.val ≤ hi+1 →
    Q (P.park (start j)) ∧ Q (P.parkInv (start j)) ∧ Q (P.portal (start j)) ∧ Q (P.portalInv (start j)) ∧
    Q (P.tick (start j)) ∧ Q (P.receiver (start j)) ∧
    Q (P.pack d (start j) (start j-10)) ∧ Q (P.unpack d (start j) (start j-10)) ∧
    Q (P.exitLoad (start j) d) ∧ Q (P.exitRestore (start j) d)

/-- The blocks after `i` are `i+1, i+2, ...`. -/
def Consec : Fin 23 → List (Fin 23) → Prop
  | _, [] => True
  | i, j :: js => j.val=i.val+1 ∧ Consec j js

/-- Index of the window's last block. -/
def lastBlock : Fin 23 → List (Fin 23) → Fin 23
  | j, [] => j
  | _, j :: js => lastBlock j js

theorem lastStart_eq : ∀ (j : Fin 23) (js : List (Fin 23)), lastStart j js = start (lastBlock j js)
  | _, [] => rfl
  | _, j :: js => lastStart_eq j js

theorem consec_range : ∀ (i : Fin 23) (js : List (Fin 23)), Consec i js →
    i.val ≤ (lastBlock i js).val ∧ ∀ k ∈ js, i.val < k.val ∧ k.val ≤ (lastBlock i js).val
  | _, [], _ => ⟨Nat.le_refl _, by simp⟩
  | i, j :: js, ⟨next,rest⟩ => by
    obtain ⟨le,all⟩ := consec_range j js rest
    refine ⟨by simp only [lastBlock]; omega,?_⟩
    intro k mem
    rcases List.mem_cons.mp mem with rfl | mem
    · simp only [lastBlock]; omega
    · have := all k mem; simp only [lastBlock]; omega

variable {α : Type} {Q : α → Prop} {P : Pieces α} {d : Bool} {lo hi : Nat}

theorem chainF_on (h : P.On Q d lo hi) : ∀ (i : Fin 23) (js : List (Fin 23)), Consec i js → lo ≤ i.val →
    (lastBlock i js).val ≤ hi → ∀ x ∈ chainF P d i js, Q x
  | _, [], _, _, _ => by simp [chainF]
  | i, j :: js, ⟨next,rest⟩, lo_i, top => by
    have r := (consec_range j js rest).1
    have jb : j.val ≤ hi := by simp only [lastBlock] at top; omega
    have ib : i.val ≤ hi := by omega
    have bj := h.block j (by omega) jb
    have bi := h.block i lo_i ib
    intro x mem
    simp only [chainF,List.mem_append] at mem
    rcases mem with mem | mem
    · simp only [nextF,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact bj.1
      · exact bj.2.2.2.2.1
      · exact bj.2.2.2.2.2.2.2.2.2.2.1
      · exact bi.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact bj.2.2.2.2.2.1
      · exact bj.2.2.1
    · exact chainF_on h j js rest (by omega) (by simpa only [lastBlock] using top) x mem

theorem chainR_on (h : P.On Q d lo hi) : ∀ (i : Fin 23) (js : List (Fin 23)), Consec i js → lo ≤ i.val →
    (lastBlock i js).val ≤ hi → ∀ x ∈ chainR P d i js, Q x
  | _, [], _, _, _ => by simp [chainR]
  | i, j :: js, ⟨next,rest⟩, lo_i, top => by
    have r := (consec_range j js rest).1
    have jb : j.val ≤ hi := by simp only [lastBlock] at top; omega
    have ib : i.val ≤ hi := by omega
    have bj := h.block j (by omega) jb
    have bi := h.block i lo_i ib
    intro x mem
    simp only [chainR,List.mem_append] at mem
    rcases mem with mem | mem
    · exact chainR_on h j js rest (by omega) (by simpa only [lastBlock] using top) x mem
    · simp only [nextR,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact bj.2.2.2.1
      · exact bj.2.2.2.2.2.2.2.1
      · exact bi.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · exact bj.2.2.2.2.2.2.2.2.2.2.2.1
      · exact bj.2.2.2.2.2.2.1
      · exact bj.2.1

private theorem exit_index (j : Fin 23) (js : List (Fin 23)) (top : (lastBlock j js).val+1 < 23) :
    exitTick j js = start ⟨(lastBlock j js).val+1,top⟩ := by
  simp only [exitTick,lastStart_eq,StairPacket.start,Fin.val_mk]; omega

/-- Every piece of a window inside `lo..hi` satisfies `Q`. -/
theorem forwardL_on (h : P.On Q d lo hi) (j : Fin 23) (js : List (Fin 23)) (c : Consec j js)
    (lo_j : lo ≤ j.val) (top : (lastBlock j js).val ≤ hi) (room : (lastBlock j js).val+1 < 23) :
    ∀ x ∈ forwardL P d j js, Q x := by
  have r := (consec_range j js c).1
  have bj := h.block j lo_j (by omega)
  have ex := h.exit ⟨(lastBlock j js).val+1,room⟩ (by show lo < (lastBlock j js).val+1; omega)
    (by show (lastBlock j js).val+1 ≤ hi+1; omega)
  rw [←exit_index j js room] at ex
  intro x mem
  simp only [forwardL,List.mem_cons,List.mem_append] at mem
  rcases mem with rfl | mem | mem | mem
  · exact bj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · simp only [firstF,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact bj.1
    · exact bj.2.2.2.2.1
    · exact bj.2.2.2.2.2.2.2.2.1
    · exact bj.2.2.2.2.2.1
    · exact bj.2.2.1
  · exact chainF_on h j js c lo_j top x mem
  · simp only [exitF,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact ex.1
    · exact ex.2.2.2.1
    · exact ex.2.2.2.2.1
    · exact ex.2.2.2.2.2.2.1
    · exact ex.2.2.2.2.2.2.2.2.1

theorem reverseL_on (h : P.On Q d lo hi) (j : Fin 23) (js : List (Fin 23)) (c : Consec j js)
    (lo_j : lo ≤ j.val) (top : (lastBlock j js).val ≤ hi) (room : (lastBlock j js).val+1 < 23) :
    ∀ x ∈ reverseL P d j js, Q x := by
  have r := (consec_range j js c).1
  have bj := h.block j lo_j (by omega)
  have ex := h.exit ⟨(lastBlock j js).val+1,room⟩ (by show lo < (lastBlock j js).val+1; omega)
    (by show (lastBlock j js).val+1 ≤ hi+1; omega)
  rw [←exit_index j js room] at ex
  intro x mem
  simp only [reverseL,List.mem_append] at mem
  rcases mem with mem | mem | mem | mem
  · simp only [exitR,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact ex.2.2.2.2.2.2.2.2.2
    · exact ex.2.2.2.2.2.2.2.1
    · exact ex.2.2.2.2.2.1
    · exact ex.2.2.1
    · exact ex.2.1
  · exact chainR_on h j js c lo_j top x mem
  · simp only [firstR,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact bj.2.2.2.1
    · exact bj.2.2.2.2.2.2.2.1
    · exact bj.2.2.2.2.2.2.2.2.2.1
    · exact bj.2.2.2.2.2.2.1
    · exact bj.2.1
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst mem
    exact bj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- An append-closed property of all pieces holds for the flattened window. -/
theorem flatten_of {Q : Program → Prop} (nil : Q []) (app : ∀ {a b : Program}, Q a → Q b → Q (a++b)) :
    ∀ L : List Program, (∀ x ∈ L, Q x) → Q L.flatten
  | [], _ => nil
  | x :: L, h => by
    rw [List.flatten_cons]
    exact app (h x (List.mem_cons_self ..)) (flatten_of nil app L (fun y hy => h y (List.mem_cons_of_mem _ hy)))

end ECDSAAdd.Entrant.StairPacket.WindowFold

end
-- END par-d WindowFold On

-- ==== end PrizeHighBankJoin5ab3264 ====

-- ==== begin PrizeHighBankFirstHit91f0292 ====
section

-- kernel-replay helpers: bitmask set membership / duplicate-freeness for lists of naturals.
-- Used only via `open ECDSAAdd.Entrant.WSlimV3 in decide +kernel` inside proofs (scoped instances).
namespace ECDSAAdd.Entrant.WSlimV3

/-- bitmask of a list of naturals (kernel-fast: Nat.pow / Nat.lor on literals) -/
def bmask : List Nat → Nat
  | [] => 0
  | x :: xs => 2 ^ x ||| bmask xs

theorem bmask_testBit_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → (bmask l).testBit x = true
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [bmask, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.true_or]
    · simp only [bmask, Nat.testBit_or, bmask_testBit_of_mem h, Bool.or_true]

theorem mem_of_bmask_testBit : ∀ {l : List Nat} {x : Nat}, (bmask l).testBit x = true → x ∈ l
  | [], x, h => by simp only [bmask, Nat.zero_testBit] at h; cases h
  | y :: ys, x, h => by
    simp only [bmask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_two_pow] at h
      exact List.mem_cons.mpr (Or.inl (of_decide_eq_true h).symm)
    · exact List.mem_cons_of_mem _ (mem_of_bmask_testBit h)

/-- membership in a list of naturals decided by one bitmask (the kernel caches the mask per list) -/
scoped instance (priority := high) decMemNat (x : Nat) (l : List Nat) : Decidable (x ∈ l) :=
  decidable_of_iff ((bmask l).testBit x = true) ⟨mem_of_bmask_testBit, bmask_testBit_of_mem⟩

/-- duplicate-free check in one pass with a bitmask accumulator -/
def nodupB : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, m => !(m.testBit x) && nodupB xs (m ||| 2 ^ x)

theorem nodupB_sound : ∀ (l : List Nat) (m : Nat), nodupB l m = true →
    (∀ y ∈ l, m.testBit y = false) ∧ l.Nodup
  | [], _, _ => ⟨fun _ h => (by cases h), List.nodup_nil⟩
  | x :: xs, m, h => by
    have h' : (!(m.testBit x)) = true ∧ nodupB xs (m ||| 2 ^ x) = true := by
      simpa only [nodupB, Bool.and_eq_true] using h
    have hx : m.testBit x = false := by
      cases hb : m.testBit x <;> simp_all
    obtain ⟨hall, hnd⟩ := nodupB_sound xs _ h'.2
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, hnd⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have h2 := hall y hy
        rw [Nat.testBit_or] at h2
        cases hb : m.testBit y <;> simp_all
    · intro hmem
      have h2 := hall x hmem
      rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true] at h2
      cases h2

theorem nodupB_complete : ∀ (l : List Nat) (m : Nat), (∀ y ∈ l, m.testBit y = false) →
    l.Nodup → nodupB l m = true
  | [], _, _, _ => rfl
  | x :: xs, m, hm, hnd => by
    have hx : m.testBit x = false := hm x List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    have hrest : nodupB xs (m ||| 2 ^ x) = true := by
      apply nodupB_complete xs _ _ hnd'.2
      intro y hy
      rw [Nat.testBit_or, hm y (List.mem_cons_of_mem _ hy), Nat.testBit_two_pow, Bool.false_or]
      exact decide_eq_false (fun h => hnd'.1 (h ▸ hy))
    simp only [nodupB, hx, hrest, Bool.not_false, Bool.and_self]

theorem nodup_of_nodupB (l : List Nat) (h : nodupB l 0 = true) : l.Nodup := (nodupB_sound l 0 h).2

/-- duplicate-freeness of a list of naturals decided in one bitmask pass -/
scoped instance (priority := high) decNodupNat (l : List Nat) : Decidable l.Nodup :=
  decidable_of_iff (nodupB l 0 = true)
    ⟨nodup_of_nodupB l, fun h => nodupB_complete l 0 (fun y _ => Nat.zero_testBit y) h⟩

end ECDSAAdd.Entrant.WSlimV3

namespace ECDSAAdd.Entrant.WSlimV3

/-- mask of the first `k` values of a `Fin n`-indexed family (structural recursion, kernel-fast) -/
def famMaskAux (n : Nat) (f : Fin n → Nat) : (k : Nat) → k ≤ n → Nat
  | 0, _ => 0
  | k + 1, h => 2 ^ f ⟨k, h⟩ ||| famMaskAux n f k (Nat.le_of_succ_le h)

theorem famMaskAux_testBit (n : Nat) (f : Fin n → Nat) : ∀ (k : Nat) (h : k ≤ n) (q : Nat),
    (famMaskAux n f k h).testBit q = true ↔ ∃ i : Fin n, i.val < k ∧ f i = q
  | 0, _, q => by
    simp only [famMaskAux, Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | k + 1, h, q => by
    rw [famMaskAux, Nat.testBit_or, Bool.or_eq_true, famMaskAux_testBit n f k _ q, Nat.testBit_two_pow]
    constructor
    · rintro (h1 | ⟨i, hi, e⟩)
      · exact ⟨⟨k, h⟩, Nat.lt_succ_self k, of_decide_eq_true h1⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, e⟩
    · rintro ⟨i, hi, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact Or.inr ⟨i, hi, e⟩
      · left
        apply decide_eq_true
        have hk : (⟨k, h⟩ : Fin n) = i := Fin.ext hi.symm
        rw [hk]; exact e

/-- `q` differs from every value of a `Fin n`-indexed family: one mask per family (cached by the kernel) -/
scoped instance (priority := high) decForallFinNe (n q : Nat) (f : Fin n → Nat) :
    Decidable (∀ i : Fin n, q ≠ f i) :=
  decidable_of_iff ((famMaskAux n f n (Nat.le_refl n)).testBit q = false) (by
    rw [← Bool.not_eq_true, famMaskAux_testBit]
    constructor
    · intro h i e; exact h ⟨i, i.isLt, e.symm⟩
    · rintro h ⟨i, _, e⟩; exact h i e.symm)

/-- `q` is a value of a `Fin n`-indexed family -/
scoped instance (priority := high) decExistsFinEq (n q : Nat) (f : Fin n → Nat) :
    Decidable (∃ i : Fin n, q = f i) :=
  decidable_of_iff ((famMaskAux n f n (Nat.le_refl n)).testBit q = true) (by
    rw [famMaskAux_testBit]
    constructor
    · rintro ⟨i, _, e⟩; exact ⟨i, e.symm⟩
    · rintro ⟨i, e⟩; exact ⟨i, i.isLt, e.symm⟩)

/-- `q` avoids two fields of every element of a list -/
scoped instance (priority := high) decForallMemNe2 {α : Type} (l : List α) (q : Nat) (g h : α → Nat) :
    Decidable (∀ r ∈ l, q ≠ g r ∧ q ≠ h r) :=
  decidable_of_iff (q ∉ l.map g ∧ q ∉ l.map h) (by
    constructor
    · intro ⟨h1, h2⟩ r hr
      exact ⟨fun e => h1 (List.mem_map.mpr ⟨r, hr, e.symm⟩), fun e => h2 (List.mem_map.mpr ⟨r, hr, e.symm⟩)⟩
    · intro hh
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · obtain ⟨r, hr, e⟩ := List.mem_map.mp hm; exact (hh r hr).1 e.symm
      · obtain ⟨r, hr, e⟩ := List.mem_map.mp hm; exact (hh r hr).2 e.symm)

end ECDSAAdd.Entrant.WSlimV3

namespace ECDSAAdd.Entrant.WSlimV3

/-- a list of naturals packed into one natural, `w` bits per entry -/
def tpack (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2 ^ w * tpack w xs

/-- entry `q` of a packed table (kernel-fast: Nat.div / Nat.mod / Nat.pow on literals) -/
def tget (w T q : Nat) : Nat := T / 2 ^ (w * q) % 2 ^ w

theorem tget_tpack (w : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) → ∀ q, tget w (tpack w l) q = l.getD q 0
  | [], _, q => by simp [tget, tpack]
  | x :: xs, h, 0 => by
    have hx : x < 2 ^ w := h x List.mem_cons_self
    simp only [tget, tpack, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  | x :: xs, h, q + 1 => by
    have hx : x < 2 ^ w := h x List.mem_cons_self
    have ih := tget_tpack w xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) q
    simp only [List.getD_cons_succ]
    rw [← ih]
    simp only [tget, tpack]
    have hp : 2 ^ (w * (q + 1)) = 2 ^ w * 2 ^ (w * q) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hp, ← Nat.div_div_eq_div_mul]
    congr 2
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem tget_tpack' (w : Nat) (l : List Nat) (h : (l.all fun x => decide (x < 2 ^ w)) = true) (q : Nat) :
    l.getD q 0 = tget w (tpack w l) q :=
  (tget_tpack w l (fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)) q).symm

theorem rename_getD (l : List Nat) (w : Nat) (h : (l.all fun x => decide (x < 2 ^ w)) = true) (P : Program) :
    renameProgram (fun q => l.getD q 0) P = renameProgram (fun q => tget w (tpack w l) q) P := by
  congr 1; funext q; exact tget_tpack' w l h q

end ECDSAAdd.Entrant.WSlimV3

namespace ECDSAAdd.Entrant.WSlimV3
-- slice algebra on one base list: lets `simp` prove program-shape equalities without materializing programs

theorem seg_merge {α : Type} (L : List α) (a n b m : Nat) (h : b = a + n) :
    (L.drop a).take n ++ (L.drop b).take m = (L.drop a).take (n + m) := by
  subst h; rw [List.take_add, List.drop_drop]
theorem seg_merge_r {α : Type} (L : List α) (a n b m : Nat) (r : List α) (h : b = a + n) :
    (L.drop a).take n ++ ((L.drop b).take m ++ r) = (L.drop a).take (n + m) ++ r := by
  rw [← List.append_assoc, seg_merge L a n b m h]
theorem take_merge {α : Type} (L : List α) (n b m : Nat) (h : b = n) :
    L.take n ++ (L.drop b).take m = L.take (n + m) := by
  subst h; rw [List.take_add]
theorem take_merge_r {α : Type} (L : List α) (n b m : Nat) (r : List α) (h : b = n) :
    L.take n ++ ((L.drop b).take m ++ r) = L.take (n + m) ++ r := by
  rw [← List.append_assoc, take_merge L n b m h]
theorem seg_drop {α : Type} (L : List α) (a n b : Nat) (h : b = a + n) :
    (L.drop a).take n ++ L.drop b = L.drop a := by
  subst h; rw [← List.drop_drop]; exact List.take_append_drop n (L.drop a)
theorem seg_drop_r {α : Type} (L : List α) (a n b : Nat) (r : List α) (h : b = a + n) :
    (L.drop a).take n ++ (L.drop b ++ r) = L.drop a ++ r := by
  rw [← List.append_assoc, seg_drop L a n b h]
theorem take_drop' {α : Type} (L : List α) (n b : Nat) (h : b = n) : L.take n ++ L.drop b = L := by
  rw [h]; exact List.take_append_drop n L
theorem take_drop_r {α : Type} (L : List α) (n b : Nat) (r : List α) (h : b = n) :
    L.take n ++ (L.drop b ++ r) = L ++ r := by
  rw [← List.append_assoc, take_drop' L n b h]

end ECDSAAdd.Entrant.WSlimV3

namespace ECDSAAdd.Entrant.WSlimV3

/-- `∃ j, f j = q` over a `Fin n`-indexed family (reversed orientation) -/
scoped instance (priority := high) decExistsFinEq' (n q : Nat) (f : Fin n → Nat) :
    Decidable (∃ i : Fin n, f i = q) :=
  decidable_of_iff ((famMaskAux n f n (Nat.le_refl n)).testBit q = true) (by
    rw [famMaskAux_testBit]
    constructor
    · rintro ⟨i, _, e⟩; exact ⟨i, e⟩
    · rintro ⟨i, e⟩; exact ⟨i, i.isLt, e⟩)

end ECDSAAdd.Entrant.WSlimV3

namespace ECDSAAdd.Entrant.WSlimV3
theorem fin_getD_val {n : Nat} (l : List (Fin n)) (i : Nat) (d : Fin n) :
    (l.getD i d).val = (l.map Fin.val).getD i d.val := by
  induction l generalizing i with
  | nil => simp
  | cons a as _ => cases i <;> simp
end ECDSAAdd.Entrant.WSlimV3

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
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
  have rows : ∀ i : Fin 15, [1560, swaps i, hits i].Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  have apart : ∀ i j : Fin 15, i < j → hits j ≠ hits i ∧ swaps j ≠ hits i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : ((Partial.portal225).drop 391).take 384=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(947, 1556), (948, 1557), (949, 1558), (950, 1559), (951, 1560), (952, 1561), (953, 1562), (954, 1563), (955, 1564), (956, 1565), (957, 1566), (958, 1567), (959, 1568), (960, 1569), (961, 1570), (962, 1571), (963, 1572), (964, 1573), (965, 1574), (966, 1575), (967, 1576), (968, 1577), (969, 1578), (970, 1579), (971, 1580), (972, 1581), (973, 1582), (974, 1583), (975, 1584), (976, 1585), (977, 1586), (978, 1587), (979, 1588), (980, 1589), (981, 1590), (982, 1591), (983, 1592), (984, 1593), (985, 1594), (986, 1595), (987, 1596), (988, 1597), (989, 1598), (990, 1599), (991, 1600), (992, 1601), (993, 1602), (994, 1603), (995, 1604), (996, 1605), (997, 1606), (998, 1607), (999, 1608), (1000, 1609), (1001, 1610), (1002, 1611), (1003, 1612), (1004, 1613), (1005, 1614), (1006, 1615), (1007, 1616), (1008, 1617), (1009, 1618), (1010, 1619), (1011, 1620), (1012, 1621), (1013, 1622), (1014, 1623), (1015, 1624), (1016, 1625), (1017, 1626), (1018, 1627), (1019, 1628), (1020, 1629), (1021, 1630), (1022, 1631), (1023, 1632), (1024, 1633), (1025, 1634), (1026, 1635), (1027, 1636), (1028, 1637), (1029, 1638), (1030, 1639), (1031, 1640), (1032, 1641), (1033, 1642), (1034, 1643), (1035, 1644), (1036, 1645), (1037, 1646), (1038, 1647), (1039, 1648), (1040, 1649), (1041, 1650), (1042, 1651)]
def orientation := latch false (some 1721) 1722 946 orientationPairs
theorem orientation_layout : (1722::946::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : ((Partial.portal225).drop 778).take 388=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1721∉1722::946::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(425, 1558), (426, 1559), (427, 1560), (428, 1561), (429, 1562), (430, 1563), (431, 1564), (432, 1565), (433, 1566), (434, 1567), (435, 1568), (436, 1569), (437, 1570), (438, 1571), (439, 1572), (440, 1573), (441, 1574), (442, 1575), (443, 1576), (444, 1577), (445, 1578), (446, 1579), (447, 1580), (448, 1581), (449, 1582), (450, 1583), (451, 1584), (452, 1585), (453, 1586), (454, 1587), (455, 1588), (456, 1589), (457, 1590), (458, 1591), (459, 1592), (460, 1593), (461, 1594), (462, 1595), (463, 1596), (464, 1597), (465, 1598), (466, 1599), (467, 1600), (468, 1601), (469, 1602), (470, 1603), (471, 1604), (472, 1605), (473, 1606), (474, 1607), (475, 1608), (476, 1609), (477, 1610), (478, 1611), (479, 1612), (480, 1613), (481, 1614), (482, 1615), (483, 1616), (484, 1617), (485, 1618), (486, 1619), (487, 1620), (488, 1621), (489, 1622), (490, 1623), (491, 1624), (492, 1625), (493, 1626), (494, 1627), (495, 1628), (496, 1629), (497, 1630), (498, 1631), (499, 1632), (500, 1633), (501, 1634), (502, 1635), (503, 1636), (504, 1637), (505, 1638), (506, 1639), (507, 1640), (508, 1641), (509, 1642), (510, 1643), (511, 1644), (512, 1645), (513, 1646), (514, 1647), (515, 1648), (516, 1649), (517, 1650), (518, 1651), (519, 1652), (520, 1653), (521, 1654), (522, 1655), (523, 1656), (524, 1657), (525, 1658), (526, 1659), (527, 1660), (528, 1661)]
def threshold := latch true none 1556 1557 thresholdPairs
theorem threshold_layout : (1556::1557::sites thresholdPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem threshold_slice : ((Partial.portal270).drop 427).take 420=threshold := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
def orientationPairs : List (Wire×Wire) := [(924, 1556), (925, 1557), (926, 1558), (927, 1559), (928, 1560), (929, 1561), (930, 1562), (931, 1563), (932, 1564), (933, 1565), (934, 1566), (935, 1567), (936, 1568), (937, 1569), (938, 1570), (939, 1571), (940, 1572), (941, 1573), (942, 1574), (943, 1575), (944, 1576), (945, 1577), (946, 1578), (947, 1579), (948, 1580), (949, 1581), (950, 1582), (951, 1583), (952, 1584), (953, 1585), (954, 1586), (955, 1587), (956, 1588), (957, 1589), (958, 1590), (959, 1591), (960, 1592), (961, 1593), (962, 1594), (963, 1595), (964, 1596), (965, 1597), (966, 1598), (967, 1599), (968, 1600), (969, 1601), (970, 1602), (971, 1603), (972, 1604), (973, 1605), (974, 1606), (975, 1607), (976, 1608), (977, 1609), (978, 1610), (979, 1611), (980, 1612), (981, 1613), (982, 1614), (983, 1615), (984, 1616), (985, 1617), (986, 1618), (987, 1619), (988, 1620), (989, 1621), (990, 1622), (991, 1623), (992, 1624), (993, 1625), (994, 1626), (995, 1627), (996, 1628), (997, 1629), (998, 1630), (999, 1631), (1000, 1632), (1001, 1633), (1002, 1634), (1003, 1635), (1004, 1636), (1005, 1637), (1006, 1638), (1007, 1639), (1008, 1640), (1009, 1641), (1010, 1642), (1011, 1643), (1012, 1644), (1013, 1645), (1014, 1646), (1015, 1647), (1016, 1648), (1017, 1649), (1018, 1650), (1019, 1651), (1020, 1652), (1021, 1653), (1022, 1654), (1023, 1655), (1024, 1656), (1025, 1657), (1026, 1658), (1027, 1659), (1028, 1660)]
def orientation := latch false (some 1698) 1699 923 orientationPairs
theorem orientation_layout : (1699::923::sites orientationPairs).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_slice : ((Partial.portal270).drop 850).take 424=orientation := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem orientation_enable : 1698∉1699::923::sites orientationPairs := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
theorem emitted : Partial.portal225=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (240::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1723∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1722 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
theorem emitted : Partial.portal270=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem exchange_good : (285::RailPair.sites (railA.zip railB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem complement_good : railB.Nodup ∧ 1700∉railB := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem move_good : (RailPair.sites (bulkA.zip bulkB)).Nodup := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1699 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

/-- The stock walk over the ticks the 90..375 window (exit 390) replaces: [90,391). -/
theorem stock405 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 90 316)=139922 ∧
    measurementCount (Rolling1588TickGap.forward d 90 316)=70113 ∧
    toffoliCount (Rolling1588.reverse d 90 316)=139916 ∧
    measurementCount (Rolling1588.reverse d 90 316)=69833 := by
  have h := walks d 90 316 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

/-- The stock walk over the ticks the 120..255 window (exit 270) replaces: [120,271). -/
theorem stock120 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 120 151)=77511 ∧
    measurementCount (Rolling1588TickGap.forward d 120 151)=38781 ∧
    toffoliCount (Rolling1588.reverse d 120 151)=77470 ∧
    measurementCount (Rolling1588.reverse d 120 151)=38702 := by
  have h := walks d 120 151 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

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
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part1 : GatePhysical (enter225) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part2 : GatePhysical (routed ⟨10,by decide⟩ 0 1) := by
  exact (route ⟨10, by decide⟩ 0 1 (by decide)).1

theorem part3 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.packAtTick false 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part4 : GatePhysical (routed ⟨10,by decide⟩ 1 14) := by
  exact (route ⟨10, by decide⟩ 1 14 (by decide)).1

theorem part5 : GatePhysical (leave225) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part6 : GatePhysical (enter240) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part7 : GatePhysical (routed ⟨11,by decide⟩ 0 1) := by
  exact (route ⟨11, by decide⟩ 0 1 (by decide)).1

theorem part8 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.packAtTick false 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part9 : GatePhysical (archiveLoad240 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad240
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.load1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part10 : GatePhysical (routed ⟨11,by decide⟩ 1 14) := by
  exact (route ⟨11, by decide⟩ 1 14 (by decide)).1

theorem part11 : GatePhysical (leave240) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part12 : GatePhysical (enter255) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part13 : GatePhysical (routed ⟨12,by decide⟩ 0 1) := by
  exact (route ⟨12, by decide⟩ 0 1 (by decide)).1

theorem part14 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.packAtTick false 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part15 : GatePhysical (archiveLoad255 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad255
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.load1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part16 : GatePhysical (routed ⟨12,by decide⟩ 1 14) := by
  exact (route ⟨12, by decide⟩ 1 14 (by decide)).1

theorem part17 : GatePhysical (leave255) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part18 : GatePhysical (park270) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part19 : GatePhysical (portal270Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

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
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part22 : GatePhysical (archiveLoad270 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad270
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.load1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part23 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.packAtTick true 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part24 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.packAtTick true 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part25 : GatePhysical (archiveLoad240 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad240
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.load0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part26 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.packAtTick true 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part27 : GatePhysical (archiveLoad255 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad255
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.load0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part28 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.packAtTick true 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part29 : GatePhysical (archiveLoad270 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveLoad270
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.load0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part30 : GatePhysical (archiveRestore270 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore270
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.restore1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part31 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick false 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part32 : GatePhysical (renameProgram (OB5.sig 270) (W.ReverseCarry.compactReceiverTick base 270)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact W.ReverseCarry.compactReceiverTick_physical base 270 (by decide) base_pool_nodup

theorem part33 : GatePhysical (portal270) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part34 : GatePhysical (park270Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part35 : GatePhysical (leave255Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part36 : GatePhysical (unrouted ⟨12,by decide⟩ 1 14) := by
  exact (route ⟨12, by decide⟩ 1 14 (by decide)).2

theorem part37 : GatePhysical (archiveRestore255 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore255
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.restore1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part38 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick false 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

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
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part41 : GatePhysical (leave240Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part42 : GatePhysical (unrouted ⟨11,by decide⟩ 1 14) := by
  exact (route ⟨11, by decide⟩ 1 14 (by decide)).2

theorem part43 : GatePhysical (archiveRestore240 false) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore240
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, Bool.false_eq_true, ReducedWindowArchives.restore1]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part44 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick false 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part45 : GatePhysical (unrouted ⟨11,by decide⟩ 0 1) := by
  exact (route ⟨11, by decide⟩ 0 1 (by decide)).2

theorem part46 : GatePhysical (enter240Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part47 : GatePhysical (leave225Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part48 : GatePhysical (unrouted ⟨10,by decide⟩ 1 14) := by
  exact (route ⟨10, by decide⟩ 1 14 (by decide)).2

theorem part49 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick false 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part50 : GatePhysical (unrouted ⟨10,by decide⟩ 0 1) := by
  exact (route ⟨10, by decide⟩ 0 1 (by decide)).2

theorem part51 : GatePhysical (enter225Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part52 : GatePhysical (portal225Inv) := by
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part53 : GatePhysical (archiveRestore270 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore270
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.restore0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part54 : GatePhysical (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick true 260)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 270 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part55 : GatePhysical (archiveRestore255 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore255
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.restore0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part56 : GatePhysical (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick true 245)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 255 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part57 : GatePhysical (archiveRestore240 true) := by
  apply physicalGateCheck_correct
  unfold Partial.archiveRestore240
  rw [ECDSAAdd.Entrant.WSlimV3.rename_getD _ 11]
  · simp only [↓reduceIte, ReducedWindowArchives.restore0]
    (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part58 : GatePhysical (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick true 230)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 240 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

theorem part59 : GatePhysical (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick true 225)) := by
  apply gatePhysical_rename _ (OB5.sig_injective 225 (by decide))
  exact physicalGateCheck_correct _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack 401 402 1557 1556 1721 1722 946 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 403 948 1556 (PortalBorrow.restore bulkA bulkB carry 1722 1556)
theorem emitted_back : Partial.portal225Inv=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 401 402 1557 1556 1721 1722 946 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 403 948 1556 (Companion.erase bulkA bulkB carry 1722 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
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
theorem emitted_back : Partial.portal270Inv=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags 423 424 1557 1556 1698 1699 923 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 425 925 1556 (Companion.erase bulkA bulkB carry 1699 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1698,1699,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem part55 : gateSlots (archiveRestore255 true) ≤ 12242 := by
  have move : gateSlots moveRestore255 = 54 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  simp only [archiveRestore255,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore0_counts.2.2.2,move]
  decide

theorem part56 : gateSlots (Rolling1588.unpackAtTick true 245) ≤ 166 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part57 : gateSlots (archiveRestore240 true) ≤ 12242 := by
  have move : gateSlots moveRestore240 = 54 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  simp only [archiveRestore240,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.restore0_counts.2.2.2,move]
  decide

theorem part58 : gateSlots (Rolling1588.unpackAtTick true 230) ≤ 166 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part59 : gateSlots (Rolling1588.unpackAtTick true 225) ≤ 166 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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

theorem part21 : gateSlots (Rolling1588.packAtTick false 260) ≤ 156 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part22 : gateSlots (archiveLoad270 false) ≤ 15988 := by
  have move : gateSlots moveLoad270 = 33 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  simp only [archiveLoad270,gateSlots_append,rename_gateSlots,Bool.false_eq_true,if_true,if_false,ReducedWindowArchives.load1_counts.2.2.2,move]
  decide

theorem part23 : gateSlots (Rolling1588.packAtTick true 225) ≤ 168 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem part24 : gateSlots (Rolling1588.packAtTick true 230) ≤ 168 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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

end ECDSAAdd.Entrant.StairPacket.PartialPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1723 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 401 402 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 946 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1721 f) 1722 u⟩ := by
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
    run Partial.portal225Inv tape (run Partial.portal225 m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1721 ∧ q≠1722 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1700 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=PortalAnd.high 423 424 thresholdPairs s.basis
    let u:=f && (PortalAnd.digits 923 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1698 f) 1699 u⟩ := by
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
    run Partial.portal270Inv tape (run Partial.portal270 m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1698 ∧ q≠1699 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Partial StairArchiveGates Baselines Challenge
set_option maxRecDepth 180000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem forward45plus1_false_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 2030 → x1 ≤ 93 → x2 ≤ 5000 → x3 ≤ 156 → x4 ≤ 70000 → x5 ≤ 3489 → x6 ≤ 93 → x7 ≤ 5000 → x8 ≤ 156 → x9 ≤ 15988 → x10 ≤ 70000 → x11 ≤ 3704 → x12 ≤ 93 → x13 ≤ 5000 → x14 ≤ 156 → x15 ≤ 15988 → x16 ≤ 70000 → x17 ≤ 3837 → x18 ≤ 9 → x19 ≤ 2219 → x20 ≤ 6004 → x21 ≤ 156 → x22 ≤ 15988 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 295159 := by omega

private theorem forward45plus1_true_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 2030 → x1 ≤ 93 → x2 ≤ 5000 → x3 ≤ 168 → x4 ≤ 70000 → x5 ≤ 3489 → x6 ≤ 93 → x7 ≤ 5000 → x8 ≤ 168 → x9 ≤ 15978 → x10 ≤ 70000 → x11 ≤ 3704 → x12 ≤ 93 → x13 ≤ 5000 → x14 ≤ 168 → x15 ≤ 15978 → x16 ≤ 70000 → x17 ≤ 3837 → x18 ≤ 9 → x19 ≤ 2219 → x20 ≤ 6004 → x21 ≤ 168 → x22 ≤ 15978 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 295177 := by omega

private theorem reverse45plus1_false_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 12262 → x1 ≤ 154 → x2 ≤ 6001 → x3 ≤ 2219 → x4 ≤ 9 → x5 ≤ 3838 → x6 ≤ 70000 → x7 ≤ 12262 → x8 ≤ 154 → x9 ≤ 5000 → x10 ≤ 93 → x11 ≤ 3705 → x12 ≤ 70000 → x13 ≤ 12262 → x14 ≤ 154 → x15 ≤ 5000 → x16 ≤ 93 → x17 ≤ 3490 → x18 ≤ 70000 → x19 ≤ 154 → x20 ≤ 5000 → x21 ≤ 93 → x22 ≤ 2030 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 283973 := by omega

private theorem reverse45plus1_true_sum (x0:Nat) (x1:Nat) (x2:Nat) (x3:Nat) (x4:Nat) (x5:Nat) (x6:Nat) (x7:Nat) (x8:Nat) (x9:Nat) (x10:Nat) (x11:Nat) (x12:Nat) (x13:Nat) (x14:Nat) (x15:Nat) (x16:Nat) (x17:Nat) (x18:Nat) (x19:Nat) (x20:Nat) (x21:Nat) (x22:Nat) : x0 ≤ 12242 → x1 ≤ 166 → x2 ≤ 6001 → x3 ≤ 2219 → x4 ≤ 9 → x5 ≤ 3838 → x6 ≤ 70000 → x7 ≤ 12242 → x8 ≤ 166 → x9 ≤ 5000 → x10 ≤ 93 → x11 ≤ 3705 → x12 ≤ 70000 → x13 ≤ 12242 → x14 ≤ 166 → x15 ≤ 5000 → x16 ≤ 93 → x17 ≤ 3490 → x18 ≤ 70000 → x19 ≤ 166 → x20 ≤ 5000 → x21 ≤ 93 → x22 ≤ 2030 → x0+x1+x2+x3+x4+x5+x6+x7+x8+x9+x10+x11+x12+x13+x14+x15+x16+x17+x18+x19+x20+x21+x22 ≤ 283961 := by omega

end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open LeaveSelector
def ports : Ports := ⟨241,401,1724,1725⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open LeaveSelector
def ports : Ports := ⟨256,408,1716,1717⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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

-- one-pass parity masks for LeaveSelector.parityAt (scoped instance decParityAt)
namespace ECDSAAdd.Entrant.WSlimV3
-- one-pass parity masks: decide `parityAt q P = b` for many q with two masks of P (cached per program)

def xMask : Program → Nat
  | [] => 0
  | .X t :: is => 2 ^ t ^^^ xMask is
  | _ :: is => xMask is

def tMask : Program → Nat
  | [] => 0
  | .X _ :: is => tMask is
  | .CX _ t :: is => 2 ^ t ||| tMask is
  | .CCX _ _ t :: is => 2 ^ t ||| tMask is
  | .measureX t _ _ :: is => 2 ^ t ||| tMask is

theorem parityAt_masks (q : Nat) : ∀ P : Program,
    ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt q P =
      if (tMask P).testBit q then none else some ((xMask P).testBit q)
  | [] => by simp [ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt, tMask, xMask]
  | i :: is => by
    have ih := parityAt_masks q is
    cases i with
    | X t =>
      simp only [ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt, tMask, xMask, Nat.testBit_xor,
        Nat.testBit_two_pow, ih]
      by_cases h : q = t
      · subst h; cases (tMask is).testBit q <;> simp
      · have h' : ¬ t = q := fun e => h e.symm
        simp [h, h']
    | CX a t =>
      simp only [ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt, tMask, xMask, Nat.testBit_or,
        Nat.testBit_two_pow, ih]
      by_cases h : q = t
      · subst h; simp
      · have h' : ¬ t = q := fun e => h e.symm
        simp [h, h']
    | CCX a b t =>
      simp only [ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt, tMask, xMask, Nat.testBit_or,
        Nat.testBit_two_pow, ih]
      by_cases h : q = t
      · subst h; simp
      · have h' : ¬ t = q := fun e => h e.symm
        simp [h, h']
    | measureX t c d =>
      simp only [ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt, tMask, xMask, Nat.testBit_or,
        Nat.testBit_two_pow, ih]
      by_cases h : q = t
      · subst h; simp
      · have h' : ¬ t = q := fun e => h e.symm
        simp [h, h']

/-- `parityAt q P = b` decided from two masks of `P` -/
scoped instance (priority := high) decParityAt (q : Nat) (P : Program) (b : Option Bool) :
    Decidable (ECDSAAdd.Entrant.StairPacket.LeaveSelector.parityAt q P = b) :=
  decidable_of_iff ((if (tMask P).testBit q then none else some ((xMask P).testBit q)) = b)
    (by rw [parityAt_masks])

end ECDSAAdd.Entrant.WSlimV3

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open Arithmetic CodecBitSliceVerify StairArchiveGates StairArchiveIntegerHook
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

def op (loading select : Bool) : Operation :=
  if loading then (if select then .load0 else .load1) else (if select then .restore0 else .restore1)

def raw : Cols := integer_load0Trace0In.take 23
def code (select : Bool) : Cols :=
  (if select then ReducedWindowArchives.load0StoredOut else ReducedWindowArchives.load1StoredOut).take 16
def startCols (loading select:Bool) := if loading then raw else code select
def endCols (loading select:Bool) := if loading then code select else raw

theorem io (loading select:Bool) (i:Fin 157) :
    get (input (op loading select)) i=get (startCols loading select) i ∧
    get (output (op loading select)) i=get (endCols loading select) i := by
  revert i
  cases loading <;> cases select <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem blank (loading select:Bool) (i:Fin 157) (h : 23≤ i.val) :
    get (startCols loading select) i=0 ∧ get (endCols loading select) i=0 := by
  revert i
  cases loading <;> cases select <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
  | false, false => [0, 0, 1, 2, 4, 62, 18, 21, 8, 8, 9, 10, 12, 69, 70, 71, 0, 1, 2, 5, 3, 9, 10]
  | false, true => [0, 0, 1, 2, 4, 62, 18, 21, 8, 8, 9, 10, 12, 69, 70, 71, 0, 1, 2, 5, 3, 9, 10]
  | true, false => [3, 0, 1, 2, 8, 9, 39, 44, 40, 46, 119, 116, 117, 118, 124, 125, 155, 160, 156, 162, 276, 232, 232]
  | true, true => [39, 44, 40, 46, 7, 8, 3, 0, 1, 2, 155, 160, 156, 162, 123, 124, 119, 116, 117, 118, 275, 232, 232]

private theorem marked (loading select:Bool) : ∀i:Fin 23,
    ((program (op loading select))[(marks loading select).getD i 0]?).any
      (fun g => decide (i.val ∈ g.wires))=true := by
  cases loading <;> cases select <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
  cases loading <;> cases select <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

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
    let t:=run (Partial.archiveLoad240 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [246,1274,247,1275,248,249,1277,250,251,1279,252,1280,253,254,1282,255,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1276,249),(249,1277),(1277,250),(250,251),(1278,1279),(251,252),(1279,1280),(252,253),(1280,254),(253,1282),(1281,255),(254,1556),(1282,1557),(255,1558),(1283,1559),(1716,1560),(1717,1561),(1718,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore240 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
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
    let t:=run (Partial.archiveRestore240 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
    let t:=run (Partial.archiveLoad255 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [261,1289,262,1290,263,264,1292,265,266,1294,267,1295,268,269,1297,270,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1291,264),(264,1292),(1292,265),(265,266),(1293,1294),(266,267),(1294,1295),(267,268),(1295,269),(268,1297),(1296,270),(269,1556),(1297,1557),(270,1558),(1298,1559),(1709,1560),(1710,1561),(1711,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore255 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
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
    let t:=run (Partial.archiveRestore255 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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

namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ
open Arithmetic ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic window archive (par-c2). The archive of block `i` (cells of ticks `t-10..t-1`, `t = start i+15`,
flags `e0(t)+6..8` written by block `i`'s leave, codec scratch `scratchS t`) is loaded inside block `i+1` by
`archiveLoadP i`. dadon's `ArchiveBoundary{t}` is `ArchiveJ` at `i = (t-90)/15`. Port lists = a short head
(cells, flags; checked by `decide` over the blocks) and the 134-wire scratch block `scratchS t` (generic).
Window form for `i ≤ 20` (`t ≤ 390`). -/

def rawHead (i : Fin 23) : List Wire := cellsLoadP (start i+15)++[e0P (start i+15)+6,e0P (start i+15)+6+1,e0P (start i+15)+6+2]
def scratch (i : Fin 23) : List Wire := (List.range 134).map (scratchS (start i+15))
def rawPortsList (i : Fin 23) : List Wire :=
  loadPortsWP (start i+15) (e0P (start i+15)+6)++[scratchS (start i+15) 132,scratchS (start i+15) 133]
def rawPorts (i : Fin 23) (q : Fin 157) : Wire := (rawPortsList i).getD q 0
def codeTail (i : Fin 23) : List Wire :=
  [OB5.sig (start i+15) (start i+15+1036),OB5.sig (start i+15) (start i+15+1038),OB5.sig (start i+15) (start i+15+1041),
   OB5.sig (start i+15) (start i+15+1043),e0P (start i+15)+6,e0P (start i+15)+7,e0P (start i+15)+8]
def codePortsList (i : Fin 23) : List Wire := restorePortsWP (start i+15)++codeTail i
def codePorts (i : Fin 23) (q : Fin 157) : Wire := (codePortsList i).getD q 0
def loadMap (i : Fin 23) (q : Wire) : Wire := (loadPortsWP (start i+15) (e0P (start i+15)+6)).getD q 0
def restoreMap (i : Fin 23) (q : Wire) : Wire := (restorePortsWP (start i+15)).getD q 0
def loadMoves (i : Fin 23) : List (Wire×Wire) := (moveLoadPairs (start i+15)).map Prod.swap
def restoreMoves (i : Fin 23) : List (Wire×Wire) := (moveRestorePairs (start i+15) (e0P (start i+15)+6)).map Prod.swap
def loadRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,17,16,18,19,20,21,22]
def loadRoute (k : Fin 157) := loadRouteList.getD k 0
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (k : Fin 157) := restoreRouteList.getD k 0
/-- Wires the scratch block never takes: below 1556 off the hosts `[1302-t, 933]` (from tick 369), from 1700 on, or
in the live block `e0..e0+9`. -/
def Band (t q : Nat) : Prop :=
  (q<1301 ∧ (q+t<1302 ∨ 933<q ∨ t<369)) ∨ (1044+t<q ∧ q<1556) ∨ 2069≤q+t ∨ 1700≤q ∨ ∃c<10, q=e0P t+c
instance (t q : Nat) : Decidable (Band t q) := by unfold Band; infer_instance

theorem band_off (t : Nat) (ht : t<512) {q k : Nat} (hk : k<134) (h : Band t q) : scratchS t k≠q := by
  have b:=scratchW_bounds t k
  have l:=scratchW_le t k hk
  have he:1574≤e0P t:=by unfold e0P; omega
  rcases scratchS_cases t k ht hk with ⟨e1, lo, hi, nm⟩ | ⟨t369, lo, hi⟩
  · rw [e1] at lo hi nm ⊢
    rcases h with h|h|h|h|⟨c,hc,rfl⟩
    · omega
    · omega
    · omega
    · omega
    · exact scratchW_ne_e0 t k c hc
  · rcases h with h|h|h|h|⟨c,hc,rfl⟩ <;> omega
theorem tick_lt (i : Fin 23) : start i+15<512 := by have:=i.isLt; simp only [start]; omega

theorem rawLength (i : Fin 23) : (rawPortsList i).length=157 := by
  simp only [rawPortsList,List.length_append,loadPortsWP_length,List.length_cons,List.length_nil]
theorem codeLength (i : Fin 23) : (codePortsList i).length=157 := by
  simp only [codePortsList,List.length_append,restorePortsWP_length,codeTail,List.length_cons,List.length_nil]
theorem range_two (f : Nat → Nat) (n : Nat) : (List.range n).map f++[f n,f (n+1)]=(List.range (n+2)).map f := by
  rw [List.range_succ,List.range_succ,List.map_append,List.map_append]
  simp only [List.append_assoc,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
theorem raw_split (i : Fin 23) : rawPortsList i=rawHead i++scratch i := by
  simp only [rawPortsList,rawHead,scratch,loadPortsWP,List.append_assoc]
  rw [range_two]
theorem code_split (i : Fin 23) : codePortsList i=cellsRestoreP (start i+15)++scratch i++codeTail i := by
  simp only [codePortsList,restorePortsWP,scratch]
theorem raw_scratch (i : Fin 23) {k : Nat} (hk : k<134) : (rawPortsList i).getD (23+k) 0=scratchS (start i+15) k := by
  rw [raw_split,List.getD_append_right _ _ _ _ (by simp [rawHead,cellsLoadP]),scratch]
  have e:23+k-(rawHead i).length=k:=by simp [rawHead,cellsLoadP]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl
theorem code_scratch (i : Fin 23) {k : Nat} (hk : k<134) : (codePortsList i).getD (16+k) 0=scratchS (start i+15) k := by
  rw [codePortsList,List.getD_append _ _ _ _ (by rw [restorePortsWP_length]; omega),restorePortsWP_scratch _ _ hk]
theorem rawIndex (i : Fin 23) {q : Wire} (h : q∈rawPortsList i) : ∃k:Fin 157, rawPorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(rawLength i) ▸ hn⟩,?_⟩
  rw [rawPorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq
theorem codeIndex (i : Fin 23) {q : Wire} (h : q∈codePortsList i) : ∃k:Fin 157, codePorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(codeLength i) ▸ hn⟩,?_⟩
  rw [codePorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq
theorem scratch_mem (i : Fin 23) {k : Nat} (hk : k<134) : scratchS (start i+15) k∈scratch i :=
  List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩
theorem scratch_nodup (i : Fin 23) : (scratch i).Nodup :=
  List.Nodup.map_on (fun a ha b hb h=>scratchS_inj _ a b (tick_lt i) (List.mem_range.mp ha) (List.mem_range.mp hb) h)
    List.nodup_range

/-- Head facts, one `decide` over the window archives `i ≤ 18` (short lists only). -/
theorem heads_all : ∀ i : Fin 23, i.val≤21 →
    (rawHead i).Nodup ∧ (∀q∈rawHead i, Band (start i+15) q) ∧
    (cellsRestoreP (start i+15)++codeTail i).Nodup ∧ (∀q∈cellsRestoreP (start i+15)++codeTail i, Band (start i+15) q) ∧
    (∀q∈cellsRestoreP (start i+15)++codeTail i, q∈rawHead i) ∧
    (∀p∈loadMoves i, p.1∈rawHead i ∧ p.2∈rawHead i ∧ p.1≠p.2) ∧
    (∀p∈restoreMoves i, p.1≠p.2 ∧ (p.1∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.1=scratchS (start i+15) c) ∧
      (p.2∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.2=scratchS (start i+15) c)) := by
  decide +kernel
theorem routes_head_all : ∀ i : Fin 23, i.val≤21 → ∀k:Fin 157,
    ((k.val<16 ∨ 150≤k.val) → backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k)) ∧
    (k.val<30 → backMap (restoreMoves i) (rawPorts i k)=codePorts i (restoreRoute k)) := by
  decide +kernel
theorem routes_mid : ∀k:Fin 157, (16≤k.val → k.val<150 → (loadRoute k).val=k.val+7) ∧
    (30≤k.val → (restoreRoute k).val+7=k.val) := by decide +kernel
theorem load_sort : ∀ k, loadRoute k=k ∨ (16≤ k.val ∧ 16≤(loadRoute k).val) := by decide +kernel
theorem restore_sort : ∀ k, restoreRoute k=k ∨ (23≤ k.val ∧ 23≤(restoreRoute k).val) := by decide +kernel

theorem rawNodup (i : Fin 23) (hi : i.val≤21) : (rawPortsList i).Nodup := by
  obtain ⟨hn,hb,-⟩:=heads_all i hi
  rw [raw_split,List.nodup_append]
  refine ⟨hn,scratch_nodup i,?_⟩
  intro a ha b hb' eq
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hb'
  exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb a ha) eq.symm
theorem codeNodup (i : Fin 23) (hi : i.val≤21) : (codePortsList i).Nodup := by
  obtain ⟨-,-,hn,hb,-⟩:=heads_all i hi
  rw [code_split,List.nodup_append,List.nodup_append]
  rw [List.nodup_append] at hn
  refine ⟨⟨hn.1,scratch_nodup i,?_⟩,hn.2.1,?_⟩
  · intro a ha b hb' eq
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hb'
    exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb a (List.mem_append_left _ ha)) eq.symm
  · intro a ha b hb' eq
    rcases List.mem_append.mp ha with ha|ha
    · exact hn.2.2 a ha b hb' eq
    · obtain ⟨k,hk,rfl⟩:=List.mem_map.mp ha
      exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb b (List.mem_append_right _ hb')) eq
theorem load_unique (i : Fin 23) (hi : i.val≤21) : Function.Injective (rawPorts i) :=
  injective_list (rawPortsList i) (rawLength i) (rawNodup i hi)
theorem restore_unique (i : Fin 23) (hi : i.val≤21) : Function.Injective (codePorts i) :=
  injective_list (codePortsList i) (codeLength i) (codeNodup i hi)
theorem load_map (i : Fin 23) : ∀q:Fin 155, loadMap i q=rawPorts i ⟨q,by omega⟩ := by
  intro q
  simp only [loadMap,rawPorts,rawPortsList]
  rw [List.getD_append _ _ _ _ (by rw [loadPortsWP_length]; exact q.isLt)]
theorem restore_map (i : Fin 23) : ∀q:Fin 150, restoreMap i q=codePorts i ⟨q,by omega⟩ := by
  intro q
  simp only [restoreMap,codePorts,codePortsList]
  rw [List.getD_append _ _ _ _ (by rw [restorePortsWP_length]; exact q.isLt)]

theorem load_route (i : Fin 23) (hi : i.val≤21) : ∀k,backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k) := by
  intro k
  by_cases h:k.val<16 ∨ 150≤k.val
  · exact (routes_head_all i hi k).1 h
  · have m:=(routes_mid k).1 (by omega) (by omega)
    have hc:codePorts i k=scratchS (start i+15) (k.val-16):=by
      have e:=code_scratch i (k:=k.val-16) (by omega); rw [show 16+(k.val-16)=k.val by omega] at e; exact e
    have hr:rawPorts i (loadRoute k)=scratchS (start i+15) (k.val-16):=by
      have e:=raw_scratch i (k:=k.val-16) (by omega); rw [show 23+(k.val-16)=k.val+7 by omega,← m] at e; exact e
    rw [hc,hr]
    apply backMap_outside
    intro p hp
    obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
    have b:=(heads_all i hi).2.1
    exact ⟨band_off _ (tick_lt i) (by omega) (b _ h1),band_off _ (tick_lt i) (by omega) (b _ h2)⟩
theorem restore_route (i : Fin 23) (hi : i.val≤21) :
    ∀k,backMap (restoreMoves i) (rawPorts i k)=codePorts i (restoreRoute k) := by
  intro k
  by_cases h:k.val<30
  · exact (routes_head_all i hi k).2 h
  · have m:=(routes_mid k).2 (by omega)
    have hr:rawPorts i k=scratchS (start i+15) (k.val-23):=by
      have e:=raw_scratch i (k:=k.val-23) (by omega); rw [show 23+(k.val-23)=k.val by omega] at e; exact e
    have hc:codePorts i (restoreRoute k)=scratchS (start i+15) (k.val-23):=by
      have e:=code_scratch i (k:=k.val-23) (by omega); rw [show 16+(k.val-23)=(restoreRoute k).val by omega] at e; exact e
    rw [hr,hc]
    apply backMap_outside
    intro p hp
    obtain ⟨-,h1,h2⟩:=(heads_all i hi).2.2.2.2.2.2 p hp
    have b:=(heads_all i hi).2.2.2.1
    have off (q : Wire) (hq : q∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, q=scratchS (start i+15) c) :
        scratchS (start i+15) (k.val-23)≠q := by
      rcases hq with hq|⟨c,hc,rfl⟩
      · exact band_off _ (tick_lt i) (by omega) (b _ hq)
      · intro eq; have:=scratchS_inj _ _ _ (tick_lt i) (by omega) (by omega) eq; omega
    exact ⟨off _ h1,off _ h2⟩

theorem load_scope (i : Fin 23) (hi : i.val≤21) : ∀p∈loadMoves i,(∃k,rawPorts i k=p.1) ∧ (∃k,rawPorts i k=p.2) := by
  intro p hp
  obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
  exact ⟨rawIndex i (raw_split i ▸ List.mem_append_left _ h1),rawIndex i (raw_split i ▸ List.mem_append_left _ h2)⟩
theorem restore_scope (i : Fin 23) (hi : i.val≤21) : ∀p∈restoreMoves i,(∃k,codePorts i k=p.1) ∧ (∃k,codePorts i k=p.2) := by
  intro p hp
  obtain ⟨-,h1,h2⟩:=(heads_all i hi).2.2.2.2.2.2 p hp
  have mem (q : Wire) (hq : q∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, q=scratchS (start i+15) c) :
      q∈codePortsList i := by
    rw [code_split]
    rcases hq with hq|⟨c,hc,rfl⟩
    · rcases List.mem_append.mp hq with hq|hq
      · exact List.mem_append_left _ (List.mem_append_left _ hq)
      · exact List.mem_append_right _ hq
    · exact List.mem_append_left _ (List.mem_append_right _ (scratch_mem i (by omega)))
  exact ⟨codeIndex i (mem _ h1),codeIndex i (mem _ h2)⟩
theorem load_proper (i : Fin 23) (hi : i.val≤21) : ∀p∈loadMoves i,p.1≠p.2 :=
  fun p hp=>((heads_all i hi).2.2.2.2.2.1 p hp).2.2
theorem restore_proper (i : Fin 23) (hi : i.val≤21) : ∀p∈restoreMoves i,p.1≠p.2 :=
  fun p hp=>((heads_all i hi).2.2.2.2.2.2 p hp).1

theorem load_program (i : Fin 23) (d : Bool) : archiveLoadP i d=placed (loadMap i) (op true d)++moves (loadMoves i) := by
  cases d <;> rfl
theorem restore_program (i : Fin 23) (d : Bool) :
    archiveRestoreP i d=placed (restoreMap i) (op false d)++moves (restoreMoves i) := by
  cases d <;> rfl

theorem load_run (i : Fin 23) (hi : i.val≤21) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (rawPorts i) (startCols true d) row s) :
    let t:=run (archiveLoadP i d) m s
    t.phase=s.phase ∧ Frame (codePorts i) (endCols true d) row t ∧ ∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d (rawPorts i) (codePorts i) (loadMap i) (loadMoves i) loadRoute (load_unique i hi) _
    (load_proper i hi) (load_route i hi) load_sort (load_scope i hi) row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map i ⟨q,lim⟩⟩
theorem restore_run (i : Fin 23) (hi : i.val≤21) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (codePorts i) (startCols false d) row s) :
    let t:=run (archiveRestoreP i d) m s
    t.phase=s.phase ∧ Frame (rawPorts i) (endCols false d) row t ∧ ∀q,(∀k,codePorts i k≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d (codePorts i) (rawPorts i) (restoreMap i) (restoreMoves i) restoreRoute (restore_unique i hi) _
    (restore_proper i hi) (restore_route i hi) restore_sort (restore_scope i hi) row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map i ⟨q,lim⟩⟩
theorem code_from_raw (i : Fin 23) (hi : i.val≤21) : ∀k,∃m,rawPorts i m=codePorts i k := by
  intro k
  have sub:=(heads_all i hi).2.2.2.2.1
  have mem:codePorts i k∈codePortsList i:=by
    rw [codePorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ((codeLength i).symm ▸ k.isLt),Option.getD_some]
    exact List.getElem_mem _
  apply rawIndex i
  rw [raw_split]
  rw [code_split] at mem
  rcases List.mem_append.mp mem with mem|mem
  · rcases List.mem_append.mp mem with mem|mem
    · exact List.mem_append_left _ (sub _ (List.mem_append_left _ mem))
    · exact List.mem_append_right _ mem
  · exact List.mem_append_left _ (sub _ (List.mem_append_right _ mem))
theorem roundtrip (i : Fin 23) (hi : i.val≤21) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame (rawPorts i) raw row s) :
    run (archiveRestoreP i d) n (run (archiveLoadP i d) m s)=s := by
  have f:=load_run i hi d row hr s m ready
  have b:=restore_run i hi d row hr _ n f.2.1
  apply state_eq
  · exact b.1.trans f.1
  · intro q
    by_cases h:∃k,rawPorts i k=q
    · obtain ⟨k,rfl⟩:=h
      exact (b.2.1 k).trans (ready k).symm
    · have no:∀k,rawPorts i k≠q:=fun k eq=>h ⟨k,eq⟩
      have noc:∀k,codePorts i k≠q:=by
        intro k; obtain ⟨m,eq⟩:=code_from_raw i hi k
        exact eq ▸ no m
      exact (b.2.2 q noc).trans (f.2.2 q no)

end ECDSAAdd.Entrant.StairPacket.ArchiveJ

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
    let t:=run (Partial.archiveLoad270 d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [276,1809,277,1808,278,279,1806,280,281,1804,282,1803,283,284,1801,285,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := [(1807,279),(279,1806),(1806,280),(280,281),(1805,1804),(281,282),(1804,1803),(282,283),(1803,284),(283,1801),(1802,285),(284,1556),(1801,1557),(285,1558),(1800,1559),(1029,1560),(1030,1561),(1031,1562)]
def restoreRouteList : List (Fin 157) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,151,150,152,153,154,155,156,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149]
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : Partial.archiveRestore270 d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
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
    let t:=run (Partial.archiveRestore270 d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
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
    get (code select) i = get (if select then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) i := by
  revert i
  cases select <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ArchivePortAction
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary240
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
theorem load_record (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀i:Fin 157,i.val<23 → s.basis (rawPorts i)=data i)
    (scratch:∀i:Fin 157,23≤ i.val → s.basis (rawPorts i)=false) :
    let t:=run (Partial.archiveLoad240 d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame codePorts (code d) row t ∧
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) i).testBit row) ∧
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
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) i).testBit row) ∧
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
        (∀i:Fin 16,t.basis (codePorts ⟨i,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) i).testBit row) ∧
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
end
section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveJ
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
theorem load_record (i : Fin 23) (hi : i.val≤21) (d:Bool) (data:Nat→Bool) (s:State) (m:List Bool)
    (legal:∃row<63145,∀q<23,(rawCol q).testBit row=data q)
    (recorded:∀k:Fin 157,k.val<23 → s.basis (rawPorts i k)=data k)
    (blank:∀k:Fin 157,23≤ k.val → s.basis (rawPorts i k)=false) :
    let t:=run (Partial.archiveLoadP i d) m s
    ∃row<63145, t.phase=s.phase ∧ Frame (codePorts i) (code d) row t ∧
        (∀k:Fin 16,t.basis (codePorts i ⟨k,by omega⟩)=(get (if d then ReducedWindowArchives.enter0StoredIn else ReducedWindowArchives.enter1StoredIn) k).testBit row) ∧
        (∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q) ∧
        (∀ tape, run (Partial.archiveRestoreP i d) tape t=s) := by
  obtain ⟨row,hr,h⟩:=legal
  have ready:=starting_frame (rawPorts i) s row data h recorded blank
  have ⟨ph,fr,away⟩:=load_run i hi d row hr s m ready
  refine ⟨row,hr,ph,fr,?_,away,fun tape=>roundtrip i hi d row hr s m tape ready⟩
  intro k
  exact (fr ⟨k,by omega⟩).trans (congrArg (fun x:Nat=>x.testBit row) (field_bits d k))
end ECDSAAdd.Entrant.StairPacket.ArchiveJ

end

-- ==== w4: switch: WindowParams, WindowCovered, WindowPhysical moved from Window (FirstHit end) ====

-- BEGIN par-d WindowParams
-- Record (loan720b): after par-b's Partial section (which needs GateMirror, Window:8322) and par-d's WindowFold.
-- B2-a changes vs par-d's draft: additive measure_* (no Stair44Resources.tc/mc, which live in Main), portal_counts by
-- tick (par-b 452ff03), first-ship window 120..255 (exit 270), record cross-check at 225..255.
section

namespace ECDSAAdd.Entrant.StairPacket.WindowParams
open Arithmetic MappedCompressed Partial WindowFold Baselines Challenge StairArchiveGates
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] enterP enterInvP leaveP leaveInvP leaveMoveP leaveMoveInvP archiveLoadP archiveRestoreP portalP portalInvP parkP parkInvP
  exitLoadP exitRestoreP StairPacket.routed StairPacket.unrouted Rolling1588.packAtTick Rolling1588.unpackAtTick

/-- par-b's parametric pieces. -/
def params : Pieces Program :=
  ofParts enterP enterInvP leaveMoveP leaveMoveInvP archiveLoadP archiveRestoreP portalP portalInvP parkP parkInvP
    exitLoadP exitRestoreP

/-- The window: blocks 1..20 (ticks 90..375), exit tick 390. -/
def first : Fin 23 := ⟨1,by decide⟩
def rest : List (Fin 23) := (List.finRange 23).filter (fun j => 2 ≤ j.val && j.val ≤ 21)

/-! Closed forms. Every `Pieces Nat` below takes a closed form where par-b's (or the stock) count lemma applies and
falls back to the measured piece itself elsewhere, so it equals `params.map c` for every argument, and a `decide` on a
window sum only ever evaluates the closed forms (the window's arguments are all inside the ranges). -/

def inBlocks (j : Fin 23) : Bool := 1 ≤ j.val && j.val ≤ 21
def portalTick (t : Nat) : Bool := 90 ≤ t && t ≤ 405 && t%15==0
def dueTick (t : Nat) : Bool := t != 5 && History5.packDue t

theorem portal_ok : ∀ t < 406, portalTick t=true → 5 ≤ wpP t := by decide
theorem portal_ok' (t : Nat) (h : portalTick t=true) : 5 ≤ wpP t := by
  have lt : t < 406 := by simp only [portalTick,Bool.and_eq_true,decide_eq_true_eq] at h; omega
  exact portal_ok t lt h

def tickT (e : Nat) := (W.compactSkywalkTickPreWidth e-1)+(W.compactSkywalkTickPostWidth e-1)-W.repairDue e-W.fwdDue e-TickRanges.due e
def tickM (e : Nat) := (W.compactSkywalkTickPostWidth e-1)+W.repairDue e
def recvT (e : Nat) := (W.compactSkywalkTickPreWidth e-1)+(W.compactSkywalkTickPostWidth e-1)-1-(if W.trimTick e then 1 else 0)
def recvM (e : Nat) := W.compactSkywalkTickPostWidth e-1

/-- The stock exit tick and its receiver, closed forms for any tick below 511. -/
theorem tick_closed (e : Nat) (hi : e < 511) :
    toffoliCount (renameProgram (OB5.sig e) (TickRanges.tick base e))=tickT e ∧
    measurementCount (renameProgram (OB5.sig e) (TickRanges.tick base e))=tickM e ∧
    toffoliCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))=recvT e ∧
    measurementCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))=recvM e := by
  have a := TickRanges.tick_counts base e (by omega) base_pool_nodup
  have b := W.repairedTick_counts base e (by omega) base_pool_nodup
  have c := W.compactSkywalkTick_counts base e (by omega) base_pool_nodup
  have r := W.ReverseCarry.compactReceiverTick_counts base e hi base_pool_nodup
  have o := W.compactSkywalkReverseTick_counts base e (by omega) base_pool_nodup
  simp only [(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,tickT,tickM,recvT,recvM]
  omega

def tcV : Pieces Nat where
  enter _ := 18
  enterInv _ := 18
  leave j := if inBlocks j then 6*wpP (start j)+3*lowsP (start j)+193 else toffoliCount (leaveMoveP j)
  leaveInv j := if inBlocks j then 6*wpP (start j)+3*lowsP (start j)+192 else toffoliCount (leaveMoveInvP j)
  load _ d := if d then 75 else 76
  restore _ d := if d then 80 else 80
  portal t := if portalTick t then 5*wpP t-4 else toffoliCount (portalP t)
  portalInv t := if portalTick t then 5*wpP t-4 else toffoliCount (portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ d := if d then 75 else 76
  exitRestore _ d := if d then 80 else 80
  routed j a n := if a+n ≤ 15 then n*(2*(smallBits j+18)) else toffoliCount (StairPacket.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(2*(smallBits j+18)) else toffoliCount (StairPacket.unrouted j a n)
  pack d s t := if dueTick t then 9 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 11 else toffoliCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickT e else toffoliCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvT e else
    toffoliCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

def mcV : Pieces Nat where
  enter _ := 6
  enterInv _ := 6
  leave j := if inBlocks j then 2*wpP (start j)+lowsP (start j)+93 else measurementCount (leaveMoveP j)
  leaveInv j := if inBlocks j then 2*wpP (start j)+lowsP (start j)+94 else measurementCount (leaveMoveInvP j)
  load _ _ := 136
  restore _ _ := 124
  portal t := if portalTick t then 3*wpP t-5 else measurementCount (portalP t)
  portalInv t := if portalTick t then 3*wpP t-5 else measurementCount (portalInvP t)
  park _ := 0
  parkInv _ := 0
  exitLoad _ _ := 136
  exitRestore _ _ := 124
  routed j a n := if a+n ≤ 15 then n*(smallBits j+18) else measurementCount (StairPacket.routed j a n)
  unrouted j a n := if a+n ≤ 15 then n*(smallBits j+18) else measurementCount (StairPacket.unrouted j a n)
  pack d s t := if dueTick t then 4 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 2 else measurementCount (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e < 511 then tickM e else measurementCount (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e < 511 then recvM e else
    measurementCount (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

private theorem due_of {t : Nat} (h : dueTick t=true) : t≠5 ∧ History5.packDue t=true := by
  simp only [dueTick,Bool.and_eq_true,bne_iff_ne,ne_eq] at h
  exact h

theorem tc_eq : params.map toffoliCount=tcV := by
  simp only [Pieces.map,params,ofParts,tcV]
  congr 1
  · funext j; exact (enter_counts j).1
  · funext j; exact (enter_counts j).2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (leaveMove_counts j (by omega) (by omega)).1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (leaveMove_counts j (by omega) (by omega)).2.1
    · rfl
  · funext j d; rw [(archive_counts j 0 d).1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext j d; rw [(archive_counts j 0 d).2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext t; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).1
    · rfl
  · funext t; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).2.1
    · rfl
  · funext e; exact (park_counts e).1
  · funext e; exact (park_counts e).2.1
  · funext e d; rw [(archive_counts first e d).2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.1
    · exact PartialCosts.part25.1
  · funext e d; rw [(archive_counts first e d).2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.1
    · exact PartialCosts.part57.1
  · funext j a n; split
    · rename_i h; exact (routed_counts j a n h).1
    · rfl
  · funext j a n; split
    · rename_i h; exact (routed_counts j a n h).2.2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.1
    · rfl

theorem mc_eq : params.map measurementCount=mcV := by
  simp only [Pieces.map,params,ofParts,mcV]
  congr 1
  · funext j; exact (enter_counts j).2.2.1
  · funext j; exact (enter_counts j).2.2.2.1
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (leaveMove_counts j (by omega) (by omega)).2.2.1
    · rfl
  · funext j; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h; exact (leaveMove_counts j (by omega) (by omega)).2.2.2.1
    · rfl
  · funext j d; rw [(archive_counts j 0 d).2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext j d; rw [(archive_counts j 0 d).2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext t; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).2.2.1
    · rfl
  · funext t; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).2.2.2.1
    · rfl
  · funext e; exact (park_counts e).2.2.1
  · funext e; exact (park_counts e).2.2.2.1
  · funext e d; rw [(archive_counts first e d).2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part9.2
    · exact PartialCosts.part25.2
  · funext e d; rw [(archive_counts first e d).2.2.2.2.2.2.2.2.2.2.1]; cases d
    · exact PartialCosts.part43.2
    · exact PartialCosts.part57.2
  · funext j a n; split
    · rename_i h; exact (routed_counts j a n h).2.1
    · rfl
  · funext j a n; split
    · rename_i h; exact (routed_counts j a n h).2.2.2
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.1
    · rfl
  · funext d s t; split
    · rename_i h; exact (pack_counts d s t (due_of h).1 (due_of h).2).2.2.2
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.1
    · rfl
  · funext e; split
    · rename_i h; exact (tick_closed e h).2.2.2
    · rfl

/-- Toffoli and measurement counts of any window, as Nat folds over closed forms. -/
theorem counts (d : Bool) (j : Fin 23) (js : List (Fin 23)) :
    toffoliCount (forwardW params d j js)=(forwardL tcV d j js).sum ∧
    toffoliCount (reverseW params d j js)=(reverseL tcV d j js).sum ∧
    measurementCount (forwardW params d j js)=(forwardL mcV d j js).sum ∧
    measurementCount (reverseW params d j js)=(reverseL mcV d j js).sum := by
  have f := measure_forward toffoliCount toffoliCount_append params d j js
  have r := measure_reverse toffoliCount toffoliCount_append params d j js
  have g := measure_forward measurementCount measurementCount_append params d j js
  have q := measure_reverse measurementCount measurementCount_append params d j js
  change toffoliCount _=(forwardL (params.map toffoliCount) d j js).sum at f
  change toffoliCount _=(reverseL (params.map toffoliCount) d j js).sum at r
  change measurementCount _=(forwardL (params.map measurementCount) d j js).sum at g
  change measurementCount _=(reverseL (params.map measurementCount) d j js).sum at q
  rw [tc_eq] at f r
  rw [mc_eq] at g q
  exact ⟨f,r,g,q⟩

/-- The window 90..360 (exit 375): window counts by one Nat decide over the closed forms. -/
theorem ship_counts :
    toffoliCount (forwardW params true first rest)=113844 ∧ toffoliCount (forwardW params false first rest)=113865 ∧
    toffoliCount (reverseW params true first rest)=113972 ∧ toffoliCount (reverseW params false first rest)=113972 ∧
    measurementCount (forwardW params true first rest)=57219 ∧ measurementCount (forwardW params false first rest)=57219 ∧
    measurementCount (reverseW params true first rest)=56943 ∧ measurementCount (reverseW params false first rest)=56943 := by
  rw [(counts true first rest).1,(counts false first rest).1,(counts true first rest).2.1,(counts false first rest).2.1,
    (counts true first rest).2.2.1,(counts false first rest).2.2.1,(counts true first rest).2.2.2,(counts false first rest).2.2.2]
  decide +kernel

/-- The window sizes (blocks 1..19, exit 375), by kernel evaluation of the fold's piece sums
(`counts` reduces them to `forwardL tcV d first rest` / `forwardL mcV d first rest`). -/
theorem ship_toffoliF_true : toffoliCount (forwardW params true first rest)=113844 := by
  rw [(counts true first rest).1]; decide +kernel
theorem ship_toffoliF_false : toffoliCount (forwardW params false first rest)=113865 := by
  rw [(counts false first rest).1]; decide +kernel
theorem ship_toffoliR_true : toffoliCount (reverseW params true first rest)=113972 := by
  rw [(counts true first rest).2.1]; decide +kernel
theorem ship_toffoliR_false : toffoliCount (reverseW params false first rest)=113972 := by
  rw [(counts false first rest).2.1]; decide +kernel
theorem ship_measureF : measurementCount (forwardW params true first rest)=57219 ∧
    measurementCount (forwardW params false first rest)=57219 := by
  rw [(counts true first rest).2.2.1,(counts false first rest).2.2.1]; decide +kernel
theorem ship_measureR : measurementCount (reverseW params true first rest)=56943 ∧
    measurementCount (reverseW params false first rest)=56943 := by
  rw [(counts true first rest).2.2.2,(counts false first rest).2.2.2]; decide +kernel

/-- `slotsV`: upper bounds of the piece slot counts. Exact closed forms where par-b's count lemmas apply (enter,
leave, portal, park, pack), the record's `WindowSlots` bounds for the archives (`part9/25/43/57`) and for the exit
tick/receiver at 270 (`part20/32`), `5000*n` for the routes (`WindowSlots.route`); the measured piece elsewhere, so
`slots_le` holds for every argument and a window `decide` only evaluates closed forms. -/
def slotsV : Pieces Nat where
  enter _ := 92
  enterInv _ := 92
  leave j := if inBlocks j then 23*wpP (start j)+10*lowsP (start j)+859+3*wpP (start j+15) else gateSlots (leaveMoveP j)
  leaveInv j := if inBlocks j then 23*wpP (start j)+10*lowsP (start j)+860+3*wpP (start j+15) else
    gateSlots (leaveMoveInvP j)
  load _ d := if d then 15978 else 15988
  restore _ d := if d then 12242 else 12262
  portal t := if portalTick t then 21*wpP t-7 else gateSlots (portalP t)
  portalInv t := if portalTick t then 21*wpP t-7 else gateSlots (portalInvP t)
  park _ := 9
  parkInv _ := 9
  exitLoad _ d := if d then 15978 else 15988
  exitRestore _ d := if d then 12242 else 12262
  routed _ _ n := 5000*n
  unrouted _ _ n := 5000*n
  pack d s t := if dueTick t then 144+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t))
  unpack d s t := if dueTick t then 142+(if d then 24 else 12) else
    gateSlots (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t))
  tick e := if e = 270 then 6004 else gateSlots (renameProgram (OB5.sig e) (TickRanges.tick base e))
  receiver e := if e = 270 then 6001 else
    gateSlots (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e))

theorem slots_le : (params.map gateSlots).Le slotsV := by
  simp only [Pieces.map,params,ofParts,slotsV]
  constructor
  · intro j; exact (enter_counts j).2.2.2.2.1.le
  · intro j; exact (enter_counts j).2.2.2.2.2.le
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (leaveMove_counts j (by omega) (by omega)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro j; dsimp only; split
    · rename_i h; simp only [inBlocks,Bool.and_eq_true,decide_eq_true_eq] at h
      exact (leaveMove_counts j (by omega) (by omega)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro j d; dsimp only; rw [(archive_counts j 0 d).2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro j d; dsimp only; rw [(archive_counts j 0 d).2.2.2.2.2.1]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro t; dsimp only; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).2.2.2.2.1.le
    · exact Nat.le_refl _
  · intro t; dsimp only; split
    · rename_i h; exact (portal_counts t (portal_ok' t h)).2.2.2.2.2.le
    · exact Nat.le_refl _
  · intro e; exact (park_counts e).2.2.2.2.1.le
  · intro e; exact (park_counts e).2.2.2.2.2.le
  · intro e d; dsimp only; rw [(archive_counts first e d).2.2.2.2.2.2.2.2.1]; cases d
    · exact WindowSlots.part9
    · exact WindowSlots.part25
  · intro e d; dsimp only; rw [(archive_counts first e d).2.2.2.2.2.2.2.2.2.2.2]; cases d
    · exact WindowSlots.part43
    · exact WindowSlots.part57
  · intro j a n; exact (WindowSlots.route j a n).1
  · intro j a n; exact (WindowSlots.route j a n).2
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of h).1 (due_of h).2).1.le
    · exact Nat.le_refl _
  · intro d s t; dsimp only; split
    · rename_i h; exact (pack_slots d s t (due_of h).1 (due_of h).2).2.le
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part20
    · exact Nat.le_refl _
  · intro e; dsimp only; split
    · rename_i h; subst h; rw [rename_gateSlots]; exact WindowSlots.part32
    · exact Nat.le_refl _

/-- The window 90..360 (exit 375): the slot sums of `slotsV`, one Nat evaluation (no program is evaluated). -/
theorem slot_sums : (forwardL slotsV true first rest).sum ≤ 1979823 ∧ (forwardL slotsV false first rest).sum ≤ 1979769 ∧
    (reverseL slotsV true first rest).sum ≤ 1901547 ∧ (reverseL slotsV false first rest).sum ≤ 1901703 := by
  decide +kernel


end ECDSAAdd.Entrant.StairPacket.WindowParams

end
-- END par-d WindowParams

-- BEGIN build-w4b WindowCovered
-- Record (loan720b): after par-d's WindowFold (+On), par-b's Partial + footprints (ParB_foot2/archfoot, + build-w4b's
-- BFootW: sharp archive footprints for t ≤ 369) and par-c1's
-- leaveOps_box (with the history band capped at 1300). `domainW` is the K2 domain; in-tree it replaces the body of
-- `PartialSites.domain` (Main) and `CoveredW` is then `PartialSites.Covered`.
section

namespace ECDSAAdd.Entrant.StairPacket.WindowFold
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- build-w4b: `Pieces.On` restricted to the pieces the fold uses: the entry forms only at the first block, the
`s-10` packs only after it, the window archives only of non-last blocks, the exit pieces only at the exit tick.
(par-d's `On` also asks for the unused forms, which can fall outside the domain: `pack (s1-10)`, the window archive at
the exit tick.) -/
structure Pieces.OnE {α : Type} (Q : α → Prop) (P : Pieces α) (d : Bool) (lo hi : Nat) : Prop where
  block : ∀ j : Fin 23, lo ≤ j.val → j.val ≤ hi →
    Q (P.enter j) ∧ Q (P.enterInv j) ∧ Q (P.leave j) ∧ Q (P.leaveInv j) ∧
    Q (P.routed j 0 1) ∧ Q (P.routed j 1 14) ∧ Q (P.unrouted j 0 1) ∧ Q (P.unrouted j 1 14)
  first : ∀ j : Fin 23, j.val = lo →
    Q (P.pack d (start j) (start j)) ∧ Q (P.unpack d (start j) (start j)) ∧ Q (P.portal (start j)) ∧
    Q (P.portalInv (start j))
  later : ∀ j : Fin 23, lo < j.val → j.val ≤ hi →
    Q (P.pack d (start j) (start j-10)) ∧ Q (P.unpack d (start j) (start j-10))
  saved : ∀ j : Fin 23, lo ≤ j.val → j.val < hi → Q (P.load j d) ∧ Q (P.restore j d)
  exit : ∀ j : Fin 23, j.val = hi+1 →
    Q (P.park (start j)) ∧ Q (P.parkInv (start j)) ∧ Q (P.portal (start j)) ∧ Q (P.portalInv (start j)) ∧
    Q (P.tick (start j)) ∧ Q (P.receiver (start j)) ∧
    Q (P.pack d (start j) (start j-10)) ∧ Q (P.unpack d (start j) (start j-10)) ∧
    Q (P.exitLoad (start j) d) ∧ Q (P.exitRestore (start j) d)

section onE
variable {α : Type} {Q : α → Prop} {P : Pieces α} {d : Bool} {lo hi : Nat}

theorem chainF_onE (h : P.OnE Q d lo hi) : ∀ (i : Fin 23) (js : List (Fin 23)), Consec i js → lo ≤ i.val →
    (lastBlock i js).val ≤ hi → ∀ x ∈ chainF P d i js, Q x
  | _, [], _, _, _ => by simp [chainF]
  | i, j :: js, ⟨next,rest⟩, lo_i, top => by
    have r := (consec_range j js rest).1
    have jb : j.val ≤ hi := by simp only [lastBlock] at top; omega
    have bj := h.block j (by omega) jb
    have lj := h.later j (by omega) jb
    have si := h.saved i lo_i (by omega)
    intro x mem
    simp only [chainF,List.mem_append] at mem
    rcases mem with mem | mem
    · simp only [nextF,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact bj.1
      · exact bj.2.2.2.2.1
      · exact lj.1
      · exact si.1
      · exact bj.2.2.2.2.2.1
      · exact bj.2.2.1
    · exact chainF_onE h j js rest (by omega) (by simpa only [lastBlock] using top) x mem

theorem chainR_onE (h : P.OnE Q d lo hi) : ∀ (i : Fin 23) (js : List (Fin 23)), Consec i js → lo ≤ i.val →
    (lastBlock i js).val ≤ hi → ∀ x ∈ chainR P d i js, Q x
  | _, [], _, _, _ => by simp [chainR]
  | i, j :: js, ⟨next,rest⟩, lo_i, top => by
    have r := (consec_range j js rest).1
    have jb : j.val ≤ hi := by simp only [lastBlock] at top; omega
    have bj := h.block j (by omega) jb
    have lj := h.later j (by omega) jb
    have si := h.saved i lo_i (by omega)
    intro x mem
    simp only [chainR,List.mem_append] at mem
    rcases mem with mem | mem
    · exact chainR_onE h j js rest (by omega) (by simpa only [lastBlock] using top) x mem
    · simp only [nextR,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
      · exact bj.2.2.2.1
      · exact bj.2.2.2.2.2.2.2
      · exact si.2
      · exact lj.2
      · exact bj.2.2.2.2.2.2.1
      · exact bj.2.1

theorem exitTick_eq (j : Fin 23) (js : List (Fin 23)) (top : (lastBlock j js).val = hi) (room : hi+1 < 23) :
    exitTick j js = start ⟨hi+1,room⟩ := by
  simp only [exitTick,lastStart_eq,StairPacket.start,Fin.val_mk]; omega

theorem forwardL_onE (h : P.OnE Q d lo hi) (j : Fin 23) (js : List (Fin 23)) (c : Consec j js)
    (lo_j : j.val = lo) (top : (lastBlock j js).val = hi) (room : hi+1 < 23) :
    ∀ x ∈ forwardL P d j js, Q x := by
  have r := (consec_range j js c).1
  have bj := h.block j (by omega) (by omega)
  have fj := h.first j lo_j
  have ex := h.exit ⟨hi+1,room⟩ rfl
  rw [←exitTick_eq j js top room] at ex
  intro x mem
  simp only [forwardL,List.mem_cons,List.mem_append] at mem
  rcases mem with rfl | mem | mem | mem
  · exact fj.2.2.1
  · simp only [firstF,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact bj.1
    · exact bj.2.2.2.2.1
    · exact fj.1
    · exact bj.2.2.2.2.2.1
    · exact bj.2.2.1
  · exact chainF_onE h j js c (by omega) (by omega) x mem
  · simp only [exitF,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact ex.1
    · exact ex.2.2.2.1
    · exact ex.2.2.2.2.1
    · exact ex.2.2.2.2.2.2.1
    · exact ex.2.2.2.2.2.2.2.2.1

theorem reverseL_onE (h : P.OnE Q d lo hi) (j : Fin 23) (js : List (Fin 23)) (c : Consec j js)
    (lo_j : j.val = lo) (top : (lastBlock j js).val = hi) (room : hi+1 < 23) :
    ∀ x ∈ reverseL P d j js, Q x := by
  have r := (consec_range j js c).1
  have bj := h.block j (by omega) (by omega)
  have fj := h.first j lo_j
  have ex := h.exit ⟨hi+1,room⟩ rfl
  rw [←exitTick_eq j js top room] at ex
  intro x mem
  simp only [reverseL,List.mem_append] at mem
  rcases mem with mem | mem | mem | mem
  · simp only [exitR,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact ex.2.2.2.2.2.2.2.2.2
    · exact ex.2.2.2.2.2.2.2.1
    · exact ex.2.2.2.2.2.1
    · exact ex.2.2.1
    · exact ex.2.1
  · exact chainR_onE h j js c (by omega) (by omega) x mem
  · simp only [firstR,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl
    · exact bj.2.2.2.1
    · exact bj.2.2.2.2.2.2.2
    · exact fj.2.1
    · exact bj.2.2.2.2.2.2.1
    · exact bj.2.1
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst mem
    exact fj.2.2.2

end onE
end ECDSAAdd.Entrant.StairPacket.WindowFold

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCovered
open Arithmetic MappedCompressed Partial WindowFold GateMirror
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] enterP enterInvP leaveP leaveInvP leaveMoveP leaveMoveInvP archiveLoadP archiveRestoreP portalP portalInvP parkP parkInvP
  exitLoadP exitRestoreP

/-- K2's domain (kernel-checked phase-valid there): `[131,529] [786,1045] [1049,1300] [1556,1812]`. -/
def domainW (q : Nat) : Bool :=
  (101 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1045) || (1049 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1812)
def CoveredW (P : Program) : Prop := ∀ q ∈ wires P, domainW q = true

theorem dom_iff (q : Nat) : domainW q = true ↔
    (101 ≤ q ∧ q ≤ 529) ∨ (786 ≤ q ∧ q ≤ 1045) ∨ (1049 ≤ q ∧ q ≤ 1300) ∨ (1556 ≤ q ∧ q ≤ 1812) := by
  unfold domainW; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc]
theorem nilW : CoveredW [] := by intro q h; simp [wires] at h
theorem appW {a b : Program} (ha : CoveredW a) (hb : CoveredW b) : CoveredW (a++b) := by
  intro q h; rw [wires_append, Finset.mem_union] at h; exact h.elim (ha q) (hb q)

theorem rail_le (s : Nat) : railP s ≤ 258 := by unfold railP; split <;> (try split) <;> omega
theorem top_A (s : Nat) (h : s ≤ 512) : s+15+railP s ≤ 528 := by unfold railP; split <;> (try split) <;> omega
theorem start_lo (j : Fin 23) (h : 1 ≤ j.val) : 90 ≤ start j := by simp only [start]; omega
theorem start_hi (j : Fin 23) (h : j.val ≤ 21) : start j ≤ 390 := by simp only [start]; omega

theorem footP_dom {s q : Nat} (lo : 90 ≤ s) (hi : s ≤ 405) (h : footP s q) : domainW q = true := by
  have a := top_A s (by omega); have b := rail_le s
  rw [dom_iff]; unfold footP at h; omega
theorem leaveBox_dom {s q : Nat} (lo : 90 ≤ s) (hi : s ≤ 390) (h : leaveBox s q) : domainW q = true := by
  rw [dom_iff]; unfold leaveBox at h; omega
theorem parkFoot_dom {e q : Nat} (lo : 225 ≤ e) (h : parkFootP e q) : domainW q = true := by
  have b : railP e ≤ 257 := by unfold railP; split <;> (try split) <;> omega
  rw [dom_iff]; unfold parkFootP at h; omega
/-- Window-form archives (flags at `e0(t)+6..8`) for ticks up to 390, on the sharp footprint `archFootW`. -/
theorem archFoot_dom {t q : Nat} (lo : 105 ≤ t) (hi : t ≤ 405) (h : archFootW t (e0P t + 6) q) : domainW q = true := by
  rw [dom_iff]; unfold archFootW e0P sbP at h; omega
/-- Stock-form exit archives (flags at `bTop(e)+1..3`) for exit ticks 225..405. -/
theorem exitFoot_dom {e q : Nat} (lo : 225 ≤ e) (hi : e ≤ 405) (h : archFootW e (bTopP e + 1) q) : domainW q = true := by
  have b : railP e ≤ 257 := by unfold railP; split <;> (try split) <;> omega
  rw [dom_iff]; unfold archFootW bTopP at h; omega

theorem enter_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : CoveredW (enterP j) ∧ CoveredW (enterInvP j) := by
  have w := enter_wires j (by omega) (by omega)
  exact ⟨fun q hq => footP_dom (start_lo j h0) (Nat.le_trans (start_hi j h1) (by decide)) (w.1 q hq),
    fun q hq => footP_dom (start_lo j h0) (Nat.le_trans (start_hi j h1) (by decide)) (w.2 q hq)⟩
attribute [local irreducible] leaveOps GateMirror.forward GateMirror.inverse in
theorem leave_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : CoveredW (leaveP j) ∧ CoveredW (leaveInvP j) := by
  obtain ⟨w1, w2⟩ := allW_programs (leaveOps_box j (by omega) (by omega))
  constructor
  · intro q hq
    rw [leaveP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w1 q hq)
  · intro q hq
    rw [leaveInvP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w2 q hq)
attribute [local irreducible] leaveOps leaveMoveOps GateMirror.forward GateMirror.inverse in
theorem leaveMove_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    CoveredW (leaveMoveP j) ∧ CoveredW (leaveMoveInvP j) := by
  obtain ⟨w1, w2⟩ := allW_programs (allW_leaveMove (start j) (leaveOps_box j (by omega) (by omega)))
  constructor
  · intro q hq
    rw [leaveMoveP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w1 q hq)
  · intro q hq
    rw [leaveMoveInvP] at hq
    exact leaveBox_dom (start_lo j h0) (start_hi j h1) (w2 q hq)
theorem portal_cov (t : Nat) (lo : 90 ≤ t) (hi : t ≤ 405) : CoveredW (portalP t) ∧ CoveredW (portalInvP t) := by
  have w := portal_wires t (by omega) (by omega)
  exact ⟨fun q hq => footP_dom lo hi (w.1 q hq), fun q hq => footP_dom lo hi (w.2 q hq)⟩
theorem park_cov (e : Nat) (lo : 225 ≤ e) (hi : e ≤ 405) : CoveredW (parkP e) ∧ CoveredW (parkInvP e) := by
  have w := park_wires e (by omega) hi
  exact ⟨fun q hq => parkFoot_dom lo (w.1 q hq), fun q hq => parkFoot_dom lo (w.2 q hq)⟩
theorem archive_cov (j : Fin 23) (d : Bool) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    CoveredW (archiveLoadP j d) ∧ CoveredW (archiveRestoreP j d) := by
  have lo : 105 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 405 := by simp only [start]; omega
  exact ⟨fun q hq => archFoot_dom lo hi (archiveLoadP_wiresW j d (by omega) q hq),
    fun q hq => archFoot_dom lo hi (archiveRestoreP_wiresW j d (by omega) q hq)⟩
theorem exitArch_cov (e : Nat) (d : Bool) (lo : 225 ≤ e) (hi : e ≤ 405) :
    CoveredW (exitLoadP e d) ∧ CoveredW (exitRestoreP e d) :=
  ⟨fun q hq => exitFoot_dom lo hi (exitLoadP_wiresW e d (by omega) q hq),
    fun q hq => exitFoot_dom lo hi (exitRestoreP_wiresW e d (by omega) q hq)⟩

/-- Routed ports of block `j` (dadon's `PartialSites.portsPass` decides, generic). -/
theorem ports_dom {j : Fin 23} (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) {a q : Nat} (ha : a < 15)
    (hq : q∈(IntegerPacket.ports (shape j) a).wires) : domainW (net j a q) = true := by
  have hj := j.isLt
  simp only [IntegerPacket.ports,shape,smallBits,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false] at hq
  rw [dom_iff]
  unfold net OB5.sig start
  split
  all_goals
    repeat' first | cases_type And | cases_type Or
    all_goals try simp only [Wire] at *
    all_goals omega

theorem routed_cov (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ∀ (a n : Nat), a+n ≤ 15 → CoveredW (StairPacket.routed j a n) ∧ CoveredW (StairPacket.unrouted j a n) := by
  intro a n bound
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [StairPacket.routed,StairPacket.unrouted,wires] at h
  | succ n ih =>
    have h : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape j) ⟨a,h⟩)
    have sub := ih (a+1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (shape j) a).wires.toFinset) :
        CoveredW (renameProgram (net j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact ports_dom h0 h1 h (List.mem_toFinset.mp (hp hx))
    exact ⟨appW (ok _ step.1) sub.1, appW sub.2 (ok _ step.2)⟩

/-- History cells of the pack codec at due tick `t` (ticks `t-5 .. t-1`). -/
theorem pack_cells (d : Bool) (t : Nat) (ten : 10 ≤ t) (due : History5.packDue t=true) :
    (∀ q ∈ wires (Rolling1588.packAtTick d t), ∃ r, t-5 ≤ r ∧ r ≤ t-1 ∧ (q=base r ∨ q=base (1028+r))) ∧
    (∀ q ∈ wires (Rolling1588.unpackAtTick d t), ∃ r, t-5 ≤ r ∧ r ≤ t-1 ∧ (q=base r ∨ q=base (1028+r))) := by
  constructor <;> intro q h <;>
    simp only [Rolling1588.packAtTick,Rolling1588.unpackAtTick,show t≠5 by omega,due,if_false,if_true] at h <;>
    rw [renameProgram_support] at h <;> obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
  · rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
    refine ⟨t-5+a/2,by omega,by omega,?_⟩
    simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId]
    split
    · left; rfl
    · right; congr 1; omega
  · rw [(Rolling1588.code_support d).2,Finset.mem_range] at ha
    refine ⟨t-5+a/2,by omega,by omega,?_⟩
    simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId]
    split
    · left; rfl
    · right; congr 1; omega

theorem pack_cov (d : Bool) (s t : Nat) (lo : 90 ≤ t) (ts : t ≤ s) (hi : s ≤ 405) (t5 : t%5=0) :
    CoveredW (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t)) ∧
    CoveredW (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t)) := by
  have due : History5.packDue t=true := by simp only [History5.packDue,decide_eq_true_eq]; omega
  have c := pack_cells d t (by omega) due
  constructor <;> intro q hq <;> rw [renameProgram_support] at hq <;> obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  · obtain ⟨r,r1,r2,e⟩ := c.1 x hx
    rw [dom_iff]; unfold OB5.sig
    rcases e with rfl|rfl <;> simp only [base,Wire] <;> split <;> omega
  · obtain ⟨r,r1,r2,e⟩ := c.2 x hx
    rw [dom_iff]; unfold OB5.sig
    rcases e with rfl|rfl <;> simp only [base,Wire] <;> split <;> omega

/-! The window 90..360 (blocks 1..19) with dadon's exit rendered at 375. Every per-block piece is generic; the
exit-tick pieces at 375 are one decide each (as the record's `site20/21/22/29/30/31/32/53/54`). -/
theorem allSitesW {P : Program} (h : StairSiteAvoidance.allSites domainW P = true) : CoveredW P :=
  StairSiteAvoidance.allSites_sound h

/-- The stock tick and receiver at the exit, through the tick layout (the record's `site20`/`site32` form), and the
exit archives (one decide each, as the record's `site22/29/30/53`). -/
theorem exit_tick (e : Nat) (he : e < 511)
    (table : (W.compactSkywalkTickLayout base e).wires.all (fun z => domainW (OB5.sig e z)) = true) :
    CoveredW (renameProgram (OB5.sig e) (TickRanges.tick base e)) ∧
    CoveredW (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e)) := by
  constructor <;> intro q hq <;> rw [renameProgram_support] at hq <;> obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  · exact List.all_eq_true.mp table x (List.mem_toFinset.mp (W.repairedTick_support base e (by omega) base_pool_nodup
      (TickRanges.tick_support base e (by omega) base_pool_nodup hx)))
  · exact List.all_eq_true.mp table x (List.mem_toFinset.mp
      (W.ReverseCarry.compactReceiverTick_support base e (by omega) base_pool_nodup hx))

theorem exit405 (d : Bool) :
    CoveredW (renameProgram (OB5.sig 405) (TickRanges.tick base 405)) ∧
    CoveredW (renameProgram (OB5.sig 405) (W.ReverseCarry.compactReceiverTick base 405)) ∧
    CoveredW (exitLoadP 405 d) ∧ CoveredW (exitRestoreP 405 d) := by
  have t := exit_tick 405 (by decide) (by decide +kernel)
  exact ⟨t.1,t.2,(exitArch_cov 405 d (by omega) (by omega)).1,(exitArch_cov 405 d (by omega) (by omega)).2⟩

theorem params_onE (d : Bool) : WindowParams.params.OnE CoveredW d 1 21 where
  block j h0 h1 := by
    have e := enter_cov j h0 (by omega)
    have l := leaveMove_cov j h0 (by omega)
    have r0 := routed_cov j h0 (by omega) 0 1 (by omega)
    have r1 := routed_cov j h0 (by omega) 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 90 := by simp only [start]; omega
    rw [hs]
    have p := pack_cov d 90 90 (by omega) (by omega) (by omega) (by omega)
    have o := portal_cov 90 (by omega) (by omega)
    exact ⟨p.1,p.2,o.1,o.2⟩
  later j h0 h1 := by
    have lo : 105 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 390 := by simp only [start]; omega
    have m : (start j-10)%5=0 := by simp only [start]; omega
    have p := pack_cov d (start j) (start j-10) (by omega) (by omega) (by omega) m
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_cov j d h0 (by omega)
  exit j h := by
    have hs : start j = 405 := by simp only [start]; omega
    rw [hs]
    have k := park_cov 405 (by omega) (by omega)
    have o := portal_cov 405 (by omega) (by omega)
    have p := pack_cov d 405 395 (by omega) (by omega) (by omega) (by omega)
    have x := exit405 d
    exact ⟨k.1,k.2,o.1,o.2,x.1,x.2.1,p.1,p.2,x.2.2.1,x.2.2.2⟩

theorem rest_eq : WindowParams.rest = [⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩,⟨11,by decide⟩,⟨12,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩,⟨15,by decide⟩,⟨16,by decide⟩,⟨17,by decide⟩,⟨18,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩,⟨21,by decide⟩] := by decide
theorem consec : Consec WindowParams.first WindowParams.rest := by
  rw [rest_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trivial⟩
theorem last : (lastBlock WindowParams.first WindowParams.rest).val = 21 := by rw [rest_eq]; rfl

/-- The window (both directions, both kernels) lies in the K2 domain. -/
theorem window_covered (d : Bool) :
    CoveredW (forwardW WindowParams.params d WindowParams.first WindowParams.rest) ∧
    CoveredW (reverseW WindowParams.params d WindowParams.first WindowParams.rest) :=
  ⟨flatten_of nilW (fun ha hb => appW ha hb) _
      (forwardL_onE (params_onE d) _ _ consec rfl last (by decide)),
    flatten_of nilW (fun ha hb => appW ha hb) _
      (reverseL_onE (params_onE d) _ _ consec rfl last (by decide))⟩

end ECDSAAdd.Entrant.StairPacket.WindowCovered

end
-- END build-w4b WindowCovered

-- BEGIN build-w4b WindowPhysical
-- Record (loan720b): after WindowCovered (uses its `rest_eq`/`consec`/`last`), par-b's Partial (physical_of_proper,
-- enterP/parkP_physical), par-c1's Proper/segment lemmas, par-c2's ArchiveJ head (rawNodup/codeNodup), the record's
-- `PartialPhysical.route`. Replaces the record's 60 `PartialPhysical.part#` decides of the literal window.
section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysicalW
open Arithmetic MappedCompressed Partial WindowFold GateMirror StairArchiveGates
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1

theorem nilP : GatePhysical [] := by simp [GatePhysical]
theorem appP {a b : Program} (ha : GatePhysical a) (hb : GatePhysical b) : GatePhysical (a++b) :=
  (gatePhysical_append _ _).2 ⟨ha,hb⟩

/-- Every gate of the leave is proper (no control on its target): par-c1's segment lemmas, without the state
hypotheses of `leave_ready`. -/
theorem leave_proper (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : ∀ g ∈ leaveOps (start j), proper g = true := by
  obtain ⟨w1,w2⟩ := start_win j h0 h1
  rw [leaveOps_split, leaveMidOps_eq]
  exact proper_append (proper_append (head_ok j h0 h1).2
    (proper_append (proper_append (lowRest_ok w1 w2).2 (storeMapped_ok w1 w2).2) (lowClose_ok w1 w2).2)) (close_ok w1 w2).2

theorem leave_phys (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    GatePhysical (leaveP j) ∧ GatePhysical (leaveInvP j) := by
  rw [leaveP, leaveInvP]; exact physical_of_proper _ (leave_proper j h0 h1)

/-- The move leave (`leaveMoveOps`): every gate is proper. -/
theorem leaveMove_proper (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ∀ g ∈ leaveMoveOps (start j), proper g = true := by
  obtain ⟨w1, w2⟩ := start_win j h0 h1
  exact leaveMove_proper_of w1 w2 (leave_proper j h0 h1)

theorem leaveMove_phys (j : Fin 23) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    GatePhysical (leaveMoveP j) ∧ GatePhysical (leaveMoveInvP j) := by
  rw [leaveMoveP, leaveMoveInvP]; exact physical_of_proper _ (leaveMove_proper j h0 h1)

theorem portal_properW90 : (portalOps 90).all proper = true := by decide +kernel
theorem portal_proper405 : (portalOps 405).all proper = true := by decide +kernel
theorem portal_phys90 : GatePhysical (portalP 90) ∧ GatePhysical (portalInvP 90) :=
  physical_of_proper _ (List.all_eq_true.mp portal_properW90)
theorem portal_phys405 : GatePhysical (portalP 405) ∧ GatePhysical (portalInvP 405) :=
  physical_of_proper _ (List.all_eq_true.mp portal_proper405)

/-- Packs and unpacks at any due tick, in any `OB5.sig s` frame. -/
theorem pack_phys (d : Bool) (s t : Nat) (hs : s ≤ 511) (ten : 10 ≤ t) (hi : t ≤ 511)
    (due : History5.packDue t=true) :
    GatePhysical (renameProgram (OB5.sig s) (Rolling1588.packAtTick d t)) ∧
    GatePhysical (renameProgram (OB5.sig s) (Rolling1588.unpackAtTick d t)) := by
  have inj := History5.historyMap_injective base base_pool_nodup (t-5) (by omega)
  have lab : ∀ a ∈ Finset.range 10, ∀ b ∈ Finset.range 10,
      MeasuredCodec5.label (History5.historyMap base (t-5)) a = MeasuredCodec5.label (History5.historyMap base (t-5)) b →
      a = b := by
    intro a ha b hb e
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    simp only [MeasuredCodec5.label, ha', hb', dif_pos] at e
    exact Fin.mk.inj (inj e)
  have c := Rolling1588.code_physical d
  have sp := Rolling1588.code_support d
  constructor <;> apply gatePhysical_rename _ (OB5.sig_injective s hs) <;>
    simp only [Rolling1588.packAtTick, Rolling1588.unpackAtTick, show t ≠ 5 by omega, due, if_false, if_true]
  · exact gatePhysical_rename_support _ _ (fun a ha b hb e => lab a (sp.1 ▸ ha) b (sp.1 ▸ hb) e) c.1
  · exact gatePhysical_rename_support _ _ (fun a ha b hb e => lab a (sp.2 ▸ ha) b (sp.2 ▸ hb) e) c.2

/-- The stock tick and its receiver at any tick below 511, in the `OB5.sig e` frame. -/
theorem tick_phys (e : Nat) (he : e < 511) :
    GatePhysical (renameProgram (OB5.sig e) (TickRanges.tick base e)) ∧
    GatePhysical (renameProgram (OB5.sig e) (W.ReverseCarry.compactReceiverTick base e)) :=
  ⟨gatePhysical_rename _ (OB5.sig_injective e (by omega)) _ (TickRanges.tick_physical base e (by omega) base_pool_nodup),
   gatePhysical_rename _ (OB5.sig_injective e (by omega)) _
     (W.ReverseCarry.compactReceiverTick_physical base e (by omega) base_pool_nodup)⟩

/-- A codec renamed through a duplicate-free port list is physical. -/
theorem codec_phys (ports : List Wire) (n : Nat) (P : Program) (nd : ports.Nodup) (len : n ≤ ports.length)
    (sup : ∀ q ∈ wires P, q < n) (hp : GatePhysical P) : GatePhysical (renameProgram (fun q => ports.getD q 0) P) := by
  apply gatePhysical_rename_support _ _ ?_ hp
  intro a ha b hb e
  have la : (a:Nat) < n := sup a ha
  have lb : (b:Nat) < n := sup b hb
  have ha' : a < ports.length := by simp only [Wire] at *; omega
  have hb' : b < ports.length := by simp only [Wire] at *; omega
  rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at e
  exact (List.Nodup.getElem_inj_iff nd).mp e

theorem moveLoad_phys (t : Nat) (lo : 90 ≤ t) (hi : t ≤ 405) : GatePhysical (moveLoadP t) := by
  rw [moveLoadP]
  refine (physical_of_proper _ (proper_swapsG _ ?_)).1
  simp only [moveLoadPairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
  and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)

theorem moveRestore_phys (t f : Nat) (lo : 90 ≤ t) (hi : t ≤ 405) (hf : 1563 ≤ f ∨ f+3 ≤ 1560) :
    GatePhysical (moveRestoreP t f) := by
  rw [moveRestoreP]
  refine (physical_of_proper _ (proper_swapsG _ ?_)).1
  simp only [moveRestorePairs, List.forall_mem_cons, List.forall_mem_nil, and_true, ne_eq, OB5.sig]
  and_intros <;> first | (intro x hx; cases hx) | (unfold Wire; split_ifs <;> omega) | (unfold Wire; omega)

theorem load_codec_phys (ports : List Wire) (nd : ports.Nodup) (len : 155 ≤ ports.length) (d : Bool) :
    GatePhysical (renameProgram (fun q => ports.getD q 0) (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1)) := by
  cases d
  · exact codec_phys ports 155 _ nd len load1_ports ReducedWindowArchives.load1_counts.1
  · exact codec_phys ports 155 _ nd len load0_ports ReducedWindowArchives.load0_counts.1
theorem restore_codec_phys (ports : List Wire) (nd : ports.Nodup) (len : 150 ≤ ports.length) (d : Bool) :
    GatePhysical (renameProgram (fun q => ports.getD q 0) (if d then ReducedWindowArchives.restore0 else ReducedWindowArchives.restore1)) := by
  cases d
  · exact codec_phys ports 150 _ nd len restore1_ports ReducedWindowArchives.restore1_counts.1
  · exact codec_phys ports 150 _ nd len restore0_ports ReducedWindowArchives.restore0_counts.1

/-- Window-form archives of block `j` (tick `start j + 15`), every window block up to 20. -/
theorem archive_phys (j : Fin 23) (d : Bool) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    GatePhysical (archiveLoadP j d) ∧ GatePhysical (archiveRestoreP j d) := by
  have lo : 90 ≤ start j+15 := by simp only [start]; omega
  have hi : start j+15 ≤ 405 := by simp only [start]; omega
  have nl : (loadPortsWP (start j+15) (e0P (start j+15)+6)).Nodup :=
    (List.nodup_append.mp (ArchiveJ.rawNodup j h1)).1
  have nr : (restorePortsWP (start j+15)).Nodup := (List.nodup_append.mp (ArchiveJ.codeNodup j h1)).1
  have fl : 1563 ≤ e0P (start j+15)+6 ∨ e0P (start j+15)+6+3 ≤ 1560 := Or.inl (by unfold e0P sbP; omega)
  constructor
  · rw [archiveLoadP]
    exact appP (load_codec_phys _ nl (by rw [loadPortsWP_length]) d) (moveLoad_phys _ lo hi)
  · rw [archiveRestoreP]
    exact appP (restore_codec_phys _ nr (by rw [restorePortsWP_length]) d) (moveRestore_phys _ _ lo hi fl)

/-- Stock-form exit archives at 390 (the two port lists by one decide each). -/
theorem exit_phys405 (d : Bool) : GatePhysical (exitLoadP 405 d) ∧ GatePhysical (exitRestoreP 405 d) := by
  have hb : bTopP 405+1 = 894 := by decide
  have nl : (loadPortsXP 405 894).Nodup := by decide +kernel
  have nr : (restorePortsXP 405).Nodup := by decide +kernel
  constructor
  · rw [exitLoadP, hb]
    exact appP (load_codec_phys _ nl (by rw [loadPortsXP_length]) d) (moveLoad_phys _ (by omega) (by omega))
  · rw [exitRestoreP, hb]
    exact appP (restore_codec_phys _ nr (by rw [restorePortsXP_length]) d)
      (moveRestore_phys _ _ (by omega) (by omega) (Or.inr (by omega)))

attribute [local irreducible] GatePhysical enterP enterInvP leaveP leaveInvP leaveMoveP leaveMoveInvP archiveLoadP archiveRestoreP portalP
  portalInvP parkP parkInvP exitLoadP exitRestoreP StairPacket.routed StairPacket.unrouted Rolling1588.packAtTick
  Rolling1588.unpackAtTick in
theorem params_onE_phys (d : Bool) : WindowParams.params.OnE GatePhysical d 1 21 where
  block j h0 h1 := by
    have e := enterP_physical j (by omega) (by omega)
    have l := leaveMove_phys j (by omega) (by omega)
    have r0 := PartialPhysical.route j 0 1 (by omega)
    have r1 := PartialPhysical.route j 1 14 (by omega)
    exact ⟨e.1,e.2,l.1,l.2,r0.1,r1.1,r0.2,r1.2⟩
  first j h := by
    have hs : start j = 90 := by simp only [start]; omega
    rw [hs]
    have p := pack_phys d 90 90 (by omega) (by omega) (by omega) (by decide)
    exact ⟨p.1,p.2,portal_phys90.1,portal_phys90.2⟩
  later j h0 h1 := by
    have lo : 105 ≤ start j := by simp only [start]; omega
    have hi : start j ≤ 390 := by simp only [start]; omega
    have due : History5.packDue (start j-10)=true := by
      simp only [History5.packDue,decide_eq_true_eq,start]; omega
    have p := pack_phys d (start j) (start j-10) (by omega) (by omega) (by omega) due
    exact ⟨p.1,p.2⟩
  saved j h0 h1 := archive_phys j d h0 (by omega)
  exit j h := by
    have hs : start j = 405 := by simp only [start]; omega
    rw [hs]
    have k := parkP_physical 405 (by omega) (by omega)
    have p := pack_phys d 405 395 (by omega) (by omega) (by omega) (by decide)
    have t := tick_phys 405 (by omega)
    have x := exit_phys405 d
    exact ⟨k.1,k.2,portal_phys405.1,portal_phys405.2,t.1,t.2,p.1,p.2,x.1,x.2⟩

/-- The window (both directions, both kernels) is physical. -/
theorem window_physical (d : Bool) :
    GatePhysical (forwardW WindowParams.params d WindowParams.first WindowParams.rest) ∧
    GatePhysical (reverseW WindowParams.params d WindowParams.first WindowParams.rest) :=
  ⟨flatten_of nilP (fun ha hb => appP ha hb) _
      (forwardL_onE (params_onE_phys d) _ _ WindowCovered.consec rfl WindowCovered.last (by decide)),
    flatten_of nilP (fun ha hb => appP ha hb) _
      (reverseL_onE (params_onE_phys d) _ _ WindowCovered.consec rfl WindowCovered.last (by decide))⟩

end ECDSAAdd.Entrant.StairPacket.WindowPhysicalW

-- The window program, generic over the piece list (blocks 1..19, ticks 90..360, exit 375).
namespace ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.WindowFold
def forward45plus1 (d:Bool) : Program :=
  forwardW WindowParams.params d WindowParams.first WindowParams.rest
def reverse45plus1 (d:Bool) : Program :=
  reverseW WindowParams.params d WindowParams.first WindowParams.rest
end ECDSAAdd.Entrant.StairPacket.Partial

namespace ECDSAAdd.Entrant.StairPacket.WindowParams
open ECDSAAdd.Entrant.StairPacket.WindowFold ECDSAAdd.Challenge

/-- Slot bounds of the window (upper bounds only; the judge has no slot ceiling). -/
theorem ship_slotsF : gateSlots (Partial.forward45plus1 true) ≤ 1979823 ∧
    gateSlots (Partial.forward45plus1 false) ≤ 1979769 := by
  show gateSlots (forwardW params true first rest) ≤ 1979823 ∧ gateSlots (forwardW params false first rest) ≤ 1979769
  rw [measure_forward gateSlots gateSlots_append, measure_forward gateSlots gateSlots_append]
  exact ⟨(forwardL_le slots_le true first rest).trans slot_sums.1,
    (forwardL_le slots_le false first rest).trans slot_sums.2.1⟩
theorem ship_slotsR : gateSlots (Partial.reverse45plus1 true) ≤ 1901547 ∧
    gateSlots (Partial.reverse45plus1 false) ≤ 1901703 := by
  show gateSlots (reverseW params true first rest) ≤ 1901547 ∧ gateSlots (reverseW params false first rest) ≤ 1901703
  rw [measure_reverse gateSlots gateSlots_append, measure_reverse gateSlots gateSlots_append]
  exact ⟨(reverseL_le slots_le true first rest).trans slot_sums.2.2.1,
    (reverseL_le slots_le false first rest).trans slot_sums.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowParams

-- END build-w4b WindowPhysical

-- ==== end PrizeHighBankFirstHit91f0292 ====
