import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowGates
import ECDSAAdd.Submission.Entrant.ShadowEntryFacts
/-! build-chain: Shadow7 renders of the stock window families EnterJ (helpers/build-chain/shadow/render7.py). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket MappedCompressed
def zeroSites (j:Fin 23) :=
  let p:=Shadow7.shape j
  let L:=ports p 0
  (L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem zero_congr (j:Fin 23) (s t:State) (agree:∀q∈Shadow7.zeroSites j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:Shadow7.onRails j 0 z s.basis) :
    Shadow7.onRails j 0 z t.basis ∧ cell (Shadow7.shape j) 0 (mappedBasis j t.basis)=cell (Shadow7.shape j) 0 (mappedBasis j s.basis) := by
  let p:=Shadow7.shape j
  let L:=ports p 0
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 0 15:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Shadow7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic enter piece of block `j` (par-c2, job C2 of PARAMETRIC.md). Tick `s = start j`, `h = Shadow7.sbP s`.
Every per-block number of dadon's `Enter{s}` / `EnterProof.ports{s}` is a function of `j` here; the
programs are par-b's `Shadow7.enterP j = Shadow7.forward (Shadow7.enterOps (start j))`. `EnterJ7.ports 12 = EnterProof.ports255`. -/

/-- The four A-rail ports `s+h+31..s+h+34`. -/
def railA (j : Fin 23) : List Wire :=
  [start j+Shadow7.sbP (start j)+31, start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33, start j+Shadow7.sbP (start j)+34]
/-- The four B-rail ports `h+801..h+804`. -/
def railB (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+801, Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803, Shadow7.sbP (start j)+804]
/-- Orientation gate `s+15` and the three flags `n f u` (`e0+5, e0+3, e0+4`). -/
def gate (j : Fin 23) : Wire := start j+15
def flagN (j : Fin 23) : Wire := Shadow7.sbP (start j)+1579
def flagF (j : Fin 23) : Wire := Shadow7.sbP (start j)+1577
def flagU (j : Fin 23) : Wire := Shadow7.sbP (start j)+1578
/-- Clean ports: `e0..e0+2` and the carry block `1556..1563`. -/
def clear (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
/-- The 23 ports of the enter program (`EnterProof.ports{s}`). -/
def ports (j : Fin 23) : List Wire :=
  [start j+Shadow7.sbP (start j)+31, start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33, start j+Shadow7.sbP (start j)+34,
   Shadow7.sbP (start j)+801, Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803, Shadow7.sbP (start j)+804, start j+15,
   Shadow7.sbP (start j)+1579, Shadow7.sbP (start j)+1577, Shadow7.sbP (start j)+1578,
   Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
def map (j : Fin 23) (q : Wire) : Wire := (ports j).getD q 0
/-- The parked bank: three low pairs, then `Wp-3` upper pairs up to the B rail's top `785+R`. -/
def lowerPairs (j : Fin 23) : List (Wire×Wire) :=
  [(start j+Shadow7.sbP (start j)+32, Shadow7.sbP (start j)+802), (start j+Shadow7.sbP (start j)+33, Shadow7.sbP (start j)+803),
   (start j+Shadow7.sbP (start j)+34, Shadow7.sbP (start j)+804)]
def upperPairs (j : Fin 23) : List (Wire×Wire) :=
  (List.range (Shadow7.wpP (start j)-3)).map (fun i => (start j+Shadow7.sbP (start j)+35+i, Shadow7.sbP (start j)+805+i))
/-- Saved high word (`Enter{s}.saved`) and the three pending flags written by the previous leave. -/
def saved (j : Fin 23) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576]++(upperPairs j).map Prod.snd
def pending (j : Fin 23) : List Wire := [Shadow7.sbP (start j)+1580, Shadow7.sbP (start j)+1581, Shadow7.sbP (start j)+1582]
/-- Low rails `s+16..` and `786..` (`h+15` wires each) and the guard predicate. -/
def lowA (j : Fin 23) : List Wire := List.range' (start j+16) (Shadow7.sbP (start j)+15)
def lowB (j : Fin 23) : List Wire := List.range' 786 (Shadow7.sbP (start j)+15)
def safe (j : Fin 23) (q : Wire) : Prop :=
  (q<start j+16 ∨ start j+Shadow7.sbP (start j)+31≤q) ∧ (q<786 ∨ Shadow7.sbP (start j)+801≤q)
instance (j : Fin 23) (q : Wire) : Decidable (safe j q) := by unfold safe; infer_instance
/-- Stock layout of tick `s` and the frame of tick `s-1`. -/
def lay (j : Fin 23) : SkywalkIntegerLayout := W.compactSkywalkTickLayout base (start j)
def pull (j : Fin 23) : Wire → Wire := OB5.sig (start j-1)
def carryPorts (j : Fin 23) : List Wire := ((IntegerPacket.ports (Shadow7.shape j) 0).carry).map (windowNet j)
def rest (j : Fin 23) : List Wire := (carryPorts j).drop 8
def guarded (j : Fin 23) : List Wire := ports j++[flagN j, flagF j, flagU j]++RailPair.sites (upperPairs j)

theorem ports_split (j : Fin 23) :
    ports j=railA j++railB j++[gate j, flagN j, flagF j, flagU j]++clear j := rfl
theorem ports_length (j : Fin 23) : (ports j).length=EnterProof.width := rfl

/-- `inc{s}` for every block. -/
theorem inc_all : ∀ j : Fin 23, ∀ a b : Fin EnterProof.width, map j a=map j b → a=b := by decide +kernel
theorem inc (j : Fin 23) : ∀ a b : Fin EnterProof.width, map j a=map j b → a=b := inc_all j
/-- `emitted{s}` / `emitted{s}Inv`: definitional for every block. -/
theorem emitted (j : Fin 23) : Shadow7.enterP j=renameProgram (map j) EnterProof.forward := rfl
theorem emittedInv (j : Fin 23) : Shadow7.enterInvP j=renameProgram (map j) EnterProof.backward := rfl

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Geometry of the enter piece of block `j`, once for all `j : Fin 23`: interval lemmas (omega) where a
fact ranges over a long list, one `decide +kernel` over the 23 blocks where it only reads short lists. -/

/-- Arithmetic frame of block `j`: `s = 75+15j`, `2h+s ∈ {512,513}`, `3 < Wp`, `Wp+h ≤ 242`. -/
theorem frame (j : Fin 23) : start j=75+15*j.val ∧ j.val<23 ∧ 2*Shadow7.sbP (start j)+start j≤499 ∧
    498≤2*Shadow7.sbP (start j)+start j ∧ 3<Shadow7.wpP (start j) ∧ Shadow7.wpP (start j)+Shadow7.sbP (start j)≤242 := by
  have hj:=j.isLt
  refine ⟨rfl,hj,?_,?_,?_,?_⟩ <;> simp only [start,Shadow7.wpP,railP,Shadow7.sbP] <;> (try split_ifs) <;> omega

theorem upperSites (j : Fin 23) {q : Wire} (h : q∈RailPair.sites (upperPairs j)) :
    (start j+Shadow7.sbP (start j)+35≤q ∧ q+3<start j+Shadow7.sbP (start j)+35+Shadow7.wpP (start j)) ∨
    (Shadow7.sbP (start j)+805≤q ∧ q+3<Shadow7.sbP (start j)+805+Shadow7.wpP (start j)) := by
  simp only [RailPair.sites,upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at h
  obtain ⟨p,⟨i,hi,rfl⟩,hp⟩:=h
  simp only [Wire] at *
  rcases hp with rfl|rfl <;> omega

theorem portsRegion (j : Fin 23) {q : Wire} (h : q∈ports j) :
    (start j+Shadow7.sbP (start j)+31≤q ∧ q≤start j+Shadow7.sbP (start j)+34) ∨ (Shadow7.sbP (start j)+801≤q ∧ q≤Shadow7.sbP (start j)+804) ∨
    q=start j+15 ∨ (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (1556≤q ∧ q≤1563) := by
  simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [Wire] at *
  omega

theorem g0_all : ∀ j : Fin 23, pull j (gate j)=(lay j).previous := by decide +kernel
theorem xa_all : ∀ j : Fin 23, (railA j).map (pull j)=((lay j).a.drop (Shadow7.sbP (start j)+15)).take 4 := by decide +kernel
theorem xb_all : ∀ j : Fin 23, (railB j).map (pull j)=((lay j).b.drop (Shadow7.sbP (start j)+15)).take 4 := by decide +kernel
theorem na_all : ∀ j : Fin 23, Shadow7.sbP (start j)+15+4≤(lay j).a.length := by decide +kernel
theorem nb_all : ∀ j : Fin 23, Shadow7.sbP (start j)+15+4≤(lay j).b.length := by decide +kernel
theorem temps_all : ∀ j : Fin 23, ∀q∈clear j, pull j q∈(lay j).carry := by decide +kernel

theorem protected0 (j : Fin 23) : ∀q∈gate j::(railA j++railB j++clear j),
    q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉RailPair.sites (upperPairs j) := by
  have f:=frame j
  intro q hq
  simp only [gate,railA,railB,clear,flagN,flagF,flagU,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  refine ⟨by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,fun hs=>?_⟩
  have u:=upperSites j hs
  simp only [Wire] at *
  omega

/-- `Enter{s}.layout`. -/
def layout (j : Fin 23) : Aperture (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (ports j)
    (lay j) (pull j) (Shadow7.sbP (start j)+15) where
  a:=railA j
  b:=railB j
  spec:=⟨rfl,rfl,clear j,rfl⟩
  g0:=g0_all j
  xa:=xa_all j
  xb:=xb_all j
  na:=na_all j
  nb:=nb_all j
  protected0:=protected0 j
  temps:=temps_all j

/-- `Enter{s}.from_full` for every block. -/
theorem from_full (j : Fin 23) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run (Shadow7.enterP j) m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof.forward,next.basis (map j q)=(shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) ∧
      ∀q∉wires (Shadow7.enterP j),next.basis q=v.basis q := by
  have src:=read_packed (layout j) raw v z G S p input
  apply actual_shadow_shadow7 (map j) (Shadow7.enterP j) false (Shadow7.sbP (start j)) 15 z G S small (inc j) (emitted j) v m
  intro q h
  have lim:wires EnterProof.forward ⊆ Finset.range 23 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have hv:=bitAt (ports j) v.basis q ((show (ports j).length=23 from rfl) ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- Every wire of `Shadow7.enterP j` is one of its 23 ports (from `emitted`, no evaluation). -/
theorem programCover (j : Fin 23) : wires (Shadow7.enterP j) ⊆ (ports j).toFinset := by
  rw [emitted j,renameProgram_support,forward_all]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(ports j).length:=Finset.mem_range.mp hw
  rw [List.mem_toFinset,map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt
theorem notWire (j : Fin 23) {q : Wire} (h : q∉ports j) : q∉wires (Shadow7.enterP j) :=
  fun m=>h (List.mem_toFinset.mp (programCover j m))

theorem noLow (j : Fin 23) : ∀q∈guarded j, safe j q := by
  have f:=frame j
  intro q hq
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  unfold safe
  rcases hq with (hp|hn)|hs
  · have r:=portsRegion j hp; simp only [Wire] at *; omega
  · simp only [flagN,flagF,flagU,Wire] at *; omega
  · have u:=upperSites j hs; simp only [Wire] at *; omega
theorem lowUnsafe (j : Fin 23) : ∀w∈lowA j++lowB j, ¬safe j w := by
  intro w h
  simp only [lowA,lowB,safe,List.mem_append,List.mem_range'_1,Wire] at *
  omega
theorem lowXa_all : ∀ j : Fin 23, (lowA j).map (pull j)=(lay j).a.take (Shadow7.sbP (start j)+15) := by decide +kernel
theorem lowXb_all : ∀ j : Fin 23, (lowB j).map (pull j)=(lay j).b.take (Shadow7.sbP (start j)+15) := by decide +kernel

theorem protects (j : Fin 23) (q:Wire) (h:q∈lowA j++lowB j) :
    q∉wires (Shadow7.enterP j) ∧ q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉sites (upperPairs j) := by
  have bad:=lowUnsafe j q h
  have gone:q∉guarded j:=fun mem=>bad (noLow j q mem)
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨notWire j gone.1.1,gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩

/-- `Enter{s}.placement`. -/
def placement (j : Fin 23) : WordPlacement (b:=Shadow7.sbP (start j)) (k:=15) (layout j) (Shadow7.enterP j) where
  lowA:=lowA j
  lowB:=lowB j
  al:=List.length_range'
  bl:=List.length_range'
  xa:=lowXa_all j
  xb:=lowXb_all j
  aTop:=rfl
  bTop:=rfl
  protected0:=protects j
  portsCount:=rfl

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- The carry ports of the block's first tick are fixed by the window frame: `1556..1573+h`. -/
theorem carryPorts_eq (j : Fin 23) : carryPorts j=List.range' 1556 (Shadow7.sbP (start j)+18) := by
  have hj:=j.isLt
  have hc:(IntegerPacket.ports (Shadow7.shape j) 0).carry=List.range' 1556 (Shadow7.sbP (start j)+18) := rfl
  unfold carryPorts
  rw [hc]
  conv => rhs; rw [← List.map_id (List.range' 1556 _)]
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range'_1] at hq
  simp only [windowNet,net,OB5.sig,start,Shadow7.sbP,id,Wire] at hq ⊢
  split <;> omega
theorem rest_eq (j : Fin 23) : rest j=List.range' 1564 (Shadow7.sbP (start j)+10) := by
  rw [rest,carryPorts_eq,List.drop_range']
  congr 1
theorem parts (j : Fin 23) : carryPorts j=((ports j).drop 15)++rest j := by
  rw [rest_eq,carryPorts_eq]
  have e:Shadow7.sbP (start j)+18=8+(Shadow7.sbP (start j)+10):=by omega
  rw [e,← List.range'_append_1]
  rfl
theorem layCarry_all : ∀ j : Fin 23,
    (lay j).carry=List.range' 1556 (W.compactSkywalkTickPreWidth (start j)-1) := by decide +kernel
theorem layWidth_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤W.compactSkywalkTickPreWidth (start j) := by decide +kernel
theorem guardedBound_all : ∀ j : Fin 23, ∀q∈guarded j, q<1564 ∨ Shadow7.sbP (start j)+1574≤q := by decide +kernel
theorem clearCover (j : Fin 23) : ∀q∈guarded j, q∉rest j := by
  intro q hq mem
  rw [rest_eq,List.mem_range'_1] at mem
  have:=guardedBound_all j q hq
  simp only [Wire] at *
  omega
theorem sourceCover (j : Fin 23) : ∀q∈rest j, pull j q∈(lay j).carry := by
  intro q hq
  rw [rest_eq,List.mem_range'_1] at hq
  have w:=layWidth_all j
  have hj:=j.isLt
  rw [layCarry_all j,List.mem_range'_1]
  have fix:pull j q=q:=by
    have hq':=hq
    simp only [pull,OB5.sig,start,Shadow7.sbP,Wire] at hq' ⊢
    split <;> omega
  rw [fix]
  simp only [Wire] at *
  omega

theorem frameA_all : ∀ j : Fin 23,
    (IntegerPacket.ports (Shadow7.shape j) 0).a.map (windowNet j)=lowA j++railA j := by decide +kernel
theorem frameB_all : ∀ j : Fin 23,
    (IntegerPacket.ports (Shadow7.shape j) 0).b.map (windowNet j)=lowB j++railB j := by decide +kernel
theorem framePrev_all : ∀ j : Fin 23,
    windowNet j (IntegerPacket.ports (Shadow7.shape j) 0).previous=(ports j).getD 8 0 := by decide +kernel
theorem frameExt_all : ∀ j : Fin 23, ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).ext
    q∉ports j ∧ q∈(upperPairs j).map Prod.fst := by decide +kernel

/-- History ports of the block's ticks in the window frame: raw `s+r+1044`, or its mirror `2069-s-r`. -/
theorem histPort (j : Fin 23) (r : Fin 15) :
    let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
    (q=start j+r.val+1044 ∧ start j+r.val+1044<1301) ∨ (q=2069-start j-r.val ∧ 1301≤start j+r.val+1044) := by
  have hr:=r.isLt
  have f:=frame j
  simp only [windowNet,net,OB5.sig,IntegerPacket.ports,Shadow7.shape]
  simp only [Wire] at *
  split <;> omega
theorem frameHist (j : Fin 23) : ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
    q∉ports j ∧ q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉sites (upperPairs j) := by
  intro r
  have f:=frame j
  have hr:=r.isLt
  have hp:=histPort j r
  dsimp only at hp ⊢
  refine ⟨fun m=>?_,?_,?_,?_,fun m=>?_⟩
  · have x:=portsRegion j m; simp only [Wire] at *; omega
  · simp only [flagN,Wire] at *; omega
  · simp only [flagF,Wire] at *; omega
  · simp only [flagU,Wire] at *; omega
  · have x:=upperSites j m; simp only [Wire] at *; omega

/-- `Enter{s}.live`. -/
theorem live (j : Fin 23) : FramePorts_shadow7 (placement j) j where
  a:=frameA_all j
  bSites:=frameB_all j
  prev:=framePrev_all j
  carry:=by
    intro q hq
    let v:=windowNet j q
    have h : v∈carryPorts j:=List.mem_map.mpr ⟨q,hq,rfl⟩
    rw [parts j,List.mem_append] at h
    rcases h with h|h
    · exact Or.inl h
    · have absent : v∉guarded j:=fun inc=>clearCover j v inc h
      simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
      exact Or.inr ⟨notWire j absent.1.1,sourceCover j _ h,absent.1.2.1,absent.1.2.2.1,absent.1.2.2.2,absent.2⟩
  ext:=fun r=>⟨notWire j (frameExt_all j r).1,(frameExt_all j r).2⟩
  hist:=fun r=>let h:=frameHist j r;⟨notWire j h.1,h.2⟩

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- `Enter{s}.ready_from_cut`, with the history cells of ticks `s..s+14` given in the pulled frame
(every block; the stock-frame form below holds for `s ≤ 255`). -/
theorem ready_from_cut_at (j : Fin 23) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false) :
    let t:=run (Shadow7.enterP j) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=v.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  obtain ⟨ph,body,outer⟩:=from_full j raw v z G S m small p input
  exact ⟨ph,complete_shadow7 (live j) _ G S small raw v _ p input body outer hist⟩

/-- Stock-frame history sources (`s ≤ 255`): the stock cell `base (1028+s+r)`, the end scratch `1812`,
or a carry wire of tick `s`. -/
theorem histSources_all : ∀ j : Fin 23, j.val≤12 → ∀r:Fin 15,
    let q:=pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history)
    q=base (1028+start j+r) ∨ q=1812 ∨ q∈(lay j).carry := by decide +kernel

/-- `Enter{s}.ready_from_cut` (dadon's form, `s ≤ 255`). -/
theorem ready_from_cut (j : Fin 23) (hj:j.val≤12) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+start j+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run (Shadow7.enterP j) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=v.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  apply ready_from_cut_at j raw v z G S m small p input
  intro r
  rcases histSources_all j hj r with eq|eq|mem
  · rw [eq];exact hist r
  · rw [eq];exact endScratch
  · exact (regValue_zero _ _).mp input.2.2.2.2.2 _ mem

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed
namespace EnterJ7
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem avoid_enter (j : Fin 23) : ∀q∈pending j,q∉wires (Shadow7.enterP j) := by
  have f:=frame j
  intro q hq
  apply notWire j
  intro hp
  have r:=portsRegion j hp
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega
theorem zeroBand_all : ∀ j : Fin 23,
    (Shadow7.zeroSites j).all (fun q=>decide (q<Shadow7.sbP (start j)+1580 ∨ Shadow7.sbP (start j)+1583≤q)) := by decide +kernel
theorem avoid_live (j : Fin 23) : ∀q∈pending j,q∉Shadow7.zeroSites j := by
  intro q hq hz
  have b:=of_decide_eq_true (List.all_eq_true.mp (zeroBand_all j) q hz)
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega

/-- `Enter{s}.ready_pending` with the history sources in the pulled frame (every block). -/
theorem ready_pending_at (j : Fin 23) (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) (eraseSites (pending j) pre))
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false) :
    let t:=run (Shadow7.enterP j) m pre
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=pre.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending j,t.basis q=pre.basis q := by
  have eq:=erase_run (pending j) (Shadow7.enterP j) (avoid_enter j) m pre
  have real:=ready_from_cut_at j raw (eraseSites (pending j) pre) z G S m small cut input hist
  rw [eq] at real
  refine ⟨real.1,(Shadow7.zero_congr j _ _ ?_ _ real.2).1,fun q mem=>run_preserves_outside _ m pre _ (avoid_enter j _ mem)⟩
  intro q used
  have absent:q∉pending j:=fun h=>avoid_live j _ h used
  simp [eraseSites,absent]

/-- `Enter{s}.ready_pending` (dadon's form, `s ≤ 255`). -/
theorem ready_pending (j : Fin 23) (hj:j.val≤12) (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) (eraseSites (pending j) pre))
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+start j+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run (Shadow7.enterP j) m pre
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    t.phase=pre.phase ∧ Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending j,t.basis q=pre.basis q := by
  apply ready_pending_at j raw pre z G S m small cut input
  intro r
  rcases histSources_all j hj r with eq|eq|mem
  · rw [eq];exact hist r
  · rw [eq];exact endScratch
  · exact (regValue_zero _ _).mp input.2.2.2.2.2 _ mem
end EnterJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed EnterProof PortalValues Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem highA_all : ∀ j : Fin 23,
    ((upperPairs j).map Prod.fst).map (pull j)=(lay j).a.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highB_all : ∀ j : Fin 23,
    ((upperPairs j).map Prod.snd).map (pull j)=(lay j).b.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highLa_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤(lay j).a.length := by decide +kernel
theorem highLb_all : ∀ j : Fin 23, Shadow7.sbP (start j)+19≤(lay j).b.length := by decide +kernel
theorem savedLive (j : Fin 23) : ∀q∈(upperPairs j).map Prod.snd,q∉ports j := by
  have f:=frame j
  intro q hq hp
  simp only [upperPairs,List.map_map,List.mem_map,List.mem_range,Function.comp] at hq
  obtain ⟨i,hi,rfl⟩:=hq
  have r:=portsRegion j hp
  simp only [Wire] at *
  omega

/-- `Enter{s}.high_from_cut` for every block. -/
theorem high_from_cut (j : Fin 23) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) cut)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue (saved j) (run (Shadow7.enterP j) m cut).basis=
      if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0 :=by
  have high:=SavedHigh.stored (Shadow7.sbP (start j)+19) raw cut z G S packed input (layout j).g0
    (highA_all j) (highB_all j) (highLa_all j) (highLb_all j)
  obtain ⟨_,bits,outer⟩:=from_full j raw cut z G S m small packed input
  have bulk:=regValue_congr ((upperPairs j).map Prod.snd) (run (Shadow7.enterP j) m cut).basis cut.basis
    (fun q hit=>outer q (notWire j (savedLive j q hit)))
  apply SavedHigh.assemble (Shadow7.sbP (start j)) 15 z G S _ (Shadow7.sbP (start j)+1574) (Shadow7.sbP (start j)+1575) (Shadow7.sbP (start j)+1576) _
  · exact bits 12 (by rw [forward_all];decide)
  · exact bits 13 (by rw [forward_all];decide)
  · exact bits 14 (by rw [forward_all];decide)
  · exact bulk.trans high

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end
