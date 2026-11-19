import ECDSAAdd.Submission.Entrant.PrizeTail10d9efffc
import ECDSAAdd.Submission.Entrant.PrizeTail752d1574c

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3300000
attribute [local irreducible] run body measurementCount leave255 leave255Inv NativePack255.nextWindow NativePack255.nextUnwind

private theorem physical (d:Bool) (x p:Nat) (good:Bounds x p) (s:State) (m n:List Bool)
    (pre:Ready255 d x p s) :
    let v:=run (NativePack255.nextWindow d) m s
    let out:=run leave255 n v
    out.phase=s.phase ∧ Ready270 d x p out ∧ (∀k,run leave255Inv k out=v) ∧ (∀k,run (NativePack255.nextUnwind d) k v=s) := by
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=pre
  let v:=run (NativePack255.nextWindow d) m s
  let out:=run leave255 n v
  let raw':=endRaw 255 raw v
  let flags:=Leave255Admission.flags (unsigned 255 x p) g sg
  have curr:=readInput 255 x p raw g sg pre.input
  have native:=NativePack255.from_domain_matched d x p good raw s m pre.domain g sg pre.cut curr pg ps _ pre.facts
  obtain ⟨h,cut,facts⟩:=NativePack255.stock_endpoint d x p good raw s m n pre.domain g sg pre.cut curr pg ps _ pre.facts
  have carried:=stepInput 255 129 x p (by decide) (by decide) fixed255 good raw v g sg pre.domain pre.input h.small
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase 255 x p (by decide) good raw v pre.domain).trans prevPhase.symm)
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology 240 x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  have accepted:Saved 240 x p ArchiveBoundary255.codePorts d out:=by
    refine ⟨row,bound,chr,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hq
    exact ArchiveWindowPreserve.after255 v n q (List.mem_append.mpr (Or.inr hq))
  have same:=unique_input pre.input (fixed_input _ _ _ (by decide) good raw pre.domain)
  have older:Saved 225 x p ArchiveBoundary240.codePorts d out:=by
    obtain ⟨r,lim,yes,old⟩:=pre.saved225
    refine ⟨r,lim,yes,ArchiveWindowPreserve.keep old ?_⟩
    intro q hq
    exact (ArchiveWindowPreserve.after255 v n q (List.mem_append.mpr (Or.inl hq))).trans
      (ArchiveWindowPreserve.entering255 d s m q hq)
  exact ⟨ph,⟨raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts.1,facts.2.1,facts.2.2.1,facts.2.2.2,same,older,accepted⟩,h.roundtrip n,native.2.2.2⟩

theorem step255 (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (NativePack255.nextWindow d++leave255) (leave255Inv++NativePack255.nextUnwind d) (Ready255 d x p) (Ready270 d x p) := by
  apply pair (F:=NativePack255.nextWindow d) (F':=leave255) (R:=NativePack255.nextUnwind d) (R':=leave255Inv)
  intro s m h
  exact physical d x p good s m _ h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket Secp256k1 WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3800000
attribute [local irreducible] run body measurementCount NativePack270.lastWindow NativePack270.lastUnwind

theorem step270 (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (NativePack270.lastWindow d) (NativePack270.lastUnwind d) (Ready270 d x p) (Final d x p) := by
  rintro s m ⟨raw,g,sg,pg,ps,pre⟩
  let z:=unsigned 270 x p
  have short:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have old:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have eq:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have last:=NativePack270.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 270 x p raw g sg pre.input) (by simpa only [eq] using pre.cut) (unsigned 255 x p) pg ps _
    old.odd old.small pre.records pre.mode pre.side pre.cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have chr:Chronology 255 x p r:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  refine ⟨last.1,⟨?_,?_,⟨r,lim,chr,frame⟩⟩,last.2.2⟩
  · obtain ⟨k,limit,actual,kept⟩:=pre.saved225
    exact ⟨k,limit,actual,ArchiveWindowPreserve.keep kept (fun q mem=>ArchiveWindowPreserve.last d s m q (List.mem_append.mpr (Or.inl mem)))⟩
  · obtain ⟨k,limit,actual,kept⟩:=pre.saved240
    exact ⟨k,limit,actual,ArchiveWindowPreserve.keep kept (fun q mem=>ArchiveWindowPreserve.last d s m q (List.mem_append.mpr (Or.inr mem)))⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowChain
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowTicket Partial
attribute [local irreducible] run measurementCount Checked body leave225 leave240 leave255 leave225Inv leave240Inv leave255Inv
  NativePack225.firstWindow NativePack240.nextWindow NativePack255.nextWindow NativePack270.lastWindow
  NativePack225.firstUnwind NativePack240.nextUnwind NativePack255.nextUnwind NativePack270.lastUnwind

theorem checked (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (forward45plus1 d) (reverse45plus1 d) (Before d x p) (ArchiveStockRows.Final d x p) := by
  rw [assembly,unwind_assembly]
  simpa only [List.append_assoc] using
    composition (step225 d x p good) (composition (step240 d x p good) (composition (step255 d x p good) (step270 d x good)))

theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    let start:=pullState (OB5.sig 224) raw
    let out:=run (forward45plus1 d) m start
    out.phase=raw.phase ∧ ArchiveStockRows.Final d x p out ∧ ∀n,run (reverse45plus1 d) n out=start := by
  have law:=checked d x good
  unfold Checked at law
  exact law _ m ⟨raw,stage,rfl⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowChain

end

