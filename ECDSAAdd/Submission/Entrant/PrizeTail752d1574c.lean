import ECDSAAdd.Submission.Entrant.PrizeTail10d9efffc

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3300000
attribute [local irreducible] run body measurementCount leave240 leave240Inv NativePack240.nextWindow NativePack240.nextUnwind

private theorem physical (d:Bool) (x p:Nat) (good:Bounds x p) (s:State) (m n:List Bool)
    (pre:Ready240 d x p s) :
    let v:=run (NativePack240.nextWindow d) m s
    let out:=run leave240 n v
    out.phase=s.phase ∧ Ready255 d x p out ∧ (∀k,run leave240Inv k out=v) ∧ (∀k,run (NativePack240.nextUnwind d) k v=s) := by
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=pre
  let v:=run (NativePack240.nextWindow d) m s
  let out:=run leave240 n v
  let raw':=endRaw 240 raw v
  let flags:=Leave240Admission.flags (unsigned 240 x p) g sg
  have curr:=readInput 240 x p raw g sg pre.input
  have native:=NativePack240.from_domain_matched d x p good raw s m pre.domain g sg pre.cut curr pg ps _ pre.facts
  obtain ⟨h,cut,facts⟩:=NativePack240.stock_endpoint d x p good raw s m n pre.domain g sg pre.cut curr pg ps _ pre.facts
  have carried:=stepInput 240 136 x p (by decide) (by decide) fixed240 good raw v g sg pre.domain pre.input h.small
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase 240 x p (by decide) good raw v pre.domain).trans prevPhase.symm)
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology 225 x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  have accepted:Saved 225 x p ArchiveBoundary240.codePorts d out:=by
    refine ⟨row,bound,chr,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hq
    exact ArchiveWindowPreserve.after240 v n q hq
  have same:=unique_input pre.input (fixed_input _ _ _ (by decide) good raw pre.domain)
  exact ⟨ph,⟨raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,same,accepted⟩,h.roundtrip n,native.2.2.2⟩

theorem step240 (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (NativePack240.nextWindow d++leave240) (leave240Inv++NativePack240.nextUnwind d) (Ready240 d x p) (Ready255 d x p) := by
  apply pair (F:=NativePack240.nextWindow d) (F':=leave240) (R:=NativePack240.nextUnwind d) (R':=leave240Inv)
  intro s m h
  exact physical d x p good s m _ h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

