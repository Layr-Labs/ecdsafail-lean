import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen

def mask (bank : Finset Wire) (archive stock : State) : State :=
  ⟨stock.phase, fun q => if q ∈ bank then archive.basis q else stock.basis q⟩

def avoids (P : Program) (bank : Finset Wire) : Prop := ∀ q ∈ bank, q ∉ wires P

theorem mask_run (P : Program) (bank : Finset Wire) (m : List Bool) (a r : State)
    (safe : avoids P bank) :
    run P m (mask bank a r) = mask bank a (run P m r) := by
  have h := Arithmetic.run_local_increment P (mask bank a r) r m (fun q used => by
    have off : q ∉ bank := fun x => safe q x used
    simp [mask, off])
  apply congrArg₂ State.mk
  · have hh := h.1
    change ((run P m (mask bank a r)).phase ^^ r.phase) = ((run P m r).phase ^^ r.phase) at hh
    change (run P m (mask bank a r)).phase = (run P m r).phase
    cases r.phase <;> simp_all
  · funext q
    by_cases used : q ∈ wires P
    · have off : q ∉ bank := fun x => safe q x used
      simpa [mask, off] using h.2 q used
    · rw [run_preserves_outside P m (mask bank a r) q used]
      change (if q ∈ bank then a.basis q else r.basis q) =
        (if q ∈ bank then a.basis q else (run P m r).basis q)
      rw [run_preserves_outside P m r q used]

theorem mask_frame (j row : Nat) (cs : CodecBitSliceVerify.Cols) (bank : Finset Wire)
    (a r : State) (off : ∀ q∈inside j, q∉bank) (h : frame j row cs r) :
    frame j row cs (mask bank a r) := by
  intro q hq
  have hk := off (fieldPort j q) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  simpa [mask,hk] using h q hq

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask


end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify

def bank (j : Nat) := (Finset.range 16).image (fieldPort j)

def offBanks (persistent other : Finset Wire) (a r : State) : Prop :=
  ∀ q, q ∉ persistent → q ∉ other → a.basis q = r.basis q

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000

theorem restored (rev : Bool) :
    (List.range' 16 105).all (fun q => get (outputCols (leave rev)) q == get (StairArchiveNativeCut.canonical rev rev) q) = true := by
  cases rev <;> decide +kernel

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask


end
