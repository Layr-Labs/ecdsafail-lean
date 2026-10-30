import ECDSAAdd.Submission.Entrant.FrontierEntry1591Forward
import ECDSAAdd.Submission.Entrant.ParityHost5

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewHistory5.allEncode

def payloadControls : List Wire := ParityHost5.payloadControls
  (fun i => OB5.sig 511 (NewHistory5.payloadWire base i))

theorem clear_payload_free : ∀q∈payloadControls,q∉wires (skywalkArithmeticClear base) := by
  intro q hq used
  change q∈(List.range 816).map (fun i=>OB5.sig 511 (NewHistory5.payloadWire base i)) at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  have bound := List.mem_range.mp hi
  have rawFree : NewHistory5.payloadWire base i∉wires (skywalkArithmeticClear base) := by
    unfold NewHistory5.payloadWire
    exact Kernel5.history_clear_away base base_pool_nodup (i/8) (by omega) _
  have pulled : OB5.sig 511 (OB5.sig 511 (NewHistory5.payloadWire base i))∈
      wires (renameProgram (OB5.sig 511) (skywalkArithmeticClear base)) := by
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨_,used,rfl⟩
  rw [KernelOB5.clear_rename,OB5.sig_invol 511 (by decide)] at pulled
  exact rawFree pulled

theorem clear_host_free : base 1543∉wires (skywalkArithmeticClear base) := by
  decide +kernel

theorem placed_host_parity (s : State)
    (parity : s.basis (base 1538)=TraceParity5.xorRange 816
      (fun i=>s.basis (NewHistory5.payloadWire base i))) :
    (pullState (OB5.sig 511) s).basis (base 1543)=
      TraceParity5.parity (payloadControls.map (pullState (OB5.sig 511) s).basis) := by
  have hostMap : OB5.sig 511 (base 1543)=base 1538 := by decide +kernel
  change s.basis (OB5.sig 511 (base 1543))=_
  rw [hostMap,parity]
  simp only [payloadControls,ParityHost5.payloadControls,List.map_map,Function.comp_def,
    TraceParity5.parity_range]
  apply TraceParity5.xorRange_congr
  intro i hi
  change s.basis (NewHistory5.payloadWire base i)=
    s.basis (OB5.sig 511 (OB5.sig 511 (NewHistory5.payloadWire base i)))
  rw [OB5.sig_invol 511 (by decide)]

theorem clear_host_parity (s : State) (m : List Bool)
    (parity : s.basis (base 1543)=TraceParity5.parity (payloadControls.map s.basis)) :
    (run (skywalkArithmeticClear base) m s).basis (base 1543)=TraceParity5.parity
      (payloadControls.map (run (skywalkArithmeticClear base) m s).basis) := by
  have payloadKeep : payloadControls.map (run (skywalkArithmeticClear base) m s).basis=
      payloadControls.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact run_preserves_outside _ _ _ _ (clear_payload_free q hq)
  rw [payloadKeep,run_preserves_outside _ _ _ _ clear_host_free]
  exact parity

theorem forward_clear_parity (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m2 m3 : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    let out := run (skywalkArithmeticClear base) m3 (run NewStackOB5.stackForwardT m2 s)
    out.basis (base 1543)=TraceParity5.parity (payloadControls.map out.basis) := by
  obtain ⟨raw,hraw⟩ : ∃raw : State,run (W.compactSkywalkForward base 1 511) [] s=raw := ⟨_,rfl⟩
  obtain ⟨enc,henc⟩ : ∃enc : State,run (NewHistory5.allEncode base 102) [] raw=enc := ⟨_,rfl⟩
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  have stage : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 512 raw.basis := by
    have stage := (W.compactSkywalkForward_spec base base_pool_nodup x p 1 511
      hp0 hx0 hpo hp hgap hx cop (by omega) s [] first).2
    rw [hraw] at stage
    exact stage
  have parity := NewHistory5.encoded_host_relation base base_pool_nodup x hx0 hx raw enc stage
    (congrArg State.basis henc.symm)
  have boundary := NewStackOB5.stackForwardT_boundary hn hlo x hx0 hx s m2 first
  rw [hraw,henc] at boundary
  have placed : (run NewStackOB5.stackForwardT m2 s).basis (base 1543)=TraceParity5.parity
      (payloadControls.map (run NewStackOB5.stackForwardT m2 s).basis) := by
    rw [boundary]
    exact placed_host_parity enc parity
  exact clear_host_parity _ m3 placed

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
