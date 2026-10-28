import ECDSAAdd.Arithmetic.Paper935.HmrSupportList
import ECDSAAdd.Arithmetic.Paper935.HmrDataUses
import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts
namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] s2HmrSourceLayout s6HmrSourceLayout

private theorem s2Forward_ports_0 : (List.range' 0 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_32 : (List.range' 32 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_64 : (List.range' 64 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_96 : (List.range' 96 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_128 : (List.range' 128 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_160 : (List.range' 160 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_192 : (List.range' 192 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_224 : (List.range' 224 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_256 : (List.range' 256 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_288 : (List.range' 288 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_320 : (List.range' 320 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_352 : (List.range' 352 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_384 : (List.range' 384 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_416 : (List.range' 416 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_448 : (List.range' 448 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_480 : (List.range' 480 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_512 : (List.range' 512 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_544 : (List.range' 544 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_576 : (List.range' 576 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_608 : (List.range' 608 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_640 : (List.range' 640 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_672 : (List.range' 672 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_704 : (List.range' 704 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_736 : (List.range' 736 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_768 : (List.range' 768 32).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

private theorem s2Forward_ports_800 : (List.range' 800 20).all (fun q =>
    decide (rowMulPort s2ForwardPorts 0 q ∈ s2SupportList)) = true := by
  decide +kernel

attribute [local irreducible] s2ForwardPorts

private theorem s2Forward_ports_checked : ∀ q ∈ Finset.range 820,
    rowMulPort s2ForwardPorts 0 q ∈ s2SupportList := by
  intro q hq
  have hlt := Finset.mem_range.mp hq

  by_cases h0 : q < 32
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_0) q
      (by rw [List.mem_range']; exact ⟨q - 0, by omega, by omega⟩))

  by_cases h32 : q < 64
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_32) q
      (by rw [List.mem_range']; exact ⟨q - 32, by omega, by omega⟩))

  by_cases h64 : q < 96
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_64) q
      (by rw [List.mem_range']; exact ⟨q - 64, by omega, by omega⟩))

  by_cases h96 : q < 128
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_96) q
      (by rw [List.mem_range']; exact ⟨q - 96, by omega, by omega⟩))

  by_cases h128 : q < 160
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_128) q
      (by rw [List.mem_range']; exact ⟨q - 128, by omega, by omega⟩))

  by_cases h160 : q < 192
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_160) q
      (by rw [List.mem_range']; exact ⟨q - 160, by omega, by omega⟩))

  by_cases h192 : q < 224
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_192) q
      (by rw [List.mem_range']; exact ⟨q - 192, by omega, by omega⟩))

  by_cases h224 : q < 256
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_224) q
      (by rw [List.mem_range']; exact ⟨q - 224, by omega, by omega⟩))

  by_cases h256 : q < 288
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_256) q
      (by rw [List.mem_range']; exact ⟨q - 256, by omega, by omega⟩))

  by_cases h288 : q < 320
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_288) q
      (by rw [List.mem_range']; exact ⟨q - 288, by omega, by omega⟩))

  by_cases h320 : q < 352
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_320) q
      (by rw [List.mem_range']; exact ⟨q - 320, by omega, by omega⟩))

  by_cases h352 : q < 384
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_352) q
      (by rw [List.mem_range']; exact ⟨q - 352, by omega, by omega⟩))

  by_cases h384 : q < 416
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_384) q
      (by rw [List.mem_range']; exact ⟨q - 384, by omega, by omega⟩))

  by_cases h416 : q < 448
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_416) q
      (by rw [List.mem_range']; exact ⟨q - 416, by omega, by omega⟩))

  by_cases h448 : q < 480
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_448) q
      (by rw [List.mem_range']; exact ⟨q - 448, by omega, by omega⟩))

  by_cases h480 : q < 512
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_480) q
      (by rw [List.mem_range']; exact ⟨q - 480, by omega, by omega⟩))

  by_cases h512 : q < 544
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_512) q
      (by rw [List.mem_range']; exact ⟨q - 512, by omega, by omega⟩))

  by_cases h544 : q < 576
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_544) q
      (by rw [List.mem_range']; exact ⟨q - 544, by omega, by omega⟩))

  by_cases h576 : q < 608
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_576) q
      (by rw [List.mem_range']; exact ⟨q - 576, by omega, by omega⟩))

  by_cases h608 : q < 640
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_608) q
      (by rw [List.mem_range']; exact ⟨q - 608, by omega, by omega⟩))

  by_cases h640 : q < 672
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_640) q
      (by rw [List.mem_range']; exact ⟨q - 640, by omega, by omega⟩))

  by_cases h672 : q < 704
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_672) q
      (by rw [List.mem_range']; exact ⟨q - 672, by omega, by omega⟩))

  by_cases h704 : q < 736
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_704) q
      (by rw [List.mem_range']; exact ⟨q - 704, by omega, by omega⟩))

  by_cases h736 : q < 768
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_736) q
      (by rw [List.mem_range']; exact ⟨q - 736, by omega, by omega⟩))

  by_cases h768 : q < 800
  · exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_768) q
      (by rw [List.mem_range']; exact ⟨q - 768, by omega, by omega⟩))

  exact of_decide_eq_true ((List.all_eq_true.mp s2Forward_ports_800) q
      (by rw [List.mem_range']; exact ⟨q - 800, by omega, by omega⟩))
private theorem s2Forward_controls_checked : ∀ u ∈ s2ForwardUses,
    u.control ∈ s2SupportList := by decide +kernel

attribute [local irreducible] s2ForwardUses

theorem s2Forward_support_checked : recordedWires s2ForwardProgram ⊆ s2HmrSourceLayout.support := by
  unfold s2ForwardProgram
  exact rowMulUses_support _ _ _ _
    (fun q hq => (s2SupportList_mem _).mp (s2Forward_ports_checked q hq))
    (fun u hu => (s2SupportList_mem _).mp (s2Forward_controls_checked u hu))

theorem s2Forward_wellFormed_checked (cursor : Nat) : RecordedWellFormedAt cursor s2ForwardProgram := by
  apply hmrGatesOnly_wellFormed
  exact rowMulUses_gatesOnly _ _ _

private theorem s6Forward_ports_0 : (List.range' 0 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_32 : (List.range' 32 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_64 : (List.range' 64 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_96 : (List.range' 96 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_128 : (List.range' 128 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_160 : (List.range' 160 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_192 : (List.range' 192 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_224 : (List.range' 224 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_256 : (List.range' 256 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_288 : (List.range' 288 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_320 : (List.range' 320 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_352 : (List.range' 352 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_384 : (List.range' 384 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_416 : (List.range' 416 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_448 : (List.range' 448 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_480 : (List.range' 480 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_512 : (List.range' 512 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_544 : (List.range' 544 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_576 : (List.range' 576 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_608 : (List.range' 608 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_640 : (List.range' 640 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_672 : (List.range' 672 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_704 : (List.range' 704 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_736 : (List.range' 736 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_768 : (List.range' 768 32).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Forward_ports_800 : (List.range' 800 20).all (fun q =>
    decide (rowMulPort s6ForwardPorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

attribute [local irreducible] s6ForwardPorts

private theorem s6Forward_ports_checked : ∀ q ∈ Finset.range 820,
    rowMulPort s6ForwardPorts 0 q ∈ s6SupportList := by
  intro q hq
  have hlt := Finset.mem_range.mp hq

  by_cases h0 : q < 32
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_0) q
      (by rw [List.mem_range']; exact ⟨q - 0, by omega, by omega⟩))

  by_cases h32 : q < 64
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_32) q
      (by rw [List.mem_range']; exact ⟨q - 32, by omega, by omega⟩))

  by_cases h64 : q < 96
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_64) q
      (by rw [List.mem_range']; exact ⟨q - 64, by omega, by omega⟩))

  by_cases h96 : q < 128
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_96) q
      (by rw [List.mem_range']; exact ⟨q - 96, by omega, by omega⟩))

  by_cases h128 : q < 160
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_128) q
      (by rw [List.mem_range']; exact ⟨q - 128, by omega, by omega⟩))

  by_cases h160 : q < 192
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_160) q
      (by rw [List.mem_range']; exact ⟨q - 160, by omega, by omega⟩))

  by_cases h192 : q < 224
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_192) q
      (by rw [List.mem_range']; exact ⟨q - 192, by omega, by omega⟩))

  by_cases h224 : q < 256
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_224) q
      (by rw [List.mem_range']; exact ⟨q - 224, by omega, by omega⟩))

  by_cases h256 : q < 288
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_256) q
      (by rw [List.mem_range']; exact ⟨q - 256, by omega, by omega⟩))

  by_cases h288 : q < 320
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_288) q
      (by rw [List.mem_range']; exact ⟨q - 288, by omega, by omega⟩))

  by_cases h320 : q < 352
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_320) q
      (by rw [List.mem_range']; exact ⟨q - 320, by omega, by omega⟩))

  by_cases h352 : q < 384
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_352) q
      (by rw [List.mem_range']; exact ⟨q - 352, by omega, by omega⟩))

  by_cases h384 : q < 416
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_384) q
      (by rw [List.mem_range']; exact ⟨q - 384, by omega, by omega⟩))

  by_cases h416 : q < 448
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_416) q
      (by rw [List.mem_range']; exact ⟨q - 416, by omega, by omega⟩))

  by_cases h448 : q < 480
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_448) q
      (by rw [List.mem_range']; exact ⟨q - 448, by omega, by omega⟩))

  by_cases h480 : q < 512
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_480) q
      (by rw [List.mem_range']; exact ⟨q - 480, by omega, by omega⟩))

  by_cases h512 : q < 544
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_512) q
      (by rw [List.mem_range']; exact ⟨q - 512, by omega, by omega⟩))

  by_cases h544 : q < 576
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_544) q
      (by rw [List.mem_range']; exact ⟨q - 544, by omega, by omega⟩))

  by_cases h576 : q < 608
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_576) q
      (by rw [List.mem_range']; exact ⟨q - 576, by omega, by omega⟩))

  by_cases h608 : q < 640
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_608) q
      (by rw [List.mem_range']; exact ⟨q - 608, by omega, by omega⟩))

  by_cases h640 : q < 672
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_640) q
      (by rw [List.mem_range']; exact ⟨q - 640, by omega, by omega⟩))

  by_cases h672 : q < 704
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_672) q
      (by rw [List.mem_range']; exact ⟨q - 672, by omega, by omega⟩))

  by_cases h704 : q < 736
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_704) q
      (by rw [List.mem_range']; exact ⟨q - 704, by omega, by omega⟩))

  by_cases h736 : q < 768
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_736) q
      (by rw [List.mem_range']; exact ⟨q - 736, by omega, by omega⟩))

  by_cases h768 : q < 800
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_768) q
      (by rw [List.mem_range']; exact ⟨q - 768, by omega, by omega⟩))

  exact of_decide_eq_true ((List.all_eq_true.mp s6Forward_ports_800) q
      (by rw [List.mem_range']; exact ⟨q - 800, by omega, by omega⟩))
private theorem s6Forward_controls_checked : ∀ u ∈ s6ForwardUses,
    u.control ∈ s6SupportList := by decide +kernel

attribute [local irreducible] s6ForwardUses

theorem s6Forward_support_checked : recordedWires s6ForwardProgram ⊆ s6HmrSourceLayout.support := by
  unfold s6ForwardProgram
  exact rowMulUses_support _ _ _ _
    (fun q hq => (s6SupportList_mem _).mp (s6Forward_ports_checked q hq))
    (fun u hu => (s6SupportList_mem _).mp (s6Forward_controls_checked u hu))

theorem s6Forward_wellFormed_checked (cursor : Nat) : RecordedWellFormedAt cursor s6ForwardProgram := by
  apply hmrGatesOnly_wellFormed
  exact rowMulUses_gatesOnly _ _ _

private theorem s6Erase_ports_0 : (List.range' 0 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_32 : (List.range' 32 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_64 : (List.range' 64 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_96 : (List.range' 96 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_128 : (List.range' 128 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_160 : (List.range' 160 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_192 : (List.range' 192 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_224 : (List.range' 224 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_256 : (List.range' 256 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_288 : (List.range' 288 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_320 : (List.range' 320 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_352 : (List.range' 352 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_384 : (List.range' 384 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_416 : (List.range' 416 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_448 : (List.range' 448 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_480 : (List.range' 480 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_512 : (List.range' 512 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_544 : (List.range' 544 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_576 : (List.range' 576 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_608 : (List.range' 608 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_640 : (List.range' 640 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_672 : (List.range' 672 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_704 : (List.range' 704 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_736 : (List.range' 736 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_768 : (List.range' 768 32).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

private theorem s6Erase_ports_800 : (List.range' 800 20).all (fun q =>
    decide (rowMulPort s6ErasePorts 0 q ∈ s6SupportList)) = true := by
  decide +kernel

attribute [local irreducible] s6ErasePorts

private theorem s6Erase_ports_checked : ∀ q ∈ Finset.range 820,
    rowMulPort s6ErasePorts 0 q ∈ s6SupportList := by
  intro q hq
  have hlt := Finset.mem_range.mp hq

  by_cases h0 : q < 32
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_0) q
      (by rw [List.mem_range']; exact ⟨q - 0, by omega, by omega⟩))

  by_cases h32 : q < 64
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_32) q
      (by rw [List.mem_range']; exact ⟨q - 32, by omega, by omega⟩))

  by_cases h64 : q < 96
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_64) q
      (by rw [List.mem_range']; exact ⟨q - 64, by omega, by omega⟩))

  by_cases h96 : q < 128
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_96) q
      (by rw [List.mem_range']; exact ⟨q - 96, by omega, by omega⟩))

  by_cases h128 : q < 160
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_128) q
      (by rw [List.mem_range']; exact ⟨q - 128, by omega, by omega⟩))

  by_cases h160 : q < 192
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_160) q
      (by rw [List.mem_range']; exact ⟨q - 160, by omega, by omega⟩))

  by_cases h192 : q < 224
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_192) q
      (by rw [List.mem_range']; exact ⟨q - 192, by omega, by omega⟩))

  by_cases h224 : q < 256
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_224) q
      (by rw [List.mem_range']; exact ⟨q - 224, by omega, by omega⟩))

  by_cases h256 : q < 288
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_256) q
      (by rw [List.mem_range']; exact ⟨q - 256, by omega, by omega⟩))

  by_cases h288 : q < 320
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_288) q
      (by rw [List.mem_range']; exact ⟨q - 288, by omega, by omega⟩))

  by_cases h320 : q < 352
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_320) q
      (by rw [List.mem_range']; exact ⟨q - 320, by omega, by omega⟩))

  by_cases h352 : q < 384
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_352) q
      (by rw [List.mem_range']; exact ⟨q - 352, by omega, by omega⟩))

  by_cases h384 : q < 416
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_384) q
      (by rw [List.mem_range']; exact ⟨q - 384, by omega, by omega⟩))

  by_cases h416 : q < 448
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_416) q
      (by rw [List.mem_range']; exact ⟨q - 416, by omega, by omega⟩))

  by_cases h448 : q < 480
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_448) q
      (by rw [List.mem_range']; exact ⟨q - 448, by omega, by omega⟩))

  by_cases h480 : q < 512
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_480) q
      (by rw [List.mem_range']; exact ⟨q - 480, by omega, by omega⟩))

  by_cases h512 : q < 544
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_512) q
      (by rw [List.mem_range']; exact ⟨q - 512, by omega, by omega⟩))

  by_cases h544 : q < 576
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_544) q
      (by rw [List.mem_range']; exact ⟨q - 544, by omega, by omega⟩))

  by_cases h576 : q < 608
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_576) q
      (by rw [List.mem_range']; exact ⟨q - 576, by omega, by omega⟩))

  by_cases h608 : q < 640
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_608) q
      (by rw [List.mem_range']; exact ⟨q - 608, by omega, by omega⟩))

  by_cases h640 : q < 672
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_640) q
      (by rw [List.mem_range']; exact ⟨q - 640, by omega, by omega⟩))

  by_cases h672 : q < 704
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_672) q
      (by rw [List.mem_range']; exact ⟨q - 672, by omega, by omega⟩))

  by_cases h704 : q < 736
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_704) q
      (by rw [List.mem_range']; exact ⟨q - 704, by omega, by omega⟩))

  by_cases h736 : q < 768
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_736) q
      (by rw [List.mem_range']; exact ⟨q - 736, by omega, by omega⟩))

  by_cases h768 : q < 800
  · exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_768) q
      (by rw [List.mem_range']; exact ⟨q - 768, by omega, by omega⟩))

  exact of_decide_eq_true ((List.all_eq_true.mp s6Erase_ports_800) q
      (by rw [List.mem_range']; exact ⟨q - 800, by omega, by omega⟩))
private theorem s6Erase_controls_checked : ∀ u ∈ s6EraseUses,
    u.control ∈ s6SupportList := by decide +kernel

attribute [local irreducible] s6EraseUses

theorem s6Erase_support_checked : recordedWires s6EraseProgram ⊆ s6HmrSourceLayout.support := by
  unfold s6EraseProgram
  exact rowMulUses_support _ _ _ _
    (fun q hq => (s6SupportList_mem _).mp (s6Erase_ports_checked q hq))
    (fun u hu => (s6SupportList_mem _).mp (s6Erase_controls_checked u hu))

theorem s6Erase_wellFormed_checked (cursor : Nat) : RecordedWellFormedAt cursor s6EraseProgram := by
  apply hmrGatesOnly_wellFormed
  exact rowMulUses_gatesOnly _ _ _
end ECDSAAdd.Arithmetic.Paper935
