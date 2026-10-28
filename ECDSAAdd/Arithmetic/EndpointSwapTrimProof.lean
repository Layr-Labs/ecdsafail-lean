import ECDSAAdd.Arithmetic.EndpointSwapTrimProgram
import ECDSAAdd.Arithmetic.OffsetBorrowedSerializedCellProof
import ECDSAAdd.Arithmetic.PairFrameUnique

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.EndpointSwapTrim
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run OffsetBorrowedField.program OffsetBorrowedInverse.program
  BalancedCircuit.program BalancedInverse.program

private theorem swap_equal_pair (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (X : Nat) :
    Triple (PairFrame r y base X X) (swapRegisters c r y) (PairFrame r y base X X) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · simpa only [h.1,h.2.1,ite_self] using v.2.2.1
  · simpa only [h.1,h.2.1,ite_self] using v.2.2.2

/-- The complete actual measured S window is identity on equal words,
including both control polarities and every outcome. Its flag must start0. -/
theorem swap_window_state (r y : List Wire) (b src flag : Wire) (constant : Bool)
    (hlen : r.length=y.length) (hn : (flag::r++y).Nodup)
    (nd : [b,src,flag].Nodup) (hb : b∉r ∧ b∉y) (hs : src∉r ∧ src∉y)
    (s : State) (m : List Bool) (hz : s.basis flag=false)
    (heq : regValue r s.basis=regValue y s.basis) :
    run (transcriptSelectWindow b src flag constant (swapRegisters flag r y)) m s=s := by
  have hf : flag∉r ∧ flag∉y := by
    have away := (List.nodup_cons.mp hn).1
    exact ⟨fun h => away (List.mem_append_left _ h),
      fun h => away (List.mem_append_right _ h)⟩
  let X := regValue r s.basis
  have input : PairFrame r y s.basis X X s.basis := ⟨rfl,heq.symm,fun _ _ _ => rfl⟩
  have body := swap_equal_pair r y flag hlen hn
    (mixedTranscriptBase s.basis b src flag constant) X
  have window := transcriptSelectWindow_pairFrame b src flag constant r y
    nd hb hs hf s.basis hz X X X X (swapRegisters flag r y) body
  have out := window s m input
  apply State.extensionality
  · exact out.1
  · exact PairFrame.unique r y s.basis X X _ _ out.2 input

private theorem kernel_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w)
    (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      ([.X sign]++(if divide then OffsetBorrowedField.program w sign
        else OffsetBorrowedInverse.program w sign)++[.X sign])
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if base sign then Y else -Y))/2
          else 2*X+(if base sign then -Y else Y))) (centerWord Y)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have clean := balancedSharedPorts_clean w sign base he.1 he.2.1
  cases divide
  · have old := balancedTranscriptDouble_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [Bool.false_eq_true,if_false]
    rw [← OffsetBorrowedInverseCanonical.double,
      OffsetBorrowedInverseCanonical.double_eq w sign hn ho base he X Y s m h]
    exact old s m h
  · have old := balancedTranscriptHalf_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [if_true]
    rw [OffsetBorrowedSerialized.half_eq w sign hn ho base he X Y s m h]
    exact old s m h

theorem partial_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w)
    (nd : [b,g,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hg : g∉(balancedSharedPorts w sign).r ∧ g∉(balancedSharedPorts w sign).y)
    (hs : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (base : BasisState) (hz : base sign=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (if divide then forward w b g sign ig else inverse w b g sign ig)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit base b g ig then -Y else Y))) (centerWord Y)) := by
  have body := kernel_frame divide w sign hn ho
    (mixedTranscriptBase base b g sign ig) (env_write w sign ho base _ he) X Y
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  have window := transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs
    base hz _ _ _ _ _ body
  cases divide <;> simpa only [forward,inverse,Bool.false_eq_true,if_false,if_true] using window

private theorem flags (w : Nat → Wire) (b g swap sign effS : Wire)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS) :
    [b,g,sign].Nodup ∧
    (b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y) ∧
    (g∉(balancedSharedPorts w sign).r ∧ g∉(balancedSharedPorts w sign).y) ∧
    (sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y) := by
  have ctrl := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ctrl
  refine ⟨?_,hl.outside b (by simp),hl.outside g (by simp),
    hl.outside sign (by simp [balancedSharedPorts])⟩
  simp [List.nodup_cons]
  tauto

/-- Equal output coordinates reflect equality at the original final swap
boundary. This algebraic fact does not constrain the selected G or S. -/
theorem forward_dup_of_payload_equal (G S : Bool) (X Y : Fp)
    (h : (skywalkPayloadCell G S (X,Y)).1=(skywalkPayloadCell G S (X,Y)).2) :
    (X+(if G then Y else -Y))/2=Y := by
  cases S with
  | false => simpa only [skywalkPayloadCell,Bool.false_eq_true,if_false] using h
  | true =>
    have eq : Y=(X+(if G then Y else -Y))/2 := by
      simpa only [skywalkPayloadCell,if_true] using h
    exact eq.symm

theorem forward_support_subset (w : Nat → Wire) (b g swap sign : Wire) (ig is : Bool) :
    wires (forward w b g sign ig)⊆
      wires (OffsetBorrowedSerialized.forward w b g swap sign ig is) := by
  change wires (forward w b g sign ig)⊆
    wires (forward w b g sign ig ++ transcriptSelectWindow b swap sign is
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y))
  rw [wires_append]
  exact Finset.subset_union_left

theorem inverse_support_subset (w : Nat → Wire) (b g swap sign : Wire) (ig is : Bool) :
    wires (inverse w b g sign ig)⊆
      wires (OffsetBorrowedSerialized.inverse w b g swap sign ig is) := by
  change wires (inverse w b g sign ig)⊆
    wires (transcriptSelectWindow b swap sign is
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y) ++
        inverse w b g sign ig)
  rw [wires_append]
  exact Finset.subset_union_right

/-- Forward duplication is required at the swap boundary, not at the input.
The accepted final replay postcondition supplies this equality. G may be either
value: there is no unsupported assumption that the penultimate state is done. -/
theorem forward_oldcell_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hz : base sign=false) (hS : base effS=false) (he : Env w base)
    (X Y : Fp)
    (dup : (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2=Y)
    (s : State) (mNew mOld : List Bool)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (forward w b g sign ig) mNew s=
      run (OffsetBorrowedCanonical.cell w b g swap sign effS ig is) mOld s := by
  have f := flags w b g swap sign effS hl
  have fresh := partial_frame true w b g sign ig hn ho f.1 f.2.1 f.2.2.1 f.2.2.2
    base hz he X Y
  simp only [if_true,dup] at fresh
  have old := OffsetBorrowedCanonical.cell_frame w b g swap sign effS ig is
    hn hl ho hoS base hz hS he X Y
  have old' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (OffsetBorrowedCanonical.cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord Y) (centerWord Y)) := by
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [skywalkPayloadCell,dup,hswap,if_true,if_false,Bool.false_eq_true] using old
  exact PairFrame.program_eq _ _ base _ _ _ _ _ _ fresh old' s mNew mOld input

/-- Inverse input duplication makes its initial swap identity for arbitrary
selected S; complete frames compare independent measurement streams. -/
theorem inverse_oldcell_eq (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hz : base sign=false) (hS : base effS=false) (he : Env w base)
    (Y : Fp) (s : State) (mNew mOld : List Bool)
    (input : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord Y) (centerWord Y) s.basis) :
    run (inverse w b g sign ig) mNew s=
      run (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is) mOld s := by
  have f := flags w b g swap sign effS hl
  have fresh := partial_frame false w b g sign ig hn ho f.1 f.2.1 f.2.2.1 f.2.2.2
    base hz he Y Y
  simp only [Bool.false_eq_true,if_false] at fresh
  have old := OffsetBorrowedInverseCanonical.cell_frame w b g swap sign effS ig is
    hn hl ho hoS base hz hS he Y Y
  have old' : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord Y) (centerWord Y)) (OffsetBorrowedInverseCanonical.cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (2*Y+(if mixedTranscriptBit base b g ig then -Y else Y))) (centerWord Y)) := by
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [skywalkPayloadUncell,hswap,if_true,if_false,Bool.false_eq_true] using old
  exact PairFrame.program_eq _ _ base _ _ _ _ _ _ fresh old' s mNew mOld input

end ECDSAAdd.Arithmetic.EndpointSwapTrim
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.partial_frame
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.swap_window_state
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.forward_dup_of_payload_equal
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.forward_support_subset
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.inverse_support_subset
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.forward_oldcell_eq
#print axioms ECDSAAdd.Arithmetic.EndpointSwapTrim.inverse_oldcell_eq
