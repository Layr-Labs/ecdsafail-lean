import ECDSAAdd.Arithmetic.InverseQuotientRecorded
import ECDSAAdd.Arithmetic.MontAdapterResources

namespace ECDSAAdd.Arithmetic.InverseQuotientCore
open Secp256k1
attribute [local irreducible] montMulControlledAdd montMulControlledSub swapRegisters

theorem support (c : Wire) (M : MontLayout) (den : List Wire)
    (hw : M.Widths) (hd : den.length = 257) :
    wires (program c M den) ⊆ (c :: den ++ M.wires).toFinset := by
  have hw' : (denView M den).Widths := ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  have ha := (montControlledAdapter_wires c M p hw).1
  have hb := (montControlledAdapter_wires c (denView M den) p hw').2
  have hs := swapRegisters_wires c (M.y.take 256) (M.out.take 256)
    (by simp [hw.y,hw.out])
  intro q hq
  simp only [program,wires_append,ha,hb,Finset.mem_union] at hq
  have subx : q ∈ M.x.take 256 → q ∈ M.x := List.mem_of_mem_take
  have suby : q ∈ M.y.take 256 → q ∈ M.y := List.mem_of_mem_take
  have subo : q ∈ M.out.take 256 → q ∈ M.out := List.mem_of_mem_take
  have subd : q ∈ den.take 256 → q ∈ den := List.mem_of_mem_take
  rcases hq with (ha | hswap) | hb
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append,MontLayout.wires] at ha ⊢
    tauto
  · have h := hs hswap
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,MontLayout.wires] at h ⊢
    tauto
  · change q ∈ (c :: den.take 256 ++ M.y ++ M.out ++ M.work).toFinset at hb
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,MontLayout.wires] at hb ⊢
    tauto

end ECDSAAdd.Arithmetic.InverseQuotientCore
