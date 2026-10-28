/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.ValueWalkPointProgram
import ECDSAAdd.Arithmetic.PointInPlaceSupport

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem valueWalkDialogPort_wires (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPort.wires.toFinset=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hp := DialogLayout.fromPool_wires_perm L.core.poolWire L.core.generic L.point.x L.point.y
    hw.inputX hw.inputY
  rw [L.core.pool_prefix hw 2613 (by omega)] at hp
  exact List.toFinset_eq_of_perm _ _ hp

theorem valueWalkPointDialogGeneric_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (valueWalkPointDialogGeneric L cx cy)=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hd := dialog_wires L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _) (L.dialogPort_nodup hw hn)
  rw [valueWalkDialogPort_wires L hw] at hd
  apply Finset.Subset.antisymm
  · intro q
    contrapose!
    intro hnot
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,not_or] at hnot
    rcases hnot with ⟨⟨⟨ng,nx⟩,ny⟩,nb⟩
    have ntake (n : Nat) : q∉L.dialogPool.take n := fun h=>nb (List.take_subset _ _ h)
    have nslice (j n : Nat) : q∉(L.dialogPool.drop j).take n :=
      fun h=>nb (List.drop_subset _ _ (List.take_subset _ _ h))
    have nbit (i : Nat) (hi : i<2613) : q≠L.core.poolWire i := by
      intro he
      have hh : L.core.poolWire i∈L.dialogPool.take i++[L.core.poolWire i] := by simp
      rw [L.dialogBit_prefix hw i hi] at hh
      exact nb (he ▸ List.take_subset _ _ hh)
    have nConst (r : List Wire) (nr : q∉r) : q∉(L.dialogUnary r).wires := by
      simp [dialogUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModAddCoreLayout.z,ModAddCoreLayout.work,nr,ntake,nslice,nbit]
    have nNeg : q∉L.dialogNegate.wires := by
      have ntail : q∉L.dialogPool.tail.take 256 := by simpa only [List.drop_one] using nslice 1 256
      simp [dialogNegate,dialogUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModAddCoreLayout.z,ModAddCoreLayout.work,nx,ntail,nslice,nbit]
    have nMasked (r : List Wire) (v : Nat) (nr : q∉r) : q∉wires (maskedConstant L.core.generic r v) := by
      intro h; have hh := maskedConstant_wires_subset L.core.generic r v h
      simp [ng,nr] at hh
    have nCA (r : List Wire) (nr : q∉r) (hr : r.length=256) (v : Fp) :
        q∉wires (valueWalkPointDialogConstantAdd L r v) := by
      have nm := nConst r nr
      have na : q∉(L.dialogUnary r).a := fun h=>nm (by simp [ModInPlaceLayout.wires,h])
      simp only [valueWalkPointDialogConstantAdd,wires_append,Finset.mem_union,not_or]
      exact ⟨⟨nMasked _ _ na,(modPrograms_not_mem q L.core.generic ng _ (L.dialogUnary_widths hw r hr) nm).1⟩,
        nMasked _ _ na⟩
    have nswap : q∉wires (swapRegisters L.core.generic L.point.x L.dialogNegate.low) := by
      intro h
      have hh := swapRegisters_wires _ _ _ (hw.inputX.trans (L.dialogNegate_widths hw).core.low.symm) h
      have nl : q∉L.dialogNegate.low := fun h=>nNeg
        (by simp [ModInPlaceLayout.wires,ModInPlaceLayout.z,ModAddCoreLayout.z,h])
      change q∈(L.core.generic::L.point.x++L.dialogNegate.low).toFinset at hh
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,ng,nx,nl,or_false] at hh
    have ncopy : q∉wires (copyRegister (some L.core.generic) L.point.y (L.dialogPool.take 256)) := by
      rw [copyRegister_wires _ _ _ (by simp [show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])]
      split <;> simp [ng,ny,ntake]
    have nsquare : q∉wires (squareSub L.dialogSquare) := by
      apply square_layout_not_mem L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn) q
      · exact ntake 256
      · exact nx
      · rw [L.dialogSquare_work hw]; exact nslice 256 2217
    have nneg := modPrograms_not_mem q L.core.generic ng L.dialogNegate (L.dialogNegate_widths hw) nNeg
    have nD : q∉wires (dialogDivide L.dialogPort p) := by rw [hd.1]; simp [ng,nx,ny,nb]
    have nU : q∉wires (dialogMultiply L.dialogPort p) := by rw [hd.2]; simp [ng,nx,ny,nb]
    simp only [valueWalkPointDialogGeneric,valueWalkPointDialogSquare,valueWalkPointDialogNegate,wires_append,Finset.mem_union,
      nCA L.point.x nx hw.inputX _,nCA L.point.y ny hw.inputY _,nD,nU,ncopy,nsquare,
      nneg.2.2.1,nneg.2.2.2,nswap,false_or,not_false_eq_true]
  · intro q hq
    simp only [valueWalkPointDialogGeneric,wires_append,Finset.mem_union,hd.1]
    simp only [hq,true_or,or_true]
end ECDSAAdd.Arithmetic
