import ECDSAAdd.Arithmetic.ConstStageSpec
import ECDSAAdd.Math.MontgomeryConversion

namespace ECDSAAdd.Arithmetic

/-- 两段只分配一份临时工作区，各自保存累加器、记录带和借位。 -/
structure MontLayout where
  x : List Wire
  y : List Wire
  out : List Wire
  first : MontStageLayout
  z : List Wire
  hZ : List Wire
  fZ : Wire

namespace MontLayout

def a (M : MontLayout) : List Wire := M.first.acc
def hA (M : MontLayout) : List Wire := M.first.history
def fA (M : MontLayout) : Wire := M.first.flag
def shared (M : MontLayout) : List Wire := M.first.work
def second (M : MontLayout) : MontStageLayout := { M.first with acc:=M.z,history:=M.hZ,flag:=M.fZ }
def activeA (M : MontLayout) : List Wire := M.a++M.hA++[M.fA]
def activeZ (M : MontLayout) : List Wire := M.z++M.hZ++[M.fZ]
def work (M : MontLayout) : List Wire := M.activeA++M.activeZ++M.shared
def wires (M : MontLayout) : List Wire := M.x++M.y++M.out++M.work

structure Widths (M : MontLayout) : Prop where
  x : M.x.length=257
  y : M.y.length=256
  out : M.out.length=257
  first : M.first.Widths
  z : M.z.length=261
  hZ : M.hZ.length=256

theorem second_widths (M : MontLayout) (hw : M.Widths) : M.second.Widths :=
  ⟨hw.z,hw.hZ,hw.first.table,hw.first.mask,hw.first.carry,hw.first.pad,hw.first.scratch⟩

theorem first_nodup (M : MontLayout) (hnd : M.wires.Nodup) : (M.x++M.y++M.first.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,work,activeA,activeZ,a,hA,fA,shared,MontStageLayout.wires,List.count_append] at h ⊢; omega

theorem second_nodup (M : MontLayout) (hnd : M.wires.Nodup) : (M.a++M.second.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hnd w
  simp only [wires,work,activeA,activeZ,a,hA,fA,shared,second,MontStageLayout.wires,MontStageLayout.work,List.count_append] at h ⊢; omega

theorem first_disjoint (M : MontLayout) (hnd : M.wires.Nodup) :
    (M.x++M.y++M.out++M.activeZ++M.shared).Disjoint M.activeA := by
  apply List.disjoint_left.mpr; intro w hw hh
  have h := List.nodup_iff_count.mp hnd w
  have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr hh
  simp only [wires,work,List.count_append] at h h1 h2; omega

theorem second_disjoint (M : MontLayout) (hnd : M.wires.Nodup) :
    (M.x++M.y++M.out++M.activeA++M.shared).Disjoint M.activeZ := by
  apply List.disjoint_left.mpr; intro w hw hh
  have h := List.nodup_iff_count.mp hnd w
  have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr hh
  simp only [wires,work,List.count_append] at h h1 h2; omega

theorem work_clean (M : MontLayout) (s : BasisState) (h : regValue M.work s=0)
    (r : List Wire) (hr : r⊆M.work) : regValue r s=0 :=
  (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp h w (hr hw))

end MontLayout

/-- 内部准备后的完整寄存器契约；历史与借位不是空工作位。 -/
structure MontPrepared (M : MontLayout) (p X Y : Nat) (s : BasisState) : Prop where
  x : regValue M.x s=X
  y : regValue M.y s=Y
  a : regValue M.a s=montgomeryValue p X Y 64%p
  z : regValue M.z s=(X*Y)%p
  hA : regValue M.hA s=montgomeryQuotient p X Y 64
  hZ : regValue M.hZ s=montgomeryQuotient p (montgomeryConversion p) (montgomeryValue p X Y 64%p) 64
  fA : s M.fA=decide (montgomeryValue p X Y 64<p)
  fZ : s M.fZ=decide (montgomeryValue p (montgomeryConversion p) (montgomeryValue p X Y 64%p) 64<p)
  shared : regValue M.shared s=0

def montP (M : MontLayout) (p : Nat) : Program :=
  montPrepare M.first M.x M.y p ++ constPrepare M.second M.a p (montgomeryConversion p)

def montQ (M : MontLayout) (p : Nat) : Program :=
  constRestore M.second M.a p (montgomeryConversion p) ++ montRestore M.first M.x M.y p

end ECDSAAdd.Arithmetic
