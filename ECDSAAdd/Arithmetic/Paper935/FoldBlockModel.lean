import ECDSAAdd.Arithmetic.Paper935.FoldBlock

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Boolean carry propagation model, with the same optional carry omission as
the emitted block. It contains no program execution or phase assumption. -/
def foldBlockModel (control : Wire) : List FoldCell → Option Wire → Bool → Bool → BasisState → BasisState
  | [],_,_,_,s => s
  | b::rest,cin,sums,keep,s =>
      let input := (cin.map s).getD false
      let outCarry := carryBit (s b.data) (b.literal && s control) input
      let prepared := writeBit (writeBit s b.carry outCarry) b.data (s b.data ^^ (b.literal && input))
      let tail := foldBlockModel control rest (b.next cin) sums keep prepared
      writeBit (writeBit tail b.carry (if keep && rest.isEmpty then outCarry else false)) b.data
        (if sums then sumBit (s b.data) (b.literal && s control) input else s b.data)

theorem foldBlockModel_frame (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) (s : BasisState) (q : Wire) (hq : q∉cells.flatMap FoldCell.wires) :
    foldBlockModel control cells cin sums keep s q=s q := by
  induction cells generalizing cin s with
  | nil => rfl
  | cons b rest ih =>
    have hd : q≠b.data := by intro e; apply hq; simp [e,FoldCell.wires]
    have hc : q≠b.carry := by intro e; apply hq; simp [e,FoldCell.wires]
    have hr : q∉rest.flatMap FoldCell.wires := by intro h; apply hq; simp [h]
    simp only [foldBlockModel,writeBit,Function.update_of_ne hd,Function.update_of_ne hc]
    rw [ih (b.next cin) _ hr]
    simp [hd,hc]

end ECDSAAdd.Arithmetic.Paper935
