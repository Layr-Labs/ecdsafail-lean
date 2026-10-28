import ECDSAAdd.Arithmetic.Paper935.HornerCarryCell

namespace ECDSAAdd.Arithmetic.Paper935

/-- A quantum/quantum carry cell from luo_core.py:882–910. -/
structure HornerCarryCell where
  target : Wire
  addend : Wire
  carry : Wire

/-- luo_core.py:882–894: increasing forward carry sweep. -/
def hornerCarrySweep : List HornerCarryCell → Option Wire → Program
  | [], _ => []
  | b::bs, cin => hornerCarryForward b.target b.addend b.carry cin ++
      hornerCarrySweep bs (some b.carry)

/-- luo_core.py:897–910: descending measured cleanup. The keep flag
applies only to the highest cell of the block. -/
def hornerCarryUnsweep (ctrl : Wire) (sums keep : Bool) :
    List HornerCarryCell → Option Wire → Program
  | [], _ => []
  | b::bs, cin => hornerCarryUnsweep ctrl sums keep bs (some b.carry) ++
      hornerCarryBackward ctrl b.target b.addend b.carry cin sums (keep && bs.isEmpty)

def hornerCarryTop : List HornerCarryCell → Option Wire → Option Wire
  | [], cin => cin
  | b::bs, _ => hornerCarryTop bs (some b.carry)

theorem hornerCarrySweep_counts (bs : List HornerCarryCell) (cin : Option Wire) :
    toffoliCount (hornerCarrySweep bs cin)=bs.length ∧
    measurementCount (hornerCarrySweep bs cin)=0 := by
  induction bs generalizing cin with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have cell : toffoliCount (hornerCarryForward b.target b.addend b.carry cin)=1 ∧
        measurementCount (hornerCarryForward b.target b.addend b.carry cin)=0 := by
      cases cin <;> exact ⟨rfl,rfl⟩
    simp only [hornerCarrySweep,toffoliCount_append,measurementCount_append,
      cell.1,cell.2,(ih (some b.carry)).1,(ih (some b.carry)).2,List.length_cons]
    simp [Nat.add_comm]

theorem hornerCarryUnsweep_counts (ctrl : Wire) (sums keep : Bool)
    (bs : List HornerCarryCell) (cin : Option Wire) :
    toffoliCount (hornerCarryUnsweep ctrl sums keep bs cin)=
      (if sums then bs.length else 0) ∧
    measurementCount (hornerCarryUnsweep ctrl sums keep bs cin)=
      bs.length-(if keep then 1 else 0) := by
  induction bs generalizing cin with
  | nil => cases sums <;> cases keep <;> exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have cell (k : Bool) :
        toffoliCount (hornerCarryBackward ctrl b.target b.addend b.carry cin sums k)=
          (if sums then 1 else 0) ∧
        measurementCount (hornerCarryBackward ctrl b.target b.addend b.carry cin sums k)=
          (if k then 0 else 1) := by
      cases cin <;> cases sums <;> cases k <;> exact ⟨rfl,rfl⟩
    simp only [hornerCarryUnsweep,toffoliCount_append,measurementCount_append,
      (cell _).1,(cell _).2,(ih (some b.carry)).1,(ih (some b.carry)).2,List.length_cons]
    cases bs <;> cases sums <;> cases keep <;> simp

end ECDSAAdd.Arithmetic.Paper935
