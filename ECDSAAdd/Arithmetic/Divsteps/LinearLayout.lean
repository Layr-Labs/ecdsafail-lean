import ECDSAAdd.Arithmetic.Divsteps.SharedSwapWalk

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Consecutive signed row with an explicit low and sign bit. -/
def linearRow (base width : Nat) : StepRow :=
  ⟨base,List.range' (base+1) (width-2),base+width-1⟩

theorem linearRow_wires (base width : Nat) (hw : 2≤width) :
    (linearRow base width).wires=List.range' base width := by
  unfold linearRow StepRow.wires
  have hs : [base+width-1]=List.range' (base+1+(width-2)) 1 := by
    simp only [List.range'_succ,List.range'_zero]
    congr 2
    omega
  rw [hs,List.range'_append_1]
  have he : width-2+1=width-1 := by omega
  rw [he]
  conv_rhs => rw [show width=(width-1)+1 by omega,List.range'_succ]

/-- Fresh triples in increasing address order. -/
def linearHistory (base : Nat) : Nat → List StepHistory
  | 0 => []
  | n+1 => ⟨base,base+1,base+2⟩ :: linearHistory (base+3) n

theorem linearHistory_length (base count : Nat) : (linearHistory base count).length=count := by
  induction count generalizing base with
  | zero => rfl
  | succ n ih => simp [linearHistory,ih]

theorem linearHistory_wires (base count : Nat) :
    (linearHistory base count).flatMap StepHistory.wires=List.range' base (3*count) := by
  induction count generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [linearHistory,List.flatMap_cons,StepHistory.wires,ih]
    have ht : [base,base+1,base+2]=List.range' base 3 := by
      simp [List.range'_succ,Nat.add_assoc]
    rw [ht,List.range'_append_1]
    congr 1
    omega

/-- Fully executable consecutive-address allocator. m and c are shared mask
and carry capacities; history includes one initial triple plus slots future
triples. The measured schedule removes the unused swap addresses from support. -/
def linearLayout (n v k m c slots : Nat) : StepLayout :=
  let d := 2*n+2*v+k
  let h := d+m+c+n+2
  { f := List.range' 0 n
    g := linearRow n n
    fv := linearRow (2*n) v
    gv := List.range' (2*n+v) v
    z := linearRow (2*n+2*v) k
    mask := List.range' d m
    carry := List.range' (d+m) c
    detect := fun w => (n+2*v+k+m+c)+w
    one := d+m+c+n
    cin := d+m+c+n+1
    history := ⟨h,h+1,h+2⟩
    past := []
    future := linearHistory (h+3) slots }

private theorem range_join (a b m n : Nat) (hb : b=a+m) :
    List.range' a m ++ List.range' b n=List.range' a (m+n) := by
  rw [hb,List.range'_append_1]

theorem linearLayout_used (n v k m c slots : Nat) (hn : 2≤n) (hv : 2≤v) (hk : 2≤k) :
    (linearLayout n v k m c slots).used=List.range' 0 (3*n+2*v+k+m+c+5+3*slots) := by
  simp only [linearLayout,StepLayout.used,StepLayout.data,StepLayout.work,StepLayout.histories,
    linearRow_wires _ _ hn,linearRow_wires _ _ hv,linearRow_wires _ _ hk,
    List.map_add_range',List.flatMap_nil,List.append_nil,StepHistory.wires,linearHistory_wires]
  have two (a : Nat) : [a,a+1]=List.range' a 2 := by simp [List.range'_succ]
  have three (a : Nat) : [a,a+1,a+2]=List.range' a 3 := by
    simp [List.range'_succ,Nat.add_assoc]
  rw [two,three]
  simp only [List.append_assoc]
  repeat rw [range_join _ _ _ _ (by omega)]
  congr 1
  omega

theorem linearLayout_valid (n v k m c slots : Nat) (hn : 2≤n) (hv : 2≤v) (hk : 2≤k)
    (hmg : n≤m) (hmv : v≤m) (hmz : k≤m)
    (hcg : n-1≤c) (hcv : v-1≤c) (hcz : k-1≤c) :
    (linearLayout n v k m c slots).Valid := by
  constructor
  · rw [linearLayout_used n v k m c slots hn hv hk]
    exact List.nodup_range'
  all_goals
    simp only [linearLayout,linearRow_wires _ _ hn,linearRow_wires _ _ hv,
      linearRow_wires _ _ hk,List.length_range'] <;> assumption


theorem linearLayout_sized (n v k m c slots : Nat) (hn : 2≤n) (hk : 2≤k) :
    (linearLayout n v k m c slots).Sized n v k := by
  simp [StepLayout.Sized,linearLayout,linearRow_wires _ _ hn,linearRow_wires _ _ hk]

theorem linearLayout_capacities (n v k m c slots : Nat) :
    (linearLayout n v k m c slots).mask.length=m ∧
    (linearLayout n v k m c slots).carry.length=c ∧
    (linearLayout n v k m c slots).future.length=slots ∧
    (linearLayout n v k m c slots).past=[] := by
  simp [linearLayout,linearHistory_length]

/-- Concrete widths and capacities for the all-input 590-slot walk. -/
def numericLayout590 : StepLayout := linearLayout 258 592 11 592 591 590

theorem numericLayout590_valid : numericLayout590.Valid :=
  linearLayout_valid 258 592 11 592 591 590 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem numericLayout590_sized : numericLayout590.Sized 258 592 11 :=
  linearLayout_sized 258 592 11 592 591 590 (by decide) (by decide)

theorem numericLayout590_capacities :
    numericLayout590.mask.length=592 ∧ numericLayout590.carry.length=591 ∧
    numericLayout590.future.length=590 ∧ numericLayout590.past=[] :=
  linearLayout_capacities 258 592 11 592 591 590

theorem numericLayout590_used : numericLayout590.used=List.range' 0 4927 :=
  linearLayout_used 258 592 11 592 591 590 (by decide) (by decide) (by decide)

theorem numericLayout590_shared_length : numericLayout590.sharedUsed.length=4337 := by
  have hh := numericLayout590.sharedUsed_sized_length numericLayout590_valid 258 592 11
    numericLayout590_sized
  rw [numericLayout590_capacities.1,numericLayout590_capacities.2.1,
    numericLayout590_capacities.2.2.1] at hh
  exact hh

/-- Executable recorded program with no abstract layout parameter. Addresses
are labels: the support has at most 4337 wires inside the old 4927-label range. -/
def numericDivsteps590 (cursor : Nat) : RecordedProgram :=
  numericLayout590.sharedSwaps 0 590 cursor

theorem numericDivsteps590_correct (p x : Int) (hp : 0≤p) (hodd : p%2=1)
    (hsmall : p<2^256) (hx : 0≤x) (hxp : x≤p) (s : State) (m : List Bool) (cursor : Nat)
    (hs : numericLayout590.SharedReady 0 (ECDSAAdd.Divsteps.zSeed p x) s.basis) :
    runWithTape (numericDivsteps590 cursor) m cursor s=s :=
  numericLayout590.sharedSwaps590_correct numericLayout590_valid numericLayout590_sized
    (by rw [numericLayout590_capacities.2.2.1]) p x hp hodd hsmall hx hxp s m cursor hs

theorem numericDivsteps590_counts (cursor : Nat) :
    recordedToffoliCount (numericDivsteps590 cursor)=5023850 ∧
    recordedMeasurementCount (numericDivsteps590 cursor)=3321110 :=
  numericLayout590.sharedSwaps590_counts numericLayout590_valid numericLayout590_sized cursor

theorem numericLayout590_wellFormed (slots cursor : Nat) :
    RecordedWellFormedAt cursor (numericLayout590.sharedSwaps 0 slots cursor) :=
  numericLayout590.sharedSwaps_wellFormed 0 slots cursor

theorem numericDivsteps590_support (cursor : Nat) :
    recordedWires (numericDivsteps590 cursor)⊆numericLayout590.sharedUsed.toFinset :=
  numericLayout590.sharedSwaps_support numericLayout590_valid 0 590 cursor

theorem numericDivsteps590_qubits (cursor : Nat) :
    (recordedWires (numericDivsteps590 cursor)).card≤4337 :=
  numericLayout590.sharedSwaps590_qubits numericLayout590_valid numericLayout590_sized
    (by rw [numericLayout590_capacities.1]) (by rw [numericLayout590_capacities.2.1])
    numericLayout590_capacities.2.2.1 cursor

end ECDSAAdd.Arithmetic.Divsteps
