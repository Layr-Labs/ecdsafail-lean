import ECDSAAdd.Math.Divsteps.Bounds

namespace ECDSAAdd.Divsteps

/-- Values supplied to the shared physical kernel after controlled row routing. -/
def swapControl (s : ZState) : Bool := decide (0≤s.z ∧ s.g%2=1)
def parityControl (s : ZState) : Bool := decide (s.g%2=1)
def routedF (s : ZState) : Int := if swapControl s then s.g else s.f
def routedG (s : ZState) : Int := if swapControl s then s.f else s.g
def routedFv (s : ZState) : Int := if swapControl s then s.gv else s.fv
def routedGv (s : ZState) : Int := if swapControl s then s.fv else s.gv
def rowValue (q c : Bool) (A B : Int) : Int := (if q then -B else B)+(if c then A else 0)

theorem rowValue_zStep (s : ZState) :
    (zStep s).g=rowValue (swapControl s) (parityControl s) (routedF s) (routedG s)/2 ∧
    (zStep s).gv=rowValue (swapControl s) (parityControl s) (routedFv s) (routedGv s) := by
  have hg : s.g%2=0 ∨ s.g%2=1 := by omega
  rcases hg with hg | hg
  all_goals
    by_cases hs : 0≤s.z
    all_goals simp [zStep,rowValue,swapControl,parityControl,routedF,routedG,routedFv,routedGv,
      hg,hs,sub_eq_add_neg,add_comm]

theorem rowValue_even (s : ZState) (hf : s.f%2=1) :
    rowValue (swapControl s) (parityControl s) (routedF s) (routedG s)%2=0 := by
  have hg : s.g%2=0 ∨ s.g%2=1 := by omega
  rcases hg with hg | hg
  all_goals
    by_cases hs : 0≤s.z
    all_goals simp [rowValue,swapControl,parityControl,routedF,routedG,hg,hs] <;> omega

/-- Conservative per-call magnitude bounds include the pre-halving numerator,
which can be twice as large as the stored integer-row result. -/
theorem rowValue_bounds (q c : Bool) (A B K : Int)
    (hA : -K≤A ∧ A≤K) (hB : -K≤B ∧ B≤K) :
    (-K≤(if q then -B else B) ∧ (if q then -B else B)≤K) ∧
    -2*K≤rowValue q c A B ∧ rowValue q c A B≤2*K := by
  cases q <;> cases c <;> simp [rowValue] <;> omega

theorem routed_rows_bounds {pB zB cB : Int} {s : ZState} (h : Bounds pB zB cB s) :
    (-pB≤routedF s ∧ routedF s≤pB) ∧ (-pB≤routedG s ∧ routedG s≤pB) ∧
    (-cB≤routedFv s ∧ routedFv s≤cB) ∧ (-cB≤routedGv s ∧ routedGv s≤cB) := by
  rcases h with ⟨hfl,hfh,hgl,hgh,hzl,hzh,hvl,hvh,hwl,hwh⟩
  unfold routedF routedG routedFv routedGv
  cases swapControl s <;> simp_all

/-- A strict twice-magnitude fit discharges both signed-kernel obligations. -/
theorem rowValue_fits (q c : Bool) (A B K : Int) (w : Nat)
    (hA : -K≤A ∧ A≤K) (hB : -K≤B ∧ B≤K)
    (hfit : 2*K<((2^(w-1):Nat):Int)) :
    (-((2^(w-1):Nat):Int)≤(if q then -B else B) ∧
      (if q then -B else B)<((2^(w-1):Nat):Int)) ∧
    -((2^(w-1):Nat):Int)≤rowValue q c A B ∧ rowValue q c A B<((2^(w-1):Nat):Int) := by
  obtain ⟨⟨hl,hh⟩,hvl,hvh⟩ := rowValue_bounds q c A B K hA hB
  constructor
  · constructor <;> omega
  · constructor <;> omega

end ECDSAAdd.Divsteps
