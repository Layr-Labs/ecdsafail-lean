import ECDSAAdd.Arithmetic.Divsteps.SignedDouble
import ECDSAAdd.Math.Divsteps.RowBounds
import ECDSAAdd.Math.Divsteps.Reverse

namespace ECDSAAdd.Divsteps

def activeControl (s : ZState) : Bool := decide (s.g≠0)

theorem doubled_routed_fv (s : ZState) :
    (if activeControl s then 2*routedFv s else routedFv s)=(zSlot s).fv := by
  by_cases hg : s.g=0
  · simp [activeControl,routedFv,swapControl,zSlot,hg]
  · by_cases hswap : 0≤s.z ∧ s.g%2=1
    all_goals simp [activeControl,routedFv,swapControl,zSlot,zStep,hg,hswap]

/-- The integer target and second coefficient already stay frozen at g=0;
only the first coefficient's doubling and the counter need active control. -/
theorem target_rows_frozen (s : ZState) :
    (zStep s).g=(zSlot s).g ∧ (zStep s).gv=(zSlot s).gv ∧
    routedF s=(zSlot s).f := by
  by_cases hg : s.g=0
  · simp [zSlot,zStep,routedF,swapControl,hg]
  · by_cases hswap : 0≤s.z ∧ s.g%2=1
    all_goals simp [zSlot,zStep,routedF,swapControl,hg,hswap]

end ECDSAAdd.Divsteps

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- The in-place, scratch-free signed double realizes the first coefficient
update, including frozen states, from the same conservative state invariant. -/
theorem doubleRow_zSlot (active low sign : Wire) (mid : List Wire)
    (hn : (active::low::(mid++[sign])).Nodup)
    (st : ZState) (pB zB cB : Int) (hbound : Bounds pB zB cB st)
    (hfit : 2*cB<((2^(mid.length+1):Nat):Int))
    (s : ECDSAAdd.State) (m : List Bool)
    (hc : s.basis active=activeControl st)
    (hv : signedRegValue (low::(mid++[sign])) s.basis=routedFv st) :
    (run (doubleSigned active low sign mid) m s).phase=s.phase ∧
    (∀ w, w∉low::(mid++[sign]) →
      (run (doubleSigned active low sign mid) m s).basis w=s.basis w) ∧
    signedRegValue (low::(mid++[sign]))
      (run (doubleSigned active low sign mid) m s).basis=(zSlot st).fv := by
  have hr := (routed_rows_bounds hbound).2.2.1
  have hcap : s.basis active=true →
      -((2^(mid.length+1):Nat):Int)≤2*signedRegValue (low::(mid++[sign])) s.basis ∧
      2*signedRegValue (low::(mid++[sign])) s.basis<((2^(mid.length+1):Nat):Int) := by
    intro _
    rw [hv]
    constructor <;> omega
  obtain ⟨hp,hframe,hvalue⟩ := doubleSigned_correct active low sign mid hn s m hcap
  rw [hc,hv] at hvalue
  exact ⟨hp,hframe,hvalue.trans (doubled_routed_fv st)⟩

end ECDSAAdd.Arithmetic.Divsteps
