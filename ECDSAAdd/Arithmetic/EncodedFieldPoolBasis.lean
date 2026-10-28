import ECDSAAdd.Arithmetic.RunPoolBasisAgreement
import ECDSAAdd.Arithmetic.DirectSkywalkCleanup
namespace ECDSAAdd.Arithmetic
open DirectSkywalk
attribute [local irreducible] run wires

/-- Generic field-frame locality keeps concrete encoder and register
definitions out of kernel checking of the composed caller comparison. -/
theorem encoded_field_pool_basis (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (encoder : Program) (support : wires encoder⊆(skywalkPoolWires w).toFinset)
    (origin : BasisState) (ha : regValue (skywalkSharedField w).a origin=0)
    (X : Nat) (raw s : State)
    (frame : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a origin X 0 raw.basis)
    (encoded : s=run encoder [] raw) :
    ∀q∈skywalkPoolWires w,s.basis q=
      (run encoder [] ({phase:=false,basis:=origin} : State)).basis q := by
  have keeps := arith_field_frame (skywalkSharedField w) origin raw.basis X ha frame
  have rawPool : ∀q∈skywalkPoolWires w,raw.basis q=origin q := by
    intro q hq
    exact keeps q (arith_pool_away_z w hn q hq)
  let ref : State := {phase:=false,basis:=origin}
  rw [encoded]
  intro q hq
  exact run_pool_basis_agreement encoder (skywalkPoolWires w).toFinset support raw ref []
    (fun k hk => rawPool k (List.mem_toFinset.mp hk)) q (List.mem_toFinset.mpr hq)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.encoded_field_pool_basis
