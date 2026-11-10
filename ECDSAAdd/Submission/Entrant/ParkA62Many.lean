import ECDSAAdd.Submission.Entrant.ParkA62ManyBase
import ECDSAAdd.Submission.Entrant.ParkA62StagedProof

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ParkA62Many
open InverseCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option Elab.async false
 theorem actual_compiled:
 (compileManyChunked? (loans Baselines.layout.dialogStreamedSquareWide)
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).isSome=true:=
 ParkA62StagedProof.actual_compiled
#print axioms actual_compiled
end ParkA62Many

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ParkA62Many
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount

theorem gain_of_success (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (ready:BankReady L g (loans L)) (success:(compileManyChunked? (loans L) (aMiddle L g)).isSome=true):
 toffoliCount (aFoldSelected L g)+62≤toffoliCount (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 rw[dif_pos ready]
 cases he:compileManyChunked? (loans L) (aMiddle L g) with
 | none=>simp[he]at success
 | some cm=>exact (aFoldManyZ_resources 62 L hw g (loans L) cm.out (by decide) ready.1 ready.2.2.2 cm.proof).1

theorem actual_fold_gain:
 toffoliCount (aFoldSelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)+62≤
 toffoliCount (aFoldTriple Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic):=
 gain_of_success _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _ actual_ready actual_compiled

theorem body_gain (L:CuccaroStreamedSquareWideLayout) (g:Wire)
 (h:toffoliCount (aFoldSelected L g)+62≤toffoliCount (aFoldTriple L g)):
 toffoliCount (aBodySelected L g)+62≤toffoliCount (aBodyTriple L g):=by
 simp only[aBodySelected,aBodyTriple,toffoliCount_append]
 omega

theorem bound2853 (a b:Nat) (h:a+62≤b) (hb:b=2915):a≤2853:=by omega

theorem actual_body_T_le:
 toffoliCount (aBodySelected Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)≤2853:=
 bound2853 _ _ (body_gain _ _ actual_fold_gain)
  (aBodyTriple_counts _ (ControlledPointLayout.dialogStreamedSquareWide_widths Baselines.layout Baselines.layout_widths) _).1
#print axioms actual_fold_gain
#print axioms actual_body_T_le
end ParkA62Many

end
