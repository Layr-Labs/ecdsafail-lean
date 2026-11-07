import ECDSAAdd.Submission.Entrant.CompareDecoder.BitColumns
set_option autoImplicit false
namespace ECDSAAdd.Entrant.CompareDecoder
open DirectDecoder
theorem low_checked (x : Nat) (bound : x<32768) (h : valid x=true) (i : Fin 7) :
 evalPoly (comparePolys.getD i.val []) (compareVars x)=(lowRs x).getD (i.val+6) false :=
 CertificateBits.low_checked x bound h i
#print axioms low_checked
end ECDSAAdd.Entrant.CompareDecoder
