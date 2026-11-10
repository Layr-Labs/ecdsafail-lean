import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAProgramBool
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
namespace ParkAChain
open ECDSAAdd ZeroReadDevelop

/-- Opaque exact one-host output equalities, with each output passed to the next host. -/
inductive Steps : List Wire → Program → Program → Prop
 | nil (p : Program) : Steps [] p p
 | cons (q : Wire) (qs : List Wire) (p r t : Program)
     (head : (compileChunked? q p).map (fun c => c.out)=some r)
     (tail : Steps qs r t) : Steps (q::qs) p t

set_option linter.unnecessarySimpa false in
theorem outputs (qs : List Wire) (p t : Program) (h : Steps qs p t) :
 (compileManyChunked? qs p).map (fun c => c.out)=some t := by
 induction h with
 | nil p => rfl
 | cons q qs p r t head tail ih =>
   rw [compileManyChunked?]
   cases hc : compileChunked? q p with
   | none => simp [hc] at head
   | some first =>
     have e : first.out=r := by simpa [hc] using head
     subst r
     cases hr : compileManyChunked? qs first.out <;>
       simpa [hc,hr,Option.map,Option.bind] using ih

theorem isSome (qs : List Wire) (p t : Program) (h : Steps qs p t) :
 (compileManyChunked? qs p).isSome=true := by
 have out := outputs qs p t h
 cases he : compileManyChunked? qs p with
 | none => simp [he] at out
 | some r => rfl

#print axioms outputs
#print axioms isSome
end ParkAChain

namespace ParkAChain
open ECDSAAdd ZeroReadDevelop
 theorem extend_isSome {qs rs : List Wire} {p t : Program}
 (h:ParkAChain.Steps qs p t) (htail:(compileManyChunked? rs t).isSome=true) :
 (compileManyChunked? (qs++rs) p).isSome=true := by
 induction h with
 | nil => exact htail
 | cons q qs p r t head tail ih =>
   have rest:=ih htail
   rw [List.cons_append,compileManyChunked?]
   cases hc:compileChunked? q p with
   | none => simp [hc] at head
   | some first =>
     have eq:first.out=r := by simpa [hc] using head
     subst r
     cases hr:compileManyChunked? (qs++rs) first.out with
     | none => simp [hr] at rest
     | some last => simp [hr,Option.bind]

end ParkAChain
