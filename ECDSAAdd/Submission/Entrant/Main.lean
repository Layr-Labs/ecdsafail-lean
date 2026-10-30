import ECDSAAdd.Submission.Entrant.OneFlag
import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Framework.GateInverse
import Mathlib.Tactic
import ECDSAAdd.Arithmetic.MappedAdder
import ECDSAAdd.Arithmetic.BalancedFoldMath
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Baselines.SlotSignedSquare
import ECDSAAdd.Arithmetic.CompactWalkPhysical
import ECDSAAdd.Baselines.SlotNativeFirst
import ECDSAAdd.Baselines.SlotSignedInteger

section FrontierDH

section
-- Verified component DHDefinitions
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnSharedDH

def flipIf (v : Bool) (w : Wire) : Program := if v then [.X w] else []

/-- `d ^= enD ∧ c ∧ f ∧ ¬g ∧ [xk = cx] ∧ [y0 = cy]` and `h ^= enH ∧ c ∧ f ∧ ¬g ∧ [xk ≠ cx]`,
with clean ancillas `a1 a2 a3` (restored). Self-inverse, measurement-free. -/
def gadget (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) : Program :=
  [.CCX c f a1, .X g, .CCX a1 g a2, .X g] ++
  ((if enD then
     flipIf (!cx) xk ++ [.CCX a2 xk a3] ++ flipIf (!cx) xk ++
     flipIf (!cy) y0 ++ [.CCX a3 y0 d] ++ flipIf (!cy) y0 ++
     (if enH then [.CX a2 h, .CX a3 h] else []) ++
     flipIf (!cx) xk ++ [.measureX a3 [] [.CZ a2 xk]] ++ flipIf (!cx) xk
   else []) ++
  ((if enH && !enD then flipIf cx xk ++ [.CCX a2 xk h] ++ flipIf cx xk else []) ++
  [.X g, .measureX a2 [] [.CZ a1 g], .X g, .measureX a1 [] [.CZ c f]]))

end OwnSharedDH
end ECDSAAdd.Entrant

end

section
-- Verified component AndPrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 theorem erase (t a b : Wire) (x : Bool) (s : State) (ha:a≠t) (hb:b≠t)
  (h:s.basis t=(s.basis a && s.basis b)) :
  measureAndCorrect t [] [.CZ a b] x s=⟨s.phase,writeBit s.basis t false⟩ := by
  obtain ⟨ph,bs⟩:=s
  simp only at h
  cases x <;> simp [measureAndCorrect,correct,writeBit,Function.update_apply,ha,hb,h]
 def clearMatch (a x t : Wire) (cx : Bool) : Program :=
  flipIf (!cx) x ++ [.measureX t [] [.CZ a x]] ++ flipIf (!cx) x
 def computeMatch (a x t : Wire) (cx : Bool) : Program :=
  flipIf (!cx) x ++ [.CCX a x t] ++ flipIf (!cx) x
 theorem compute_match (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (zero:s.basis t=false) :
  run (computeMatch a x t cx) m s=
    ⟨s.phase,writeBit s.basis t (s.basis a && (s.basis x==cx))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      by_cases qt:q=t
      · subst q
        simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
      · by_cases qx:q=x
        · subst q
          simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
        · simp [computeMatch,flipIf,run,writeBit,Function.update_apply,qt,qx,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      simp [computeMatch,flipIf,run,writeBit,zero]
 theorem compute_toggle (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) :
  run (computeMatch a x t cx) m s=
    ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && (s.basis x==cx)))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      by_cases qt:q=t
      · subst q
        simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt]
      · by_cases qx:q=x
        · subst q
          simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt]
        · simp [computeMatch,flipIf,run,writeBit,Function.update_apply,qt,qx,ax,ant,xt,Ne.symm ant,Ne.symm xt]
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      simp [computeMatch,flipIf,run,writeBit]
 theorem clear_match (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (clearMatch a x t cx) m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · let v : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
    have vt : v.basis t=(v.basis a && v.basis x) := by
     simp [v,writeBit,Function.update_apply,ant,xt,ax,Ne.symm xt] at value ⊢
     exact value
    have e:=erase t a x (m.headD false) v ant xt vt
    simp only [clearMatch,flipIf,Bool.not_false,if_true,List.cons_append,List.nil_append,run]
    rw [show {phase:=s.phase,basis:=writeBit s.basis x (!s.basis x)}=v by rfl,e]
    apply State.extensionality
    · rfl
    · funext q
      by_cases qt:q=t
      · subst q;simp [v,writeBit,Function.update_apply,Ne.symm xt]
      · by_cases qx:q=x
        · subst q;simp [v,writeBit,Function.update_apply,xt]
        · simp [v,writeBit,Function.update_apply,qt,qx]
  · have e:=erase t a x (m.headD false) s ant xt (by simpa using value)
    simpa [clearMatch,flipIf,run] using e
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component SharedWindow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def hShared (a t h : Wire) : Program := [.CX a h,.CX t h]
 def hOld (a x h : Wire) (cx : Bool) : Program := flipIf cx x ++ [.CCX a x h] ++ flipIf cx x
 theorem h_eq (a x t h : Wire) (cx : Bool) (hn:[a,x,t,h].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (hShared a t h) m s=run (hOld a x h cx) m s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant,ah⟩,⟨xt,xh⟩,th,_⟩:=hn
  cases cx <;> apply State.extensionality
  all_goals try simp [hShared,hOld,flipIf,run]
  all_goals
   funext q
   by_cases qh:q=h
   · subst q
     simp only [hShared,hOld,flipIf,Bool.false_eq_true,if_false,if_true,List.nil_append,List.append_nil,
       List.cons_append,run,writeBit,Function.update_self,Function.update_of_ne (Ne.symm th),Function.update_of_ne (Ne.symm ah)]
     simp [writeBit,Function.update_apply,ax,ant,ah,xt,xh,th,Ne.symm xh,Ne.symm ax,value]
     all_goals cases s.basis a <;> cases s.basis x <;> rfl
   · by_cases qx:q=x
     · subst q
       simp [hShared,hOld,flipIf,run,writeBit,Function.update_apply,qh,xh,Ne.symm xh,ax,Ne.symm ax]
     · simp [hShared,hOld,flipIf,run,writeBit,Function.update_apply,qh,qx,xh,Ne.symm xh,ax,Ne.symm ax]
 theorem run_write_outside (p : Program) (port : Wire) (hp:port∉wires p)
  (s : State) (m : List Bool) (value : Bool) :
  run p m ⟨s.phase,writeBit s.basis port value⟩=
   ⟨(run p m s).phase,writeBit (run p m s).basis port value⟩ := by
  have h:=pool_run_agrees p (wires p) (Finset.Subset.refl _) m
    ⟨s.phase,writeBit s.basis port value⟩ s rfl (by
     intro q hq
     exact Function.update_of_ne (show q≠port from fun he=>hp (he ▸ hq)) _ _)
  apply State.extensionality
  · exact h.1
  funext q
  by_cases used:q∈wires p
  · change _=writeBit (run p m s).basis port value q
    rw [show writeBit (run p m s).basis port value q=(run p m s).basis q from
      Function.update_of_ne (show q≠port from fun he=>hp (he ▸ used)) _ _]
    exact h.2 q used
  · rw [run_preserves_outside p m _ q used]
    change writeBit s.basis port value q=writeBit (run p m s).basis port value q
    by_cases eq:q=port
    · subst q;simp [writeBit]
    · simp only [writeBit,Function.update_of_ne eq,run_preserves_outside p m s q used]
 theorem zero_records (P : Program) (h:measurementCount P=0) (s : State) (m n : List Bool) :
  run P m s=run P n s := by
  rw [←run_take P m s,←run_take P n s,h]
  rfl
 theorem window_eq (a x t h : Wire) (cx : Bool) (hn:[a,x,t,h].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (hShared a t h++clearMatch a x t cx) m s=
   run (clearMatch a x t cx++hOld a x h cx) m s := by
  have nd3 : [a,x,t].Nodup := List.Nodup.of_append_left (show ([a,x,t]++[h]).Nodup from hn)
  have facts:=hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
  obtain ⟨⟨ax,ant,ah⟩,⟨xt,xh⟩,th,_⟩:=facts
  have keep (q : Wire) (qh:q=a∨q=x∨q=t) :
    (run (hShared a t h) m s).basis q=s.basis q := by
    simp only [hShared,run]
    rcases qh with rfl|rfl|rfl <;> simp [writeBit,Function.update_apply,ah,xh,th]
  have v : (run (hShared a t h) m s).basis t=
      ((run (hShared a t h) m s).basis a && ((run (hShared a t h) m s).basis x==cx)) := by
    rw [keep t (Or.inr (Or.inr rfl)),keep a (Or.inl rfl),keep x (Or.inr (Or.inl rfl))]
    exact value
  have hzero:measurementCount (hShared a t h)=0:=by simp [hShared,measurementCount]
  have oldzero:measurementCount (hOld a x h cx)=0:=by cases cx <;> simp [hOld,flipIf,measurementCount]
  have oldaway:t∉wires (hOld a x h cx) := by
    cases cx <;> simp [hOld,flipIf,wires,Instr.wires,Ne.symm ant,Ne.symm xt,th]
  rw [run_append,run_append,run_take (hShared a t h) m s,run_take (clearMatch a x t cx) m s,
    hzero,List.drop_zero,clear_match a x t cx nd3 _ m v,clear_match a x t cx nd3 s _ value]
  rw [zero_records _ oldzero _ _ m,run_write_outside _ _ oldaway]
  rw [h_eq a x t h cx hn s m value]
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component SharedGadget
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def prepPrefix (c f g a1 a2 : Wire) : Program := [.CCX c f a1,.X g,.CCX a1 g a2,.X g]
 def prepare (c f g d x y a1 a2 a3 : Wire) (cx cy : Bool) : Program :=
  prepPrefix c f g a1 a2 ++ (computeMatch a2 x a3 cx ++ computeMatch a3 y d cy)
 def tail (c f g a1 a2 : Wire) : Program := [.X g,.measureX a2 [] [.CZ a1 g],.X g,.measureX a1 [] [.CZ c f]]
 theorem new_shape (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool) :
  gadget c f g d h x y a1 a2 a3 true true cx cy=
   prepare c f g d x y a1 a2 a3 cx cy ++
    ((hShared a2 a3 h++clearMatch a2 x a3 cx)++tail c f g a1 a2) := by
  simp only [gadget,prepare,prepPrefix,tail,hShared,clearMatch,computeMatch,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,if_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
 theorem old_shape (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool) :
  DHGadget.gadget c f g d h x y a1 a2 a3 true true cx cy=
   prepare c f g d x y a1 a2 a3 cx cy ++
    ((clearMatch a2 x a3 cx++hOld a2 x h cx)++tail c f g a1 a2) := by
  simp only [DHGadget.gadget,prepare,prepPrefix,tail,hOld,clearMatch,computeMatch,flipIf,DHGadget.flipIf,
    if_true,List.append_assoc]
 theorem ready (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool) (z:s.basis a3=false) :
  (run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis a3=
   ((run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis a2 &&
    ((run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis x==cx)) := by
  have first:a3∉wires (prepPrefix c f g a1 a2) := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
   simp [prepPrefix,wires,Instr.wires]
   tauto
  have nd:[a2,x,a3].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndD:[a3,y,d].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ad:a3≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have a2d:a2≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have xd:x≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have a2a3:a2≠a3:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have xa3:x≠a3:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have pm:measurementCount (prepPrefix c f g a1 a2)=0:=by simp [prepPrefix,measurementCount]
  have cm:measurementCount (computeMatch a2 x a3 cx)=0:=by cases cx <;> simp [computeMatch,flipIf,measurementCount]
  let v:=run (prepPrefix c f g a1 a2) m s
  have zero:v.basis a3=false:=(run_preserves_outside _ _ _ _ first).trans z
  have cEq:=compute_match a2 x a3 cx nd v m zero
  let w:=run (computeMatch a2 x a3 cx) m v
  have dEq:=compute_toggle a3 y d cy ndD w m
  simp only [prepare,run_append,run_take,pm,cm,List.drop_zero]
  simp only [List.take_zero,zero_records _ pm s [] m,zero_records _ cm _ [] m]
  change (run (computeMatch a3 y d cy) m w).basis a3=
   ((run (computeMatch a3 y d cy) m w).basis a2 && ((run (computeMatch a3 y d cy) m w).basis x==cx))
  rw [dEq]
  simp only [writeBit,Function.update_of_ne ad,Function.update_of_ne a2d,Function.update_of_ne xd]
  change (run (computeMatch a2 x a3 cx) m v).basis a3=
   ((run (computeMatch a2 x a3 cx) m v).basis a2 && ((run (computeMatch a2 x a3 cx) m v).basis x==cx))
  rw [cEq]
  simp [writeBit,Function.update_apply,a2a3,xa3]
 theorem context_congr (P A B Q : Program) (s : State) (m : List Bool)
  (mc:measurementCount A=measurementCount B)
  (eq:∀n,run A n (run P (m.take (measurementCount P)) s)=run B n (run P (m.take (measurementCount P)) s)) :
  run (P++(A++Q)) m s=run (P++(B++Q)) m s := by
  simp only [run_append]
  rw [mc,eq]
 theorem gadget_eq (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z:s.basis a3=false) :
  run (gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s=
   run (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s := by
  cases enD <;> cases enH
  · rfl
  · rfl
  · simp only [gadget,DHGadget.gadget,flipIf,DHGadget.flipIf,if_true,if_false,Bool.not_false,Bool.false_and,Bool.false_eq_true,List.append_nil]
  · rw [new_shape,old_shape]
    apply context_congr
    · cases cx <;> simp [hShared,hOld,clearMatch,flipIf,measurementCount]
    · intro n
      have nd:[a2,x,a3,h].Nodup := by
       simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
      exact window_eq a2 x a3 h cx nd _ n (ready c f g d h x y a1 a2 a3 cx cy hn s _ z)
 theorem gadget_run_fast (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) (z3:s.basis a3=false) :
  run (gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s=⟨s.phase,fun q=>
   if q=d then s.basis d ^^ (enD && s.basis c && s.basis f && !s.basis g && (s.basis x==cx) && (s.basis y==cy))
   else if q=h then s.basis h ^^ (enH && s.basis c && s.basis f && !s.basis g && (s.basis x != cx))
   else s.basis q⟩ := by
  rw [gadget_eq c f g d h x y a1 a2 a3 enD enH cx cy hn s m z3]
  exact DHGadget.gadget_run c f g d h x y a1 a2 a3 enD enH cx cy hn s m z1 z2 z3
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component MeasuredDefinitions
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnMeasuredDH
open DHGadget
def gadgetM (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) : Program :=
  [.CCX c f a1, .X g, .CCX a1 g a2, .X g] ++
  ((if enD then
     flipIf (!cx) xk ++ [.CCX a2 xk a3] ++ flipIf (!cx) xk ++
     flipIf (!cy) y0 ++ [.measureX d [] [.CZ a3 y0]] ++ flipIf (!cy) y0 ++
     flipIf (!cx) xk ++ [.measureX a3 [] [.CZ a2 xk]] ++ flipIf (!cx) xk
   else []) ++
  ((if enH then flipIf cx xk ++ [.measureX h [] [.CZ a2 xk]] ++ flipIf cx xk else []) ++
  [.X g, .measureX a2 [] [.CZ a1 g], .X g, .measureX a1 [] [.CZ c f]]))


end OwnMeasuredDH
end ECDSAAdd.Entrant

end

section
-- Verified component PrefixState
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 theorem prefix_run (c f g a1 a2 : Wire) (hn:[c,f,g,a1,a2].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) :
  run (prepPrefix c f g a1 a2) m s=⟨s.phase,
   writeBit (writeBit s.basis a1 (s.basis c && s.basis f)) a2 (s.basis c && s.basis f && !s.basis g)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨cf,cg,ca1,ca2⟩,⟨fg,fa1,fa2⟩,⟨ga1,ga2⟩,a12,_⟩:=hn
  apply State.extensionality
  · simp [prepPrefix,run]
  · funext q
    by_cases qa1:q=a1
    · subst q
      simp [prepPrefix,run,writeBit,Function.update_apply,ca1,ca2,fa1,fa2,ga1,ga2,a12,
       Ne.symm ca1,Ne.symm ca2,Ne.symm fa1,Ne.symm fa2,Ne.symm ga1,Ne.symm ga2,Ne.symm a12,z1,z2]
    · by_cases qa2:q=a2
      · subst q
        simp [prepPrefix,run,writeBit,Function.update_apply,ca1,ca2,fa1,fa2,ga1,ga2,a12,
         Ne.symm ca1,Ne.symm ca2,Ne.symm fa1,Ne.symm fa2,Ne.symm ga1,Ne.symm ga2,Ne.symm a12,z1,z2]
      · by_cases qg:q=g
        · subst q
          simp [prepPrefix,run,writeBit,Function.update_apply,qa1,qa2,ga1,ga2]
        · simp [prepPrefix,run,writeBit,Function.update_apply,qa1,qa2,qg,ga1,ga2,Ne.symm ga2]
 theorem bne_match (x cx : Bool) : (x != cx)=(x==!cx) := by
  cases x <;> cases cx <;> rfl
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component ConditionalStages
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def clearIf (en : Bool) (a x t : Wire) (cx : Bool) : Program := if en then clearMatch a x t cx else []
 theorem clear_if (en : Bool) (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(en && s.basis a && (s.basis x==cx))) :
  run (clearIf en a x t cx) m s=⟨s.phase,writeBit s.basis t false⟩ := by
  cases en
  · simp only [Bool.false_and] at value
    apply State.extensionality
    · rfl
    · funext q
      simp only [clearIf,Bool.false_eq_true,if_false,run]
      by_cases qt:q=t
      · subst q;simp [writeBit,value]
      · simp [writeBit,Function.update_apply,qt]
  · exact clear_match a x t cx hn s m (by simpa using value)
 def dStage (en : Bool) (a x y t d : Wire) (cx cy : Bool) : Program :=
  if en then computeMatch a x t cx ++ (clearMatch t y d cy ++ clearMatch a x t cx) else []
 theorem d_stage (en : Bool) (a x y t d : Wire) (cx cy : Bool) (hn:[a,x,y,t,d].Nodup)
  (s : State) (m : List Bool) (zero:s.basis t=false)
  (value:s.basis d=(en && s.basis a && (s.basis x==cx) && (s.basis y==cy))) :
  run (dStage en a x y t d cx cy) m s=⟨s.phase,writeBit s.basis d false⟩ := by
  cases en
  · simp only [Bool.false_and] at value
    apply State.extensionality
    · rfl
    · funext q
      simp only [dStage,Bool.false_eq_true,if_false,run]
      by_cases qd:q=d
      · subst q;simp [writeBit,value]
      · simp [writeBit,Function.update_apply,qd]
  · simp only [Bool.true_and] at value
    have ndC:[a,x,t].Nodup := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
    have ndD:[t,y,d].Nodup := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
    have facts:=hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
    obtain ⟨⟨ax,ay,ant,ad⟩,⟨xy,xt,xd⟩,⟨yt,yd⟩,td,_⟩:=facts
    let w : State:=⟨s.phase,writeBit s.basis t (s.basis a && (s.basis x==cx))⟩
    let u : State:=⟨w.phase,writeBit w.basis d false⟩
    have ce (n : List Bool) : run (computeMatch a x t cx) n s=w := compute_match a x t cx ndC s n zero
    have wd : w.basis d=(w.basis t && (w.basis y==cy)) := by
      simpa only [w,writeBit,Function.update_of_ne (Ne.symm td),Function.update_self,Function.update_of_ne yt] using value
    have de (n : List Bool) : run (clearMatch t y d cy) n w=u := clear_match t y d cy ndD w n wd
    have ut : u.basis t=(u.basis a && (u.basis x==cx)) := by
      simp only [u,w,writeBit,Function.update_of_ne td,Function.update_of_ne ad,
       Function.update_of_ne xd,Function.update_self,Function.update_of_ne ant,Function.update_of_ne xt]
    have ae (n : List Bool) : run (clearMatch a x t cx) n u=⟨u.phase,writeBit u.basis t false⟩ :=
      clear_match a x t cx ndC u n ut
    simp only [dStage,if_true,run_append,ce,de,ae]
    apply State.extensionality
    · rfl
    · funext q
      by_cases qt:q=t
      · subst q;simp [u,w,writeBit,Function.update_apply,td,zero]
      · by_cases qd:q=d
        · subst q;simp [u,w,writeBit,Function.update_apply,qt]
        · simp [u,w,writeBit,Function.update_apply,qt,qd]
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component MeasuredGadget
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnMeasuredDH
open Arithmetic OwnSharedDH
 theorem shape (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  gadgetM c f g d h x y a1 a2 a3 enD enH cx cy=
   prepPrefix c f g a1 a2 ++ (dStage enD a2 x y a3 d cx cy ++
    (clearIf enH a2 x h (!cx) ++ (clearMatch a1 g a2 false ++ clearMatch c f a1 true))) := by
  simp only [gadgetM,prepPrefix,dStage,clearIf,computeMatch,clearMatch,flipIf,DHGadget.flipIf,
   Bool.not_not,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
   List.nil_append,List.append_nil,List.append_assoc,List.cons_append]
 theorem gadgetM_run_fast (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) (z3:s.basis a3=false)
  (hd:s.basis d=(enD && s.basis c && s.basis f && !s.basis g && (s.basis x==cx) && (s.basis y==cy)))
  (hh:s.basis h=(enH && s.basis c && s.basis f && !s.basis g && (s.basis x != cx))) :
  run (gadgetM c f g d h x y a1 a2 a3 enD enH cx cy) m s=⟨s.phase,fun q=>
   if q=d then false else if q=h then false else s.basis q⟩ := by
  have ndP:[c,f,g,a1,a2].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndD:[a2,x,y,a3,d].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndH:[a2,x,h].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndA2:[a1,g,a2].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndA1:[c,f,a1].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have facts:=hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
  obtain ⟨⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩,⟨m1,m2,m3,m4,m5,m6,m7,m8⟩,⟨k1,k2,k3,k4,k5,k6,k7⟩,
    ⟨l1,l2,l3,l4,l5,l6⟩,⟨p1,p2,p3,p4,p5⟩,⟨q1,q2,q3,q4⟩,⟨r1,r2,r3⟩,⟨t1,t2⟩,t3,_⟩:=facts
  let v : State:=⟨s.phase,writeBit (writeBit s.basis a1 (s.basis c && s.basis f)) a2
    (s.basis c && s.basis f && !s.basis g)⟩
  let u : State:=⟨v.phase,writeBit v.basis d false⟩
  let k : State:=⟨u.phase,writeBit u.basis h false⟩
  let l : State:=⟨k.phase,writeBit k.basis a2 false⟩
  have pe (n : List Bool) : run (prepPrefix c f g a1 a2) n s=v := prefix_run c f g a1 a2 ndP s n z1 z2
  have vz : v.basis a3=false := by
   simp [v,writeBit,Function.update_apply,Ne.symm t2,Ne.symm t3,z3]
  have vd : v.basis d=(enD && v.basis a2 && (v.basis x==cx) && (v.basis y==cy)) := by
   simpa [v,writeBit,Function.update_apply,p3,p4,m6,m7,k5,k6,Bool.and_assoc] using hd
  have de (n : List Bool) : run (dStage enD a2 x y a3 d cx cy) n v=u :=
   d_stage enD a2 x y a3 d cx cy ndD v n vz vd
  have uh : u.basis h=(enH && u.basis a2 && (u.basis x==!cx)) := by
   simpa [u,v,writeBit,Function.update_apply,r2,r1,m3,m4,m6,m7,Ne.symm p4,Ne.symm p2,k5,k6,r2,
    Bool.and_assoc,bne_match] using hh
  have he (n : List Bool) : run (clearIf enH a2 x h (!cx)) n u=k := clear_if enH a2 x h (!cx) ndH u n uh
  have ka2 : k.basis a2=(k.basis a1 && (k.basis g==false)) := by
   simp [k,u,v,writeBit,Function.update_apply,Ne.symm r2,Ne.symm p4,Ne.symm p3,Ne.symm r1,
    Ne.symm q2,Ne.symm q3,t1,q1,Ne.symm p1,q2,q3,Bool.and_assoc]
  have a2e (n : List Bool) : run (clearMatch a1 g a2 false) n k=l := clear_match a1 g a2 false ndA2 k n ka2
  have la1 : l.basis a1=(l.basis c && (l.basis f==true)) := by
   simp [l,k,u,v,writeBit,Function.update_apply,t1,Ne.symm r1,Ne.symm p3,l4,l5,n7,n8,n4,n6,
    Ne.symm t1,l3,l1,Bool.and_assoc]
  have a1e (n : List Bool) : run (clearMatch c f a1 true) n l=⟨l.phase,writeBit l.basis a1 false⟩ :=
   clear_match c f a1 true ndA1 l n la1
  simp only [shape,run_append,pe,de,he,a2e,a1e]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qd:q=d
    · subst q;simp [l,k,u,v,writeBit,Function.update_apply,p3,p4,p2]
    · by_cases qh:q=h
      · subst q;simp [l,k,u,v,writeBit,Function.update_apply,r1,r2]
      · by_cases qa1:q=a1
        · subst q;simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,z1]
        · by_cases qa2:q=a2
          · subst q;simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,qa1,z2]
          · simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,qa1,qa2]
end ECDSAAdd.Entrant.OwnMeasuredDH

end

section
-- Verified component CompleteProperties
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnSharedDH
set_option maxHeartbeats 4000000 in
theorem gadget_wires (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) (q : Wire)
    (hq : q ∈ wires (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy)) :
    q = c ∨ q = f ∨ q = g ∨ q = d ∨ q = h ∨ q = xk ∨ q = y0 ∨ q = a1 ∨ q = a2 ∨ q = a3 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, wires, Instr.wires, correctionWires] at hq <;> tauto

theorem gadget_counts (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 4 ∧
    measurementCount (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 3 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, toffoliCount, measurementCount]

theorem gadget_gateSlots (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    Challenge.gateSlots (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 33 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, Challenge.gateSlots, Challenge.instructionSlots]

theorem gadget_physical (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) :
    GatePhysical (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  intro i hi
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf] at hi <;> rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [RecordedQuantum.PhysicalInstr, ProperGate, eq_comm]


end OwnSharedDH
namespace OwnMeasuredDH
open DHGadget
/-- When the gadget only clears `d` and `h`, the measured variant has the same run. -/
theorem gadgetM_eq (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
    (z1 : s.basis a1 = false) (z2 : s.basis a2 = false) (z3 : s.basis a3 = false)
    (hd : (s.basis d ^^ (enD && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk == cx) && (s.basis y0 == cy))) = false)
    (hh : (s.basis h ^^ (enH && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk != cx))) = false) :
    run (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s =
      run (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s := by
  have hd' : s.basis d = (enD && s.basis c && s.basis f && !s.basis g &&
      (s.basis xk == cx) && (s.basis y0 == cy)) := by
    revert hd; cases s.basis d <;> simp
  have hh' : s.basis h = (enH && s.basis c && s.basis f && !s.basis g && (s.basis xk != cx)) := by
    revert hh; cases s.basis h <;> simp
  rw [gadgetM_run_fast c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3 hd' hh',
    gadget_run c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3]
  congr 1
  funext q
  split_ifs
  · exact hd.symm
  · exact hh.symm
  · rfl

theorem gadgetM_wires (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) (q : Wire)
    (hq : q ∈ wires (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy)) :
    q ∈ wires (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, gadget, flipIf, wires, Instr.wires, correctionWires] at hq ⊢ <;> tauto

theorem gadgetM_counts (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 3 ∧
    measurementCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 5 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf, toffoliCount, measurementCount]

theorem gadgetM_gateSlots (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    Challenge.gateSlots (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 35 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf, Challenge.gateSlots, Challenge.instructionSlots]

theorem gadgetM_physical (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) :
    GatePhysical (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  intro i hi
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf] at hi <;> rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [RecordedQuantum.PhysicalInstr, ProperGate, eq_comm]


end OwnMeasuredDH
namespace OwnDHComposition
 theorem combined_budget (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (OwnMeasuredDH.gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) +
    toffoliCount (OwnSharedDH.gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 7 :=
  Nat.add_le_add (OwnMeasuredDH.gadgetM_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
    (OwnSharedDH.gadget_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
 theorem exact_active_costs (c f g d h xk y0 a1 a2 a3 : Wire) (cx cy : Bool) :
    toffoliCount (OwnMeasuredDH.gadgetM c f g d h xk y0 a1 a2 a3 true true cx cy)=3 ∧
    toffoliCount (OwnSharedDH.gadget c f g d h xk y0 a1 a2 a3 true true cx cy)=4 := by
  cases cx <;> cases cy <;> simp [OwnMeasuredDH.gadgetM, DHGadget.flipIf,
    OwnSharedDH.gadget,OwnSharedDH.flipIf,toffoliCount]
end OwnDHComposition
end ECDSAAdd.Entrant

end

section
-- Verified component Callers
open ECDSAAdd ECDSAAdd.Entrant
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
attribute [local irreducible] run wires
 def clrClear (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  OwnMeasuredDH.gadgetM L.control L.point.finite L.genericSelect L.doubleSelect L.core.equalNegY
    (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1) (L.core.poolWire 2)
    (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C)
 def clrRestore (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  OwnSharedDH.gadget L.control L.point.finite L.genericSelect L.doubleSelect L.core.equalNegY
    (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1) (L.core.poolWire 2)
    (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C)
section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem clrClear_flag (C : Point) (cy : Fp) (R : Point) (b D G H : Bool)
    (hD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))))
    (hH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C)))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrClear L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false false G false false false false)) := by
  intro s m v
  have post := clrDH_flag L hw hn C cy R b D G H false false hD hH s m v
  have nd := dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C)
  have pool3 : ∀ i, i < 3 → s.basis (L.core.poolWire i) = false := by
    intro i hi
    apply (regValue_zero _ _).mp v.clean
    have mem : L.core.poolWire i ∈ L.dialogPool.take 3 := by
      rw [pool_block L hw 3 (by omega)]
      exact List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩
    exact List.mem_of_mem_take mem
  have hrun := DHGadget.gadget_run L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega))
  have hr' := dialogFlagState_read L hn false false G false false false false
  have outD := (post.2.flags L.doubleSelect (by simp [inPlaceFlags])).trans hr'.2.1
  have outH := (post.2.flags L.core.equalNegY (by simp [inPlaceFlags])).trans hr'.2.2.2.2.2.1
  have dg : L.doubleSelect ≠ L.core.equalNegY := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
    exact nd.2.2.2.2.1.2.1
  change (run (DHGadget.gadget _ _ _ _ _ _ _ _ _ _ _ _ _ _) m s).basis _ = _ at outD outH
  rw [hrun] at outD outH
  simp only [if_true, if_neg (Ne.symm dg)] at outD outH
  have heq := OwnMeasuredDH.gadgetM_eq L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega)) outD outH
  unfold clrClear
  rw [heq]
  exact post

theorem clrRestore_flag (C : Point) (cy : Fp) (R : Point) (b D G H D' H' : Bool)
    (hD : D' = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))))
    (hH : H' = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C)))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrRestore L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false)) := by
  intro s m v
  have nd:=dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C)
  have zero:s.basis (L.core.poolWire 2)=false := by
   apply (regValue_zero _ _).mp v.clean
   apply List.mem_of_mem_take (i:=3)
   rw [pool_block L hw 3 (by omega)]
   exact List.mem_map.mpr ⟨2,List.mem_range'_1.mpr ⟨by omega,by omega⟩,rfl⟩
  have eq:=OwnSharedDH.gadget_eq L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m zero
  have old:=clrDH_flag L hw hn C cy R b D G H D' H' hD hH s m v
  unfold clrRestore
  rw [eq]
  exact old
end
end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component WholeSemantics
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum Edges
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires
def finiteProgram (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  inputClass L C cy ++
  genFlagN L ++ clrClear L C cy ++
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
  clrRestore L C cy ++ mergeFlagsN L ++
  renameProgram (sigP L) (corners2 L C ++ Edges.shared L C) ++
  chainErase L.control L.point.finite L.genericSelect

private theorem dh3_10_equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgram L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,dh3_10_equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,dh3_10_equal_simp]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,dh3_10_equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,dh3_10_equal_simp]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,dh3_10_equal_simp]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have hI1 : (((G ^^ (b && pointFinite R1)) ^^ D) ^^ H) = I := by
    rw [hR1fin, ← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := inputClass_flag L hw hn R C cy b false false false false false false false
  rw [hD,hI,hH,Bool.false_xor,Bool.false_xor,Bool.false_xor] at h3
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have cls := DHClass.classify hc b R
  dsimp only at cls
  have hKC : decide (cy≠-cy) = decide (C≠-C) := by
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact doubling_enabled_iff hc
  have clrD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))) := by
    rw [hKC]; simp only [D, G, C]; rw [← cls.1, Bool.xor_self]
  have clrH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    rw [hE]; simp only [H, G, C]; rw [← cls.2, Bool.xor_self]
  have hf1 := clrClear_flag L hw hn C cy R b D G H clrD clrH
  have read := dialogFlagState_read L hn false false G false false false false
  have h7 := genericD_ok L hw hn hc Gen hGen R b
    (dialogFlagState L false false G false false false false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2) read.2.2.2.2.2.1 read.2.1
  rw [read.2.2.1] at h7
  have resD : D = (false ^^ (decide (cy≠-cy) && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R1 == yBit C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [D, C]; rw [cls.1]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hKC, Bool.false_xor]; simp only [D, G, C]; exact cls.1
  have resH : H = (false ^^ (exceptionBit C && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [H, C]; rw [cls.2]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hE, Bool.false_xor]; simp only [H, G, C]; exact cls.2
  have hu := clrRestore_flag L hw hn C cy R1 b false G false D H resD resH
  have h9 := genFlagN_flag L hn R1 b false D G false false H false
  rw [hI1] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,dh3_10_equal_simp] using hf.2.2.2
  have h10 := Edges.shared_flag L hw hn S C b false D I O false H false
  have hdo : (b && pointEqual S (C+C))=D := by
    have hcy : decide (cy≠-cy)=true := by rw [cy_ne_neg hc]
    have hk : K=b := by simp [K,hcy]
    rw [←hk,hK]
    simpa only [dh3_10_equal_simp] using hf.2.1
  rw [heout,hdo,Bool.xor_self,Bool.xor_self] at h10
  simp only [dh3_10_equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have hout := park_triple L hw hn (Edges.outStage L C) R1 S b
    (dialogFlagState L false D I false false H false) (dialogFlagState L false false I false false false false)
    (dialogFlagState_read L hn false D I false false H false).2.2.2.1
    (dialogFlagState_read L hn false false I false false false false).2.2.2.1
    (by simpa only [Edges.outStage, List.append_assoc] using (h10a.seq h8).seq h10)
  have merge_run (s : State) (m : List Bool) :
      run (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ Edges.shared L C)) m s =
        run (genFlagN L ++ renameProgram (sigP L) (Edges.outStage L C)) m s := by
    have shape : genFlagN L ++ renameProgram (sigP L) (Edges.outStage L C) =
        (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) ++
          renameProgram (sigP L) (corners2 L C ++ Edges.shared L C) := by
      simp only [Edges.outStage,rename_append,sigP_zeroFlag L hw hn,List.append_assoc]
    rw [shape,run_append,run_take]
    rw [run_append (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)),run_take]
    simp only [show measurementCount (mergeFlagsN L)=0 from rfl,
      show measurementCount (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L))=0 from rfl,
      List.drop_zero]
    rw [mergeFlagsN_run_eq L hw hn s m]
  have hmerged : Triple (PointDialogBoundary L R1 b (dialogFlagState L false D G false false H false))
      (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ Edges.shared L C))
      (PointDialogBoundary L S b (dialogFlagState L false false I false false false false)) := by
    intro s m hs
    rw [merge_run]
    exact (h9.seq hout) s m hs
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← dh3_10_equal_simp]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := ((((((h3.seq h6).seq hf1).seq h7).seq hu).seq hmerged).seq h12)
  simpa only [finiteProgram,List.append_assoc,dialogFlagState_zero] using h


theorem Edges.shared_counts (L : ControlledPointLayout) (hw : L.Widths) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.shared L (.some hc))=258 ∧ measurementCount (Edges.shared L (.some hc))=256 := by
  have tc : tailCost true (yBit (.some hc)) (exceptionBit (.some hc)) (yBit (-((.some hc) : Point)))=1 := by
    rw [yBit_neg hc]
    cases yBit (.some hc) <;> cases exceptionBit (.some hc) <;> decide
  have hh := affineInputWith_counts (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
    (L.core.poolWire 513) true (yBit (.some hc)) (exceptionBit (.some hc))
    (yBit (-((.some hc) : Point))) (yBit ((.some hc)+(.some hc)))
    L.control (pairPorts L) (pairCode (.some hc)) (pairCode ((.some hc)+(.some hc)))
  simpa only [Edges.shared,pairPorts_length L hw,tc] using hh

theorem shared_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) : GatePhysical (Edges.shared L C) :=
  affineInputWith_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ (shared_nodup L hw hn)

theorem shared_wires (L : ControlledPointLayout) (hw : L.Widths) (C : Point) :
    wires (Edges.shared L C) ⊆ (L.control::yLow L::L.core.generic::L.core.equalNegY::L.doubleSelect::
      L.core.poolWire 513::(pairSrc L++L.dialogPool.take 256)).toFinset := by
  have pp := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  intro q hq
  have hh := affineInputWith_wires (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
    (L.core.poolWire 513) true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C))
    L.control (pairPorts L) (pairCode C) (pairCode (C+C)) hq
  simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
  rcases hh with h|h|h|h|h|h|h
  all_goals first | tauto | (have hm := pp.subset h; change _ at hm; tauto)

def wrapper (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram L C cy (renameProgram (Wrapper5.U L) Gen))

theorem wrapper_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (wrapper L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  intro s m hi
  have h := finite_spec L hw hn R hc b (renameProgram (Wrapper5.U L) Gen)
    (Wrapper5.genericOK_relabel L hw hc Gen hGen) s m hi
  unfold wrapper
  rw [Square5Placement.pool_relabel_state_eq L (Wrapper5.U L) (Wrapper5.U_pool L hw)
    (Wrapper5.U_outside L hw) _ s m hi.clean h.2.clean]
  exact h

end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component GadgetSubsets
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OwnDHSubsets
open Arithmetic
attribute [local irreducible] wires
 theorem shared_subset (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  wires (OwnSharedDH.gadget c f g d h x y a1 a2 a3 enD enH cx cy)⊆
   wires (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) := by
  intro q hq
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
   simp [OwnSharedDH.gadget,OwnSharedDH.flipIf,DHGadget.gadget,DHGadget.flipIf,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto
 theorem measured_subset (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  wires (OwnMeasuredDH.gadgetM c f g d h x y a1 a2 a3 enD enH cx cy)⊆
   wires (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) := by
  intro q hq
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
   simp [OwnMeasuredDH.gadgetM,DHGadget.gadget,DHGadget.flipIf,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto
end ECDSAAdd.Entrant.OwnDHSubsets

end

section
-- Verified component WrapperProperties
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires run toffoliCount measurementCount
theorem finite_counts (L : ControlledPointLayout) (hw : L.Widths) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (finiteProgram L (.some hc) cy Gen) ≤ 525+toffoliCount Gen ∧
    measurementCount (finiteProgram L (.some hc) cy Gen) ≤ 521+measurementCount Gen := by
  have inp := inputClass_counts L hw hc
  have out := Edges.shared_counts L hw hc
  have zero : toffoliCount (corners2 L (.some hc))=0 ∧ measurementCount (corners2 L (.some hc))=0 := by
    simp only [corners2,toffoliCount_append,measurementCount_append,
      (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2]; decide
  have clear : toffoliCount (clrClear L (.some hc) cy) ≤ 3 ∧ measurementCount (clrClear L (.some hc) cy) ≤ 5 :=
    OwnMeasuredDH.gadgetM_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have restore : toffoliCount (clrRestore L (.some hc) cy) ≤ 4 ∧ measurementCount (clrRestore L (.some hc) cy) ≤ 3 :=
    OwnSharedDH.gadget_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f1 : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have mf : toffoliCount (mergeFlagsN L) = 1 ∧ measurementCount (mergeFlagsN L) = 0 := by
    simp [mergeFlagsN, toffoliCount, measurementCount]
  simp only [finiteProgram,toffoliCount_append,measurementCount_append,renameProgram_counts,
    out.1,out.2,zero.1,zero.2]
  omega


theorem wrapper_counts (L : ControlledPointLayout) (hw:L.Widths) (Gen : Program) {cx cy : Fp}
 (hc:curve.toAffine.Nonsingular cx cy) :
 toffoliCount (wrapper L (.some hc) cy Gen)≤525+toffoliCount Gen ∧
 measurementCount (wrapper L (.some hc) cy Gen)≤521+measurementCount Gen := by
 simpa only [wrapper,renameProgram_counts] using finite_counts L hw (renameProgram (Wrapper5.U L) Gen) hc

theorem clear_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) :
 wires (clrClear L C cy)⊆wires (clrDH L C cy) := OwnDHSubsets.measured_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem restore_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) :
 wires (clrRestore L C cy)⊆wires (clrDH L C cy) := OwnDHSubsets.shared_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem finite_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 wires (finiteProgram L C cy Gen)⊆wires (Edges.finiteProgram L C cy Gen) := by
 intro q hq
 have clear (h:q∈wires (clrClear L C cy)) : q∈wires (clrDH L C cy) := clear_subset L C cy h
 have restore (h:q∈wires (clrRestore L C cy)) : q∈wires (clrDH L C cy) := restore_subset L C cy h
 simp only [finiteProgram,Edges.finiteProgram,wires_append,Finset.mem_union] at hq ⊢
 tauto

theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 wires (wrapper L C cy Gen)⊆wires (Edges.wrapper L C cy Gen) := by
 change wires (renameProgram (Wrapper5.U L) _) ⊆ wires (renameProgram (Wrapper5.U L) _)
 rw [renameProgram_support,renameProgram_support]
 exact Finset.image_subset_image (finite_subset L C cy _)

theorem clear_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (C : Point) (cy : Fp) :
 GatePhysical (clrClear L C cy) := OwnMeasuredDH.gadgetM_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C))
theorem restore_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (C : Point) (cy : Fp) :
 GatePhysical (clrRestore L C cy) := OwnSharedDH.gadget_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C))
theorem finite_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (C : Point) (cy : Fp) (Gen : Program) (hG:GatePhysical Gen) : GatePhysical (finiteProgram L C cy Gen) := by
 have hp:=Edges.finite_physical L hw hn C cy Gen hG
 have hc:=clear_physical L hw hn C cy
 have hr:=restore_physical L hw hn C cy
 simp only [Edges.finiteProgram,gatePhysical_append] at hp
 simp only [finiteProgram,gatePhysical_append]
 tauto
 theorem wrapper_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (C : Point) (cy : Fp) (Gen : Program) (hG:GatePhysical Gen) : GatePhysical (wrapper L C cy Gen) :=
 gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective _
  (finite_physical L hw hn C cy _ (gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective Gen hG))

theorem finite_slots (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 gateSlots (finiteProgram L C cy Gen)≤gateSlots (Edges.finiteProgram L C cy Gen)+68 := by
 have hc:gateSlots (clrClear L C cy)≤35:=OwnMeasuredDH.gadgetM_gateSlots _ _ _ _ _ _ _ _ _ _ _ _ _ _
 have hr:gateSlots (clrRestore L C cy)≤33:=OwnSharedDH.gadget_gateSlots _ _ _ _ _ _ _ _ _ _ _ _ _ _
 simp only [finiteProgram,Edges.finiteProgram,gateSlots_append]
 omega
 theorem wrapper_slots (L : ControlledPointLayout) (hw:L.Widths) (C : Point) (cy : Fp) (Gen : Program) :
 gateSlots (wrapper L C cy Gen)≤22904+gateSlots Gen := by
 have old:=Edges.wrapper_slots L hw C cy Gen
 have diff:=finite_slots L C cy (renameProgram (Wrapper5.U L) Gen)
 simp only [wrapper,Edges.wrapper,rename_gateSlots] at old ⊢
 omega
end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component FullFrame
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem wrapper_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    wires (wrapper L C cy Gen) ⊆ WrapperOB5.support L :=
 (wrapper_subset L C cy Gen).trans (Edges.wrapper_support L hw hn C cy Gen hG)
private theorem dh3_13_boundary_frame (L : ControlledPointLayout) (P : Program)
    (hP : wires P ⊆ L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q ∉ PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem dh3_13_boundary_work (L : ControlledPointLayout) : L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem dh3_13_work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,ControlledPointLayout.point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- The new support inventory closes the complete work frame, including parity2312. -/
theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen)
    (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} wrapper L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (dh3_13_boundary_work L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := wrapper_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (wrapper_support L hw hn (.some hc) cy Gen hG).trans (WrapperOB5.support_used L hw)
  rw [dh3_13_boundary_frame L _ hsup R _ b s m hi ho q (dh3_13_work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end ECDSAAdd.Entrant.OwnDHWrapper

end
end FrontierDH

section FrontierTerminalGraph

-- TERMINAL GRAPH COMPONENT GraphCell
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorSum (a b cin out : Wire) : Program := [.CX a out,.CX b out,.CX cin out]

theorem xorSum_run (a b cin out : Wire) (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (s : State) (m : List Bool) :
    run (xorSum a b cin out) m s =
      ⟨s.phase,writeBit s.basis out (s.basis out ^^ sumBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [xorSum,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=out
  · subst q
    simp [writeBit,Function.update,ha,hb,hc,sumBit,Bool.xor_assoc]
  · simp [writeBit,Function.update,hq]

/-- Decode a supplied sum bit into a clean carry wire using only CNOTs. -/
theorem extractCarry_run (a b out carry : Wire)
    (ha : a≠carry) (hb : b≠carry) (ho : out≠carry)
    (s : State) (m : List Bool) (clean : s.basis carry=false) (C : Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) C) :
    run (xorSum a b out carry) m s=⟨s.phase,writeBit s.basis carry C⟩ := by
  rw [xorSum_run a b out carry ha hb ho,clean,sum]
  congr 2
  cases s.basis a <;> cases s.basis b <;> cases C <;> rfl

def eraseGraphCell (a b cin out carry : Wire) : Program :=
  xorSum a b cin out ++ eraseCarry a b cin carry

/-- A supplied sum/majority graph is erased with zero T, for every measurement tape. -/
theorem eraseGraphCell_run (a b cin out carry : Wire)
    (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (hak : a≠carry) (hbk : b≠carry) (hck : cin≠carry)
    (hok : out≠carry) (s : State) (m : List Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) (s.basis cin))
    (maj : s.basis carry=carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run (eraseGraphCell a b cin out carry) m s=
      ⟨s.phase,writeBit (writeBit s.basis out false) carry false⟩ := by
  have x : run (xorSum a b cin out) m s=⟨s.phase,writeBit s.basis out false⟩ := by
    rw [xorSum_run a b cin out ha hb hc,sum]
    simp
  let t : State:=⟨s.phase,writeBit s.basis out false⟩
  have tm : t.basis carry=carryBit (t.basis a) (t.basis b) (t.basis cin) := by
    simpa only [t,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,
      Function.update_of_ne hc,Function.update_of_ne hok.symm] using maj
  rw [eraseGraphCell,run_append,run_take,x]
  simpa only [t] using eraseCarry_correct a b cin carry hak hbk hck t tm
    (m.drop (measurementCount (xorSum a b cin out)))

theorem graphCell_resources (a b cin out carry : Wire) :
    toffoliCount (eraseGraphCell a b cin out carry)=0 ∧
    measurementCount (eraseGraphCell a b cin out carry)=1 := by
  simp [eraseGraphCell,xorSum,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,eraseCarry]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AffineStream
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def parity (xs : List Wire) (b : BasisState) : Bool:=xs.foldr (fun x t=>b x ^^ t) false
def xorList (xs : List Wire) (target : Wire) : Program:=xs.map (fun x=>.CX x target)

theorem parity_congr (xs : List Wire) (b b' : BasisState) (h : ∀q∈xs,b q=b' q) :
    parity xs b=parity xs b' := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change (b x ^^ parity xs b)=(b' x ^^ parity xs b')
    rw [h x (by simp),ih (fun q hq=>h q (by simp [hq]))]

theorem xorList_run (xs : List Wire) (target : Wire) (away : target∉xs)
    (s : State) (m : List Bool) :
    run (xorList xs target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil=>
    simp only [xorList,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq:q=target <;> simp [writeBit,hq]
  | cons x xs ih=>
    have xt:x≠target:=fun e=>away (by simp [e])
    have tail:target∉xs:=fun h=>away (by simp [h])
    let t : State:=⟨s.phase,writeBit s.basis target (s.basis target ^^ s.basis x)⟩
    have pa:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
      intro q hq
      have nq:q≠target:=fun e=>tail (e ▸ hq)
      simp [t,writeBit,nq])
    simp only [xorList,List.map_cons,run]
    change run (xorList xs target) m t=_
    rw [ih tail t,pa]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=target
    · subst q
      simp [t,writeBit,parity,Bool.xor_assoc]
    · simp [t,writeBit,hq]

/-- Move a supplied output into a consumed clean target slot, removing its affine sum.
The full state map is Clifford and holds without any arithmetic-graph premise. -/
def streamStage (xs : List Wire) (prev out : Wire) : Program:=
  [.CX out prev]++xorList xs prev++xorList xs out++[.CX prev out]

theorem streamStage_run (xs : List Wire) (prev out : Wire)
    (ne : prev≠out) (ap : prev∉xs) (ao : out∉xs)
    (s : State) (m : List Bool) (clean : s.basis prev=false) :
    run (streamStage xs prev out) m s=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
  let t : State:=⟨s.phase,writeBit s.basis prev (s.basis out)⟩
  have first (r : List Bool) : run [.CX out prev] r s=t:=by simp [run,t,writeBit,clean]
  have par1:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [t,writeBit,nq])
  let u : State:=⟨s.phase,writeBit t.basis prev (s.basis out ^^ parity xs s.basis)⟩
  have second (r : List Bool) : run (xorList xs prev) r t=u:=by
    rw [xorList_run xs prev ap,par1]
    simp [u,t,writeBit]
  have par2:parity xs u.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [u,t,writeBit,nq])
  let v : State:=⟨s.phase,writeBit u.basis out (s.basis out ^^ parity xs s.basis)⟩
  have third (r : List Bool) : run (xorList xs out) r u=v:=by
    rw [xorList_run xs out ao,par2]
    simp [v,u,t,writeBit,Ne.symm ne]
  have final:run [.CX prev out] m v=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
    simp only [run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hp:q=prev
    · subst q;simp [v,u,t,writeBit,ne]
    · by_cases ho:q=out
      · subst q;simp [v,u,t,writeBit,ne,Ne.symm ne]
      · simp [v,u,t,writeBit,hp,ho]
  have zero (xs : List Wire) (target : Wire) : measurementCount (xorList xs target)=0:=by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simpa only [xorList,List.map_cons,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih
  rw [streamStage]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.sum_cons,
    List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero,zero]
  rw [first,second,third]
  exact final
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT ControlledCompare
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def selectedBorrow (bit : Bool) (x cin carry control target : Wire) : Program :=
  constantBorrow bit x cin carry ++ [.CCX control carry target] ++ constantBorrowErase bit x cin carry

theorem selectedBorrow_counts (bit : Bool) (x cin carry control target : Wire) :
    toffoliCount (selectedBorrow bit x cin carry control target)=2 ∧
    measurementCount (selectedBorrow bit x cin carry control target)=1 := by
  have c:=constantBorrow_counts bit x cin carry
  simp only [selectedBorrow,toffoliCount_append,measurementCount_append,c.1,c.2.1,c.2.2.1,c.2.2.2]
  simp [toffoliCount,measurementCount]

def compareSelected : List Wire → List Wire → Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,control,target,k =>
      constantBorrow (decide (k%2=1)) x cin c ++
        compareSelected (x'::xs) cs c control target (k/2) ++
          constantBorrowErase (decide (k%2=1)) x cin c
  | [x],c::_,cin,control,target,k => selectedBorrow (decide (k%2=1)) x cin c control target
  | _,_,_,_,_,_ => []

theorem compareSelected_counts (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : 0<xs.length) (hc : carry.length=xs.length) :
    toffoliCount (compareSelected xs carry cin control target k)=xs.length+1 ∧
    measurementCount (compareSelected xs carry cin control target k)=xs.length := by
  induction xs generalizing carry cin k with
  | nil => simp at hn
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs => simpa only [compareSelected,List.length_cons,List.length_nil] using selectedBorrow_counts (decide (k%2=1)) x cin c control target
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have r:=ih cs c (k/2) (by simp) (by simpa using hc)
        have b:=constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        constructor
        · simp only [toffoliCount_append,b.1,b.2.2.1,r.1,List.length_cons];omega
        · simp only [measurementCount_append,b.2.1,b.2.2.2,r.2,List.length_cons];omega

theorem selectedBorrow_correct (bit : Bool) (x cin carry control target : Wire)
    (hn : [x,cin,carry,control,target].Nodup) (s : State) (m : List Bool)
    (zero : s.basis carry=false) :
    run (selectedBorrow bit x cin carry control target) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (s.basis target ^^ (s.basis control && carryBit (!s.basis x) bit (s.basis cin)))) carry false⟩ := by
  have nd : [x,cin,carry].Nodup:=hn.sublist (by simp)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxi,hxc,hxb,hxt⟩,⟨hic,hib,hit⟩,⟨hcb,hct⟩,hbt⟩:=hn
  let K:=carryBit (!s.basis x) bit (s.basis cin)
  let s1 : State:=⟨s.phase,writeBit s.basis carry K⟩
  have first (r : List Bool) : run (constantBorrow bit x cin carry) r s=s1 := by
    rw [constantBorrow_correct bit x cin carry nd,zero]
    simp [s1,K]
  let s2 : State:=⟨s.phase,writeBit s1.basis target (s.basis target ^^ (s.basis control && K))⟩
  have second (r : List Bool) : run [.CCX control carry target] r s1=s2 := by
    simp [s1,s2,run,writeBit,(Ne.symm hct),(Ne.symm hcb)]
  have final (r : List Bool) : run (constantBorrowErase bit x cin carry) r s2=
      ⟨s.phase,writeBit s2.basis carry false⟩ := by
    have km : s2.basis carry=carryBit (!s2.basis x) bit (s2.basis cin) := by
      simp [s2,s1,writeBit,hct,hxt,hit,hxc,hic,K]
    exact constantBorrowErase_correct bit x cin carry nd s2 r km
  have counts:=constantBorrow_counts bit x cin carry
  rw [selectedBorrow]
  simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
  rw [first,second,final]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=carry
  · subst q;simp [s1,s2,writeBit]
  · by_cases ht:q=target
    · subst q;simp [s1,s2,writeBit,(Ne.symm hct),K]
    · simp [s1,s2,writeBit,hq,ht]

theorem compareSelected_correct (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : (control::target::cin::(xs++carry)).Nodup) (hpos : 0<xs.length)
    (hc : carry.length=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareSelected xs carry cin control target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareSelected xs carry cin control target k) m s).basis q=s.basis q) ∧
    (run (compareSelected xs carry cin control target k) m s).basis target=
      (s.basis target ^^ (s.basis control && decide (regValue xs s.basis<k+(s.basis cin).toNat))) := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hpos
  | cons x xs ih =>
    have cnt:=List.nodup_iff_count.mp hn
    have htx : target≠x := by
      intro bad;have h:=cnt target;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have htci : target≠cin := by
      intro bad;have h:=cnt target;subst cin
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have hxc : x≠cin := by
      intro bad;have h:=cnt cin;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c,control,target].Nodup := by
          apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have htc : target≠c := by
          intro bad;have h:=cnt target;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have zero:=hclean c (by simp)
        rw [compareSelected,selectedBorrow_correct _ _ _ _ _ _ nd s m zero]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          by_cases hqc:q=c
          · subst q;simp [writeBit,zero]
          · simp [writeBit,hqc,hq]
        · have small : k<2 := by simpa using hk
          by_cases h0:k=0
          · subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
          · have h1:k=1:=by omega
            subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have htc : target≠c := by
          intro bad; have h := cnt target; subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hbc : control≠c := by
          intro bad; have h:=cnt control;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hxc' : x≠c := by
          intro bad; have h := cnt c; subst x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcic : cin≠c := by
          intro bad; have h := cnt c; subst cin
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hctail : c∉x'::xs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
          omega
        have hccs : c∉cs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nd' : (control::target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        let bit := decide (k%2=1)
        let K := carryBit (!s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by simp [s1,writeBit,hq]
        have zero := hclean c (by simp)
        have first (record : List Bool) : run (constantBorrow bit x cin c) record s=s1 := by
          rw [constantBorrow_correct _ _ _ _ nd]
          simp [s1,K,zero]
        have clean' : ∀q∈cs,s1.basis q=false := by
          intro q hq
          rw [keep q (fun bad => hccs (bad ▸ hq))]
          exact hclean q (by simp [hq])
        have high : k/2<2^(x'::xs).length := by
          simp only [List.length_cons,Nat.pow_succ] at hk ⊢
          omega
        obtain ⟨hp,he,hv⟩ := ih cs c (k/2) nd' (by simp) (by simpa using hc) high s1 m clean'
        let t := run (compareSelected (x'::xs) cs c control target (k/2)) m s1
        have tx : t.basis x=s.basis x := (he x htx.symm).trans (keep x hxc')
        have ti : t.basis cin=s.basis cin := (he cin htci.symm).trans (keep cin hcic)
        have tk : t.basis c=K := by rw [he c htc.symm]; simp [s1,writeBit]
        have clear (record : List Bool) : run (constantBorrowErase bit x cin c) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply constantBorrowErase_correct _ _ _ _ nd t record
          rw [tx,ti,tk]
        have counts := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
        rw [first]
        change (run (constantBorrowErase bit x cin c) _ t).phase=_ ∧ _
        rw [clear]
        refine ⟨hp,?_,?_⟩
        · intro q hq
          by_cases hqc : q=c
          · subst q; simp [writeBit,zero]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (he q hq).trans (keep q hqc)
        · simp only [writeBit,Function.update_of_ne htc]
          rw [hv,keep target htc,keep control hbc]
          have v : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (fun bad => hctail (bad ▸ hq)))
          have carryVal : s1.basis c=K := by simp [s1,writeBit]
          rw [v,carryVal]
          have split : bit.toNat+2*(k/2)=k := by
            have e := Nat.mod_add_div k 2
            have b := Nat.mod_lt k (by decide : 0<2)
            by_cases odd : k%2=1 <;> simp [bit,odd] <;> omega
          have thr := borrow_threshold (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2)
          rw [split] at thr
          have pred : decide (regValue (x::x'::xs) s.basis<k+(s.basis cin).toNat)=
              decide (regValue (x'::xs) s.basis<k/2+K.toNat) := by
            apply decide_eq_decide.mpr
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
          rw [pred]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Emitter
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

structure DecoderLayout where
  y : List Wire
  r : List Wire
  carry : List Wire
  sigma : Wire
  h : Wire
  bias : Wire

def DecoderLayout.Widths (L : DecoderLayout) : Prop:=L.y.length=256 ∧ L.r.length=256 ∧ L.carry.length=255

def DecoderLayout.Y (L : DecoderLayout) (i : Nat):Wire:=L.y.getD i 0
def DecoderLayout.R (L : DecoderLayout) (i : Nat):Wire:=L.r.getD i 0
def DecoderLayout.A (L : DecoderLayout) (i : Nat):Wire:=L.carry.getD i 0

def rawSources (L : DecoderLayout) (i : Nat) : List Wire:=
 if i=0 then [L.Y 0]
 else if i<255 then [L.Y (i-1),L.Y i,L.sigma,L.A (i-1)]
 else [L.Y 254,L.sigma,L.A 254]

def correction (L : DecoderLayout) (i : Nat) : MappedBit:=
 if i=1 then ⟨some L.bias,false⟩
 else if Nat.testBit (2^32+977) i then ⟨some L.h,false⟩ else ⟨none,false⟩

def correctionSources (L : DecoderLayout) (i : Nat) : List Wire:=
 (correction L i).wire.toList

def addCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.CCX L.sigma (L.Y 0) (L.A 0),.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++majority (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def eraseAddCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.measureX (L.A 0) [] [.CZ L.sigma (L.Y 0)],.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++eraseCarry (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def streamCarry (L : DecoderLayout) (i : Nat) : Program:=
 streamStage (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)

def eraseCorrectionCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=1 then [.measureX (L.R 0) [] [.CZ (L.Y 0) L.h]]
 else xorList (rawSources L (i-1)) (L.R 255)++
   mappedEraseCarry (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))++
     xorList (rawSources L (i-1)) (L.R 255)

def biasCompute (L : DecoderLayout) : Program:=
 [.X L.sigma,.CCX (L.Y 255) L.sigma L.bias,.X L.sigma]
def biasErase (L : DecoderLayout) : Program:=
 [.X L.sigma,.measureX L.bias [] [.CZ (L.Y 255) L.sigma],.X L.sigma]

def normalize (L : DecoderLayout) : Program:=
 (L.y.take 255).map (fun q=>.CX (L.Y 255) q)++L.r.map (fun q=>.CX (L.Y 255) q)
def restoreSource (L : DecoderLayout) : Program:=(L.y.take 255).map (fun q=>.CX (L.Y 255) q)
def copySource (L : DecoderLayout) : Program:=(L.y.zip L.r).map (fun q=>.CX q.1 q.2)

def clearQuotient (L : DecoderLayout) : Program:=
 [.X (L.Y 255),.X L.sigma]++
   compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)++
     [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]

def decoder (L : DecoderLayout) : Program:=
 normalize L++[.CX (L.R 0) L.h,.CX (L.Y 0) L.h]++biasCompute L++
 (List.range 255).flatMap (addCarry L)++
 xorList (rawSources L 0++correctionSources L 0) (L.R 0)++
 (List.range' 1 255).flatMap (streamCarry L)++
 (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)++
 (List.range 255).reverse.flatMap (eraseAddCarry L)++
 biasErase L++clearQuotient L++restoreSource L++copySource L

theorem xorList_counts (xs : List Wire) (target : Wire) :
 toffoliCount (xorList xs target)=0 ∧ measurementCount (xorList xs target)=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [xorList,List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem streamStage_counts (xs : List Wire) (prev out : Wire) :
 toffoliCount (streamStage xs prev out)=0 ∧ measurementCount (streamStage xs prev out)=0 := by
 have p:=xorList_counts xs prev;have q:=xorList_counts xs out
 simp [streamStage,toffoliCount_append,measurementCount_append,p.1,p.2,q.1,q.2,toffoliCount,measurementCount]

theorem local_counts (L : DecoderLayout) (i : Nat) :
 (toffoliCount (addCarry L i)=1 ∧ measurementCount (addCarry L i)=0) ∧
 (toffoliCount (eraseAddCarry L i)=0 ∧ measurementCount (eraseAddCarry L i)=1) ∧
 (toffoliCount (streamCarry L i)=0 ∧ measurementCount (streamCarry L i)=0) ∧
 (toffoliCount (eraseCorrectionCarry L i)=0 ∧ measurementCount (eraseCorrectionCarry L i)=1) := by
 have st:=streamStage_counts (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)
 have x:=xorList_counts (rawSources L (i-1)) (L.R 255)
 have m:=mappedBit_counts (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))
 constructor
 · by_cases h:i=0 <;> simp [addCarry,h,majority,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · by_cases h:i=0 <;> simp [eraseAddCarry,h,eraseCarry,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · exact st
 · by_cases h:i=1
   · simp [eraseCorrectionCarry,h,toffoliCount,measurementCount]
   · simp only [eraseCorrectionCarry,h,ite_false,toffoliCount_append,measurementCount_append,x.1,x.2,m.2.2.1,m.2.2.2.1]
     simp
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Counts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flat_counts {α : Type} (xs : List α) (f : α→Program) (T M : Nat)
    (h : ∀i∈xs,toffoliCount (f i)=T ∧ measurementCount (f i)=M) :
    toffoliCount (xs.flatMap f)=T*xs.length ∧ measurementCount (xs.flatMap f)=M*xs.length := by
 induction xs with
 | nil=>simp [toffoliCount,measurementCount]
 | cons x xs ih=>
   have a:=h x (by simp)
   have b:=ih (fun i hi=>h i (by simp [hi]))
   simp only [List.flatMap_cons,toffoliCount_append,measurementCount_append,List.length_cons,a.1,a.2,b.1,b.2,Nat.mul_succ]
   constructor <;> omega

theorem cxMap_counts {α : Type} (xs : List α) (f g : α→Wire) :
    toffoliCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 ∧
    measurementCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem simple_counts (L : DecoderLayout) :
 (toffoliCount (normalize L)=0 ∧ measurementCount (normalize L)=0) ∧
 (toffoliCount (restoreSource L)=0 ∧ measurementCount (restoreSource L)=0) ∧
 (toffoliCount (copySource L)=0 ∧ measurementCount (copySource L)=0) ∧
 (toffoliCount (biasCompute L)=1 ∧ measurementCount (biasCompute L)=0) ∧
 (toffoliCount (biasErase L)=0 ∧ measurementCount (biasErase L)=1) := by
 have a:=cxMap_counts (L.y.take 255) (fun _=>L.Y 255) id
 have b:=cxMap_counts L.r (fun _=>L.Y 255) id
 have c:=cxMap_counts (L.y.zip L.r) Prod.fst Prod.snd
 simp only [id_eq] at a b
 refine ⟨?_,?_,?_,?_,?_⟩
 · simp only [normalize,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,Nat.zero_add,and_self]
 · exact a
 · exact c
 · simp [biasCompute,toffoliCount,measurementCount]
 · simp [biasErase,toffoliCount,measurementCount]


theorem clearQuotient_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (clearQuotient L)=256 ∧ measurementCount (clearQuotient L)=255 := by
 have yl : (L.y.take 255).length=255:=by simp [hw.1]
 have c:=compareSelected_counts (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)
   (by omega) (by rw [hw.2.2,yl])
 simp only [clearQuotient,toffoliCount_append,measurementCount_append,c.1,c.2,yl]
 simp [toffoliCount,measurementCount]

theorem decoder_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (decoder L)=512 ∧ measurementCount (decoder L)=766 := by
 have a:=flat_counts (List.range 255) (addCarry L) 1 0 (fun i _=>(local_counts L i).1)
 have b:=flat_counts (List.range' 1 255) (streamCarry L) 0 0 (fun i _=>(local_counts L i).2.2.1)
 have c:=flat_counts (List.range' 1 255).reverse (eraseCorrectionCarry L) 0 1 (fun i _=>(local_counts L i).2.2.2)
 have d:=flat_counts (List.range 255).reverse (eraseAddCarry L) 0 1 (fun i _=>(local_counts L i).2.1)
 have z:=xorList_counts (rawSources L 0++correctionSources L 0) (L.R 0)
 have e:=simple_counts L
 have q:=clearQuotient_counts L hw
 simp only [List.length_range,List.length_range',List.length_reverse,Nat.one_mul,Nat.zero_mul] at a b c d
 simp only [decoder,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,z.1,z.2,
   e.1.1,e.1.2,e.2.1.1,e.2.1.2,e.2.2.1.1,e.2.2.1.2,e.2.2.2.1.1,e.2.2.2.1.2,e.2.2.2.2.1,e.2.2.2.2.2,q.1,q.2]
 simp [toffoliCount,measurementCount]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def cxWindow (sigma x : Wire) (P : Program) : Program := [.CX sigma x]++P++[.CX sigma x]
def cxBasis (sigma x : Wire) (b : BasisState) : BasisState :=writeBit b x (b x ^^ b sigma)

theorem cxWindow_write (sigma x target : Wire) (P : Program)
    (hsx : sigma≠x) (hst : sigma≠target) (hxt : x≠target)
    (s : State) (m : List Bool) (value : Bool)
    (middle : ∀r,run P r ⟨s.phase,cxBasis sigma x s.basis⟩=
      ⟨s.phase,writeBit (cxBasis sigma x s.basis) target value⟩) :
    run (cxWindow sigma x P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
  have first (r : List Bool):run [.CX sigma x] r s=⟨s.phase,cxBasis sigma x s.basis⟩:=rfl
  rw [cxWindow]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.map_cons,List.sum_cons,List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero]
  rw [first,middle]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hx:q=x
  · subst q;simp [cxBasis,writeBit,hsx,hst,hxt]
  · by_cases ht:q=target
    · subst q;simp [cxBasis,writeBit,hxt,Ne.symm hxt]
    · simp [cxBasis,writeBit,hx,ht]

theorem cxBasis_mapped (b : MappedBit) (sigma x : Wire) (basis : BasisState)
    (ha : ∀q∈b.wire,q≠x) : b.value (cxBasis sigma x basis)=b.value basis := by
 apply mappedBit_value_congr
 intro q hq
 simp [cxBasis,writeBit,ha q hq]

theorem windowMajority_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool) :
    run (cxWindow sigma x (mappedMajority b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout (s.basis cout ^^
        carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin))⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 rw [mappedMajority_correct b x cin cout nd ha]
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simp [cxBasis,writeBit,Ne.symm xc,ic]

theorem windowErase_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool)
    (known : s.basis cout=carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin)) :
    run (cxWindow sigma x (mappedEraseCarry b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout false⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 apply mappedEraseCarry_correct b x cin cout nd ha
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simpa [cxBasis,writeBit,Ne.symm xc,ic] using known
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT LayoutFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def DecoderLayout.wires (L : DecoderLayout) : List Wire:=
 [L.sigma,L.h,L.bias]++L.y++L.r++L.carry

def ofBalanced (L : BalancedCircuit.Layout) : DecoderLayout:=
 ⟨L.y,L.r,L.carry.take 254++[L.lower],L.sign,L.one,L.parity⟩

theorem ofBalanced_widths (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).Widths := by
 have w:=BalancedCleanup.widths L.toLayout hw
 simp [ofBalanced,DecoderLayout.Widths,w.2.1,w.2.2.1,List.length_take,hw.2.2]

theorem ofBalanced_nodup (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
 (ofBalanced L).wires.Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have take: (L.carry.take 254).count q≤L.carry.count q:=(List.take_sublist 254 L.carry).count_le q
 simp only [ofBalanced,DecoderLayout.wires,BalancedCircuit.Layout.wires,
  BalancedCleanup.Layout.wires,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,
  BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem getD_mem (xs : List Wire) (i : Nat) (hi : i<xs.length) : xs.getD i 0∈xs := by
 rw [List.getD_eq_getElem _ _ hi]
 exact List.getElem_mem hi

theorem getD_inj (xs : List Wire) (hn : xs.Nodup) (i j : Nat)
    (hi : i<xs.length) (hj : j<xs.length) (eq : xs.getD i 0=xs.getD j 0) : i=j := by
 apply List.getElem?_inj hi hn
 have x:=congrArg some eq
 simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj,
   List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using x

theorem register_nodup (L : DecoderLayout) (hn : L.wires.Nodup) :
 L.y.Nodup ∧ L.r.Nodup ∧ L.carry.Nodup := by
 unfold DecoderLayout.wires at hn
 have a:=List.nodup_append'.mp hn
 have b:=List.nodup_append'.mp a.1
 have c:=List.nodup_append'.mp b.1
 exact ⟨c.2.1,b.2.1,a.2.1⟩

theorem carry_source_away (L : DecoderLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry := by
 intro hc
 have h:=List.nodup_iff_count.mp hn q
 have pos:0<L.carry.count q:=List.count_pos_iff.mpr hc
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem carry_ne_carry (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i<255) (hj : j<255) (ne : i≠j) : L.A i≠L.A j := by
 intro eq
 have len:=hw.2.2
 exact ne (getD_inj L.carry (register_nodup L hn).2.2 i j (by omega) (by omega) eq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Geometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem y_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.Y i∈L.y :=
 getD_mem L.y i (by have h:=hw.1;omega)
theorem a_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<255) : L.A i∈L.carry :=
 getD_mem L.carry i (by have h:=hw.2.2;omega)
theorem r_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.R i∈L.r :=
 getD_mem L.r i (by have h:=hw.2.1;omega)

theorem y_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<255) : L.Y i≠L.A j := by
 intro e
 exact carry_source_away L hn _ (Or.inl (y_mem L hw i hi)) (e ▸ a_mem L hw j hj)

theorem sigma_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<255) : L.sigma≠L.A i := by
 intro e
 exact carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ a_mem L hw i hi)

theorem sigma_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) : L.sigma≠L.Y i := by
 intro eq
 have h:=List.nodup_iff_count.mp hn L.sigma
 have mem:=y_mem L hw i hi
 rw [←eq] at mem
 have pos:=List.count_pos_iff.mpr mem
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil,
  beq_self_eq_true,if_true] at h
 omega

theorem y_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.Y i≠L.Y j := by
 intro eq
 have len:=hw.1
 exact ne (getD_inj L.y (register_nodup L hn).1 i j (by omega) (by omega) eq)

theorem source_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (q : Wire) (hq : q∈L.y ∨ q∈L.carry ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.r := by
 intro hr
 have h:=List.nodup_iff_count.mp hn q
 have pos:=List.count_pos_iff.mpr hr
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|hc|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 · have cc:=List.count_pos_iff.mpr hc;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem raw_source_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈rawSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold rawSources at hq
 split_ifs at hq with h0 h255
 · have eq:q=L.Y 0:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
   subst q
   exact Or.inl (y_mem L hw 0 (by omega))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl
   · exact Or.inl (y_mem L hw (i-1) (by omega))
   · exact Or.inl (y_mem L hw i hi)
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw (i-1) (by omega)))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl
   · exact Or.inl (y_mem L hw 254 (by omega))
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw 254 (by omega)))
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientClear
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run compareSelected

theorem state_ext (s t : State) (hp : s.phase=t.phase) (hb : ∀q,s.basis q=t.basis q) : s=t := by
 cases s
 cases t
 exact congrArg₂ State.mk hp (funext hb)

theorem y_split (L : DecoderLayout) (hw : L.Widths) :
 L.y=L.y.take 255++[L.Y 255] := by
 have len:=hw.1
 have split : L.y.take 255++[L.y.getD 255 0]=L.y.take 256 := by
   conv_rhs=>rw [show 256=255+1 from rfl,List.take_add_one]
   simp only [List.getD_eq_getElem _ _ (by omega : 255<L.y.length)]
   simp [List.getElem?_eq_getElem (by omega : 255<L.y.length)]
 simpa only [DecoderLayout.Y,List.take_of_length_le (by omega : L.y.length≤256)] using split.symm

theorem compare_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.sigma::L.h::L.Y 255::(L.y.take 255++L.carry)).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 unfold DecoderLayout.wires at h
 rw [y_split L hw] at h
 simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem clearQuotient_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) (clean : ∀q∈L.carry,s.basis q=false)
 (quotient : s.basis L.h = (!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat)))) :
 run (clearQuotient L) m s=⟨s.phase,writeBit s.basis L.h false⟩ := by
 have nd:=compare_nd L hw hn
 have yz:=sigma_ne_y L hw hn 255 (by omega)
 have hs : L.h≠L.sigma := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 have hy : L.h≠L.Y 255 := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 let t : State:=⟨s.phase,writeBit (writeBit s.basis (L.Y 255) (!s.basis (L.Y 255))) L.sigma (!s.basis L.sigma)⟩
 have pre (r : List Bool) : run [.X (L.Y 255),.X L.sigma] r s=t := by
   simp [run,t,writeBit,yz]
 have tclean : ∀q∈L.carry,t.basis q=false := by
   intro q hq
   have qy:q≠L.Y 255:=fun e=>carry_source_away L hn _ (Or.inl (y_mem L hw 255 (by omega))) (e ▸ hq)
   have qs:q≠L.sigma:=fun e=>carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ hq)
   simpa only [t,writeBit,Function.update_of_ne qs,Function.update_of_ne qy] using clean q hq
 have tv : regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis := by
   apply regValue_congr
   intro q hq
   have qs:q≠L.sigma := fun e => (List.nodup_cons.mp nd).1 (by simp [←e,hq])
   have qy:q≠L.Y 255 := fun e =>
     (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2).1 (by simp [←e,hq])
   simp [t,writeBit,qs,qy]
 let k:=((p-1)/2)/3
 let v : State:=⟨s.phase,writeBit t.basis L.h
   (s.basis L.h ^^ (!s.basis L.sigma && decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat)))⟩
 have mid (r : List Bool) :
   run (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k) r t=v := by
   have c:=compareSelected_correct (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k nd
     (by simp [hw.1]) (by simp [hw.1,hw.2.2]) (by norm_num [k,p,hw.1]) t r tclean
   rw [tv] at c
   apply state_ext
   · exact c.1
   · intro q
     by_cases eq:q=L.h
     · subst q
       simpa [v,t,writeBit,hs,hy,Ne.symm yz,tv] using c.2.2
     · simpa [v,writeBit,eq] using c.2.1 q eq
 have post (r : List Bool) : run [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)] r v=
   ⟨s.phase,writeBit s.basis L.h false⟩ := by
   apply state_ext
   · simp [run,v,t]
   · intro q
     by_cases qh:q=L.h
     · subst q
       simp only [run,v,t,writeBit,Function.update_apply]
       simp only [hs,hy,Ne.symm hs,Ne.symm hy,yz,Ne.symm yz,if_false,if_true]
       rw [quotient]
       cases s.basis L.sigma <;>
         cases decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat) <;>
         simp_all [k]
     · by_cases qs:q=L.sigma
       · subst q;simp [run,v,t,writeBit,hs,Ne.symm hs,yz,Ne.symm yz]
       · by_cases qy:q=L.Y 255
         · subst q;simp [run,v,t,writeBit,hy,Ne.symm hy,yz,Ne.symm yz]
         · simp [run,v,t,writeBit,qh,qs,qy]
 have result:=run_three_states [.X (L.Y 255),.X L.sigma]
   (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k)
   [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]
   (fun a d => a=s → d=⟨s.phase,writeBit s.basis L.h false⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [pre] at hab
     subst b
     rw [mid] at hbc
     subst c
     exact hcd.symm.trans (post m3)) s m
 simpa only [clearQuotient,List.append_assoc,k] using result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT BiasSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem bias_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 [L.Y 255,L.sigma,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have mem:=y_mem L hw 255 (by omega)
 have take : (if L.Y 255==q then 1 else 0) ≤ L.y.count q := by
   by_cases eq:L.Y 255=q
   · subst q;simpa using (List.count_pos_iff.mpr mem)
   · simp [eq]
 simp only [DecoderLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
 omega

theorem biasCompute_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (biasCompute L) m s=
   ⟨s.phase,writeBit s.basis L.bias
      (s.basis L.bias ^^ (s.basis (L.Y 255) && !s.basis L.sigma))⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasCompute,run]
 apply congrArg (State.mk s.phase)
 funext q
 by_cases eq:q=L.sigma
 · subst q;simp [writeBit,yx,xb]
 · by_cases eb:q=L.bias
   · subst q;simp [writeBit,yx,Ne.symm xb]
   · simp [writeBit,eq,eb,yx]

theorem biasErase_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool)
 (known : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma)) :
 run (biasErase L) m s=⟨s.phase,writeBit s.basis L.bias false⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasErase,run]
 cases hm:m.headD false <;>
   simp [measureAndCorrect,correct,writeBit,yx,xb,Ne.symm xb,yb,known]
 all_goals
   funext q
   by_cases eq:q=L.sigma
   · subst q;simp [xb]
   · simp [Function.update_apply,eq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT NormalizeSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

def complementBasis (control : Wire) (xs : List Wire) (b : BasisState) : BasisState :=
 fun q=>if q∈xs then b q ^^ b control else b q

theorem conditional_complement_run (control : Wire) (xs : List Wire)
 (hn : xs.Nodup) (away : control∉xs) (s : State) (m : List Bool) :
 run (xs.map (fun q=>Instr.CX control q)) m s=⟨s.phase,complementBasis control xs s.basis⟩ := by
 induction xs generalizing s with
 | nil =>
   apply state_ext
   · simp [run]
   · intro q;simp [run,complementBasis]
 | cons x xs ih =>
   obtain ⟨xaway,tailnd⟩:=List.nodup_cons.mp hn
   have cx:control≠x:=fun e=>away (by simp [e])
   have ct:control∉xs:=fun h=>away (by simp [h])
   let t : State:=⟨s.phase,writeBit s.basis x (s.basis x ^^ s.basis control)⟩
   simp only [List.map_cons,run]
   change run (xs.map (fun q=>Instr.CX control q)) m t=_
   rw [ih tailnd ct]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=x
   · subst q;simp [complementBasis,t,writeBit,xaway]
   · simp [complementBasis,t,writeBit,eq,cx]

theorem normalize_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.y.take 255++L.r).Nodup ∧ L.Y 255∉L.y.take 255++L.r := by
 have full:(L.y++L.r).Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have h:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
   omega
 have sub:(L.y.take 255++L.r).Sublist (L.y++L.r) := (List.take_sublist 255 L.y).append (List.Sublist.refl _)
 constructor
 · exact full.sublist sub
 · have shape:=y_split L hw
   have hn':(L.y.take 255++[L.Y 255]++L.r).Nodup := by simpa only [←shape] using full
   intro mem
   have c:=List.nodup_iff_count.mp hn' (L.Y 255)
   have pos:=List.count_pos_iff.mpr mem
   simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos
   omega

theorem normalize_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (normalize L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 simpa only [normalize,List.map_append] using conditional_complement_run (L.Y 255) (L.y.take 255++L.r) nd.1 nd.2 s m

theorem restoreSource_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (restoreSource L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 exact conditional_complement_run (L.Y 255) (L.y.take 255)
   (List.nodup_append'.mp nd.1).1 (fun h=>nd.2 (List.mem_append_left _ h)) s m
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bSources (L : DecoderLayout) (i : Nat) : List Wire:=rawSources L i++correctionSources L i

theorem r_ne_r (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.R i≠L.R j := by
 intro eq
 have len:=hw.2.1
 exact ne (getD_inj L.r (register_nodup L hn).2.1 i j (by omega) (by omega) eq)

theorem correction_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (i : Nat) (q : Wire) (hq : q∈correctionSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold correctionSources correction at hq
 split_ifs at hq with h1 hc
 · have eq:q=L.bias:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
 · have eq:q=L.h:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
 · simp at hq

theorem bSources_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈bSources L i) : q∉L.r := by
 rcases List.mem_append.mp hq with h|h
 · exact raw_source_r_away L hw hn i hi q h
 · exact correction_r_away L hn i q h

theorem bSources_parity (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState)
 (agree : ∀q,q∉L.r→s q=t q) : parity (bSources L i) s=parity (bSources L i) t := by
 apply parity_congr
 intro q hq
 exact agree q (bSources_r_away L hw hn i hi q hq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamForward
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bExpected (L : DecoderLayout) (origin : BasisState) (i : Nat) : Bool:=
 origin (L.R i) ^^ parity (bSources L i) origin

structure StreamFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀q,q∉L.r→s.basis q=origin.basis q
 stored : ∀j,j<nDone→s.basis (L.R j)=bExpected L origin.basis (j+1)
 current : s.basis (L.R nDone)=false
 pending : ∀j,nDone<j→j<256→s.basis (L.R j)=origin.basis (L.R j)

theorem stream_initial (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (m : List Bool)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) :
 StreamFrame L origin 0 (run (xorList (bSources L 0) (L.R 0)) m origin) := by
 have away:L.R 0∉bSources L 0:=by
   intro h;exact bSources_r_away L hw hn 0 (by omega) _ h (r_mem L hw 0 (by omega))
 rw [xorList_run _ _ away,low]
 simp only [Bool.xor_self]
 refine ⟨rfl,?_,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R 0:=fun e=>hq (e ▸ r_mem L hw 0 (by omega))
   simp [writeBit,ne]
 · intro j hj;omega
 · simp [writeBit]
 · intro j hj hbound
   simp [writeBit,r_ne_r L hw hn j 0 hbound (by omega) (by omega)]

theorem stream_frame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (n : Nat) (bound : n<255) (f : StreamFrame L origin n s) (m : List Bool) :
 StreamFrame L origin (n+1) (run (streamCarry L (n+1)) m s) := by
 have ne:=r_ne_r L hw hn n (n+1) (by omega) (by omega) (by omega)
 have ap:L.R n∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw n (by omega))
 have ao:L.R (n+1)∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw (n+1) (by omega))
 have par:=bSources_parity L hw hn (n+1) (by omega) s.basis origin.basis f.outside
 have pending:=f.pending (n+1) (by omega) (by omega)
 simp only [streamCarry,Nat.add_sub_cancel]
 change StreamFrame L origin (n+1) (run (streamStage (bSources L (n+1)) (L.R n) (L.R (n+1))) m s)
 rw [streamStage_run _ _ _ ne ap ao s m f.current,pending,par]
 change StreamFrame L origin (n+1)
   ⟨s.phase,writeBit (writeBit s.basis (L.R n) (bExpected L origin.basis (n+1))) (L.R (n+1)) false⟩
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · intro q hq
   have n0:q≠L.R n:=fun e=>hq (e ▸ r_mem L hw n (by omega))
   have n1:q≠L.R (n+1):=fun e=>hq (e ▸ r_mem L hw (n+1) (by omega))
   simpa only [writeBit,Function.update_of_ne n0,Function.update_of_ne n1] using f.outside q hq
 · intro j hj
   have nj1:=r_ne_r L hw hn j (n+1) (by omega) (by omega) (by omega)
   simp only [writeBit,Function.update_of_ne nj1]
   by_cases eq:j=n
   · subst j;simp
   · have nj0:=r_ne_r L hw hn j n (by omega) (by omega) eq
     simpa only [Function.update_of_ne nj0] using f.stored j (by omega)
 · simp [writeBit]
 · intro j hj hbound
   have nj1:=r_ne_r L hw hn j (n+1) hbound (by omega) (by omega)
   have nj0:=r_ne_r L hw hn j n hbound (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne nj0,Function.update_of_ne nj1] using f.pending j (by omega) hbound

theorem stream_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : StreamFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 StreamFrame L origin n (run ((List.range' 1 n).flatMap (streamCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [Nat.add_comm 1 n]
   apply stream_frame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT XorWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorWindow (xs : List Wire) (temp : Wire) (P : Program) : Program:=xorList xs temp++P++xorList xs temp

theorem xorWindow_write (xs : List Wire) (temp target : Wire) (P : Program)
 (awayT : temp∉xs) (awayQ : target∉xs) (ne : temp≠target)
 (s : State) (m : List Bool) (value : Bool)
 (middle : ∀r,run P r ⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩=
   ⟨s.phase,writeBit (writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)) target value⟩) :
 run (xorWindow xs temp P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
 let t : State:=⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩
 let u : State:=⟨s.phase,writeBit t.basis target value⟩
 have first (r : List Bool):run (xorList xs temp) r s=t:=xorList_run _ _ awayT _ _
 have par:parity xs u.basis=parity xs s.basis:=by
   apply parity_congr
   intro q hq
   have qt:q≠temp:=fun e=>awayT (e ▸ hq)
   have qq:q≠target:=fun e=>awayQ (e ▸ hq)
   simp [u,t,writeBit,qt,qq]
 have last (r : List Bool):run (xorList xs temp) r u=⟨s.phase,writeBit s.basis target value⟩:=by
   rw [xorList_run _ _ awayT,par]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases qt:q=temp
   · subst q;simp [u,t,writeBit,ne]
   · by_cases qq:q=target
     · subst q;simp [u,t,writeBit,ne,Ne.symm ne]
     · simp [u,t,writeBit,qt,qq]
 rw [xorWindow]
 simp only [List.append_assoc,run_append,run_take,(xorList_counts xs temp).2,List.take_zero,List.drop_zero]
 rw [first,middle]
 exact last _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamEraseSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def BGraph (L : DecoderLayout) (origin : BasisState) : Prop:=
 ∀ i, 1 ≤ i → i ≤ 255 → bExpected L origin i=
   carryBit ((correction L (i-1)).value origin) (parity (rawSources L (i-1)) origin)
     (if i=1 then false else bExpected L origin (i-1))

structure EraseBFrame (L : DecoderLayout) (origin : State) (nLive : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀ q, q∉L.r → s.basis q=origin.basis q
 live : ∀j,j<nLive → s.basis (L.R j)=bExpected L origin.basis (j+1)
 clean : ∀j,nLive ≤ j → j<256 → s.basis (L.R j)=false

theorem flag_y_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈[L.sigma,L.h,L.bias]) : q∉L.y := by
 intro hy
 have p:=List.count_pos_iff.mpr hq
 have y:=List.count_pos_iff.mpr hy
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at h
 omega

theorem correction_option_r_away (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (q : Wire) (hq : q∈(correction L i).wire) : q∉L.r := by
 apply correction_r_away L hn i q
 simpa only [correctionSources,Option.mem_toList] using hq

theorem correction_value_same (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 (correction L i).value s=(correction L i).value t := by
 apply mappedBit_value_congr
 intro q hq
 exact same q (correction_option_r_away L hn i q hq)

theorem raw_parity_same (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 parity (rawSources L i) s=parity (rawSources L i) t := by
 apply parity_congr
 intro q hq
 exact same q (raw_source_r_away L hw hn i hi q hq)

theorem eraseCorrectionCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 run (eraseCorrectionCarry L i) m s=⟨s.phase,writeBit s.basis (L.R (i-1)) false⟩ := by
 by_cases h1:i=1
 · subst i
   have ym:=y_mem L hw 0 (by omega)
   have rm:=r_mem L hw 0 (by omega)
   have hy:L.h∉L.y:=flag_y_away L hn _ (by simp)
   have yr:L.Y 0≠L.R 0:=fun e=>source_r_away L hn _ (Or.inl ym) (e ▸ rm)
   have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ rm)
   have yh:L.Y 0≠L.h:=fun e=>hy (e ▸ ym)
   have nd:[L.Y 0,L.h,L.R 0].Nodup:=by simp [yh,yr,hr]
   have ySame:=f.outside (L.Y 0) (source_r_away L hn _ (Or.inl ym))
   have hSame:=f.outside L.h (source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
   have g:=graph 1 (by omega) (by omega)
   have k:=f.live 0 (by omega)
   have corr:correction L 0=⟨some L.h,false⟩:=by rfl
   rw [show 1-1=0 by omega] at g
   rw [corr] at g
   simp only [rawSources,ite_true,parity,List.foldr_cons,List.foldr_nil,Bool.xor_false,
     MappedBit.value,Option.map_some,Option.getD_some,Bool.false_xor,ite_true] at g
   have known:s.basis (L.R 0)=carryBit false (s.basis (L.Y 0)) (s.basis L.h) := by
     rw [k,g,ySame,hSame]
     cases origin.basis (L.Y 0) <;> cases origin.basis L.h <;> rfl
   change run (mappedEraseCarry ⟨none,false⟩ (L.Y 0) L.h (L.R 0)) m s=_
   apply mappedEraseCarry_correct ⟨none,false⟩ (L.Y 0) L.h (L.R 0) nd (by simp)
   simpa [MappedBit.value] using known
 · have h2:2 ≤ i:=by omega
   let tmp:=L.R 255
   let cin:=L.R (i-2)
   let target:=L.R (i-1)
   have tc:tmp≠cin:=r_ne_r L hw hn 255 (i-2) (by omega) (by omega) (by omega)
   have tt:tmp≠target:=r_ne_r L hw hn 255 (i-1) (by omega) (by omega) (by omega)
   have ct:cin≠target:=r_ne_r L hw hn (i-2) (i-1) (by omega) (by omega) (by omega)
   have nd:[tmp,cin,target].Nodup:=by simp [tc,tt,ct]
   have optAway:∀q∈(correction L (i-1)).wire,q∉[tmp,cin,target]:=by
     intro q hq bad
     have away:=correction_option_r_away L hn (i-1) q hq
     simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
     rcases bad with rfl|rfl|rfl
     · exact away (r_mem L hw 255 (by omega))
     · exact away (r_mem L hw (i-2) (by omega))
     · exact away (r_mem L hw (i-1) (by omega))
   have awayTemp:tmp∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) tmp q (r_mem L hw 255 (by omega))
   have aq:target∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) target q (r_mem L hw (i-1) (by omega))
   have tempZero:s.basis tmp=false:=f.clean 255 hi (by omega)
   have rawSame:=raw_parity_same L hw hn (i-1) (by omega) s.basis origin.basis f.outside
   have corSame:=correction_value_same L hn (i-1) s.basis origin.basis f.outside
   have cinValue:s.basis cin=bExpected L origin.basis (i-1):=by
     have a:=f.live (i-2) (by omega)
     simpa only [show i-2+1=i-1 by omega] using a
   have targetValue:s.basis target=bExpected L origin.basis i:=by
     have a:=f.live (i-1) (by omega)
     simpa only [show i-1+1=i by omega] using a
   rw [eraseCorrectionCarry,if_neg h1]
   change run (xorWindow (rawSources L (i-1)) tmp
     (mappedEraseCarry (correction L (i-1)) tmp cin target)) m s=_
   apply xorWindow_write _ tmp target _ awayTemp aq tt
   intro r
   apply mappedEraseCarry_correct (correction L (i-1)) tmp cin target nd optAway
   have bm:(correction L (i-1)).value
       (writeBit s.basis tmp (s.basis tmp ^^ parity (rawSources L (i-1)) s.basis))=
       (correction L (i-1)).value origin.basis := by
     apply correction_value_same L hn (i-1)
     intro q hq
     have nq:q≠tmp:=fun e=>hq (e ▸ r_mem L hw 255 (by omega))
     simpa [writeBit,nq] using f.outside q hq
   rw [bm]
   simp only [writeBit,Function.update_of_ne (Ne.symm tt),Function.update_of_ne (Ne.symm tc),
     Function.update_self,tempZero,Bool.false_xor,targetValue,cinValue,rawSame]
   simpa only [h1,ite_false] using graph i hlo hi
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Front
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run normalize biasCompute

def front (L : DecoderLayout) : Program :=
 normalize L ++ ([.CX (L.R 0) L.h,.CX (L.Y 0) L.h] ++ biasCompute L)

def frontBasis (L : DecoderLayout) (b : BasisState) : BasisState :=
 let n:=complementBasis (L.Y 255) (L.y.take 255++L.r) b
 writeBit (writeBit n L.h (n L.h ^^ n (L.R 0) ^^ n (L.Y 0))) L.bias
   (n L.bias ^^ (n (L.Y 255) && !n L.sigma))

theorem front_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (front L) m s=⟨s.phase,frontBasis L s.basis⟩ := by
 have hy:L.h≠L.Y 0:=fun e=>flag_y_away L hn _ (by simp) (e ▸ y_mem L hw 0 (by omega))
 have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ r_mem L hw 0 (by omega))
 have hh : [L.sigma,L.h,L.bias].Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have c:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append] at c
   omega
 have hs:L.sigma≠L.h := fun e=>(List.nodup_cons.mp hh).1 (by simp[e])
 have hb:L.bias≠L.h := fun e=>(List.nodup_cons.mp (List.nodup_cons.mp hh).2).1 (by simp[e])
 have htop:L.Y 255≠L.h:=fun e=>flag_y_away L hn _ (by simp) (e.symm ▸ y_mem L hw 255 (by omega))
 let n : State:=⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩
 let u : State:=⟨s.phase,writeBit n.basis L.h (n.basis L.h ^^ n.basis (L.R 0) ^^ n.basis (L.Y 0))⟩
 have middle (r : List Bool) : run [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] r n=u := by
   simp only [run]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=L.h
   · subst q;simp [u,n,writeBit,Ne.symm hy]
   · simp [u,n,writeBit,eq]
 have last (r : List Bool) : run (biasCompute L) r u=⟨s.phase,frontBasis L s.basis⟩ := by
   rw [biasCompute_run L hw hn]
   simp only [u,n,frontBasis,writeBit,Function.update_of_ne hb,Function.update_of_ne htop,Function.update_of_ne hs]
 have result:=run_three_states (normalize L) [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] (biasCompute L)
   (fun a d=>a=s → d=⟨s.phase,frontBasis L s.basis⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [normalize_run L hw hn] at hab
     change n=b at hab
     subst b
     rw [middle] at hbc
     subst c
     exact hcd.symm.trans (last m3)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CopySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem zip_copy (ys rs : List Wire) :
 (ys.zip rs).map (fun q=>Instr.CX q.1 q.2)=copyRegister none ys rs := by
 induction ys generalizing rs with
 |nil=>cases rs <;>rfl
 |cons y ys ih=>cases rs with
   |nil=>rfl
   |cons r rs=>simp only [List.zip_cons_cons,List.map_cons,copyRegister,copyGate,List.singleton_append];rw[ih]

theorem yr_nodup (L : DecoderLayout) (hn : L.wires.Nodup) : (L.y++L.r).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem copySource_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) :
 (run (copySource L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (copySource L) m s).basis q=s.basis q) ∧
 regValue L.r (run (copySource L) m s).basis=regValue L.r s.basis ^^^ regValue L.y s.basis := by
 rw [copySource,zip_copy]
 simpa only [copyValue] using copyRegister_correct none L.y L.r (hw.1.trans hw.2.1.symm)
   (yr_nodup L hn) (by simp) s m

theorem complementBasis_value (control : Wire) (xs : List Wire) (b : BasisState) :
 regValue xs (complementBasis control xs b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 cases hb:b control
 · apply regValue_congr
   intro q hq
   simp [complementBasis,hb,hq]
 · rw [regValue_congr xs _ (fun q=>!b q) (by intro q hq;simp[complementBasis,hb,hq])]
   exact regValue_complement xs b
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flags_nd (L : DecoderLayout) (hn : L.wires.Nodup) : [L.sigma,L.h,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have c:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at c
 omega

theorem flags_bank_away (L : DecoderLayout) (hn : L.wires.Nodup) (f : Wire)
 (hf : f=L.h ∨ f=L.bias) (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) : q≠f := by
 intro eq
 subst q
 rcases hq with hy|hr|hc
 · exact flag_y_away L hn f (by rcases hf with rfl|rfl <;>simp) hy
 · exact source_r_away L hn f (by rcases hf with rfl|rfl <;>tauto) hr
 · exact carry_source_away L hn f (by rcases hf with rfl|rfl <;>tauto) hc

theorem front_on_banks (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) :
 frontBasis L b q=complementBasis (L.Y 255) (L.y.take 255++L.r) b q := by
 have qh:=flags_bank_away L hn L.h (Or.inl rfl) q hq
 have qb:=flags_bank_away L hn L.bias (Or.inr rfl) q hq
 simp [frontBasis,writeBit,qh,qb]

theorem normalized_flag (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (f : Wire) (hf:f∈[L.sigma,L.h,L.bias]) :
 complementBasis (L.Y 255) (L.y.take 255++L.r) b f=b f := by
 have ya:=flag_y_away L hn f hf
 have ra:f∉L.r:=by
   simp only[List.mem_cons,List.not_mem_nil,or_false] at hf
   apply source_r_away L hn f
   rcases hf with rfl|rfl|rfl <;>tauto
 simp [complementBasis,show f∉L.y.take 255 from fun h=>ya (List.mem_of_mem_take h),ra]

theorem front_source_sigma (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState) :
 frontBasis L b L.sigma=b L.sigma := by
 have nd:=flags_nd L hn
 have sh:L.sigma≠L.h:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 have sb:L.sigma≠L.bias:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne sh,Function.update_of_ne sb]
 exact normalized_flag L hn b L.sigma (by simp)

theorem front_bias (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.bias=false) :
 frontBasis L b L.bias=(b (L.Y 255) && !b L.sigma) := by
 have norm:=normalize_nd L hw hn
 simp only[frontBasis,writeBit,Function.update_self]
 rw[normalized_flag L hn b L.bias (by simp),normalized_flag L hn b L.sigma (by simp)]
 simp [complementBasis,norm.2,clean]

theorem front_h (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.h=false) :
 frontBasis L b L.h=
  (complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.R 0) ^^
   complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.Y 0)) := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne hb,Function.update_self]
 rw[normalized_flag L hn b L.h (by simp),clean,Bool.false_xor]

theorem front_carry_clean (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : ∀q∈L.carry,b q=false) : ∀q∈L.carry,frontBasis L b q=false := by
 intro q hq
 rw[front_on_banks L hn b q (Or.inr (Or.inr hq))]
 have qy:q∉L.y := by
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hq
 have qr:q∉L.r:=source_r_away L hn q (Or.inr (Or.inl hq))
 simp [complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),qr,clean q hq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontValues
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem complement_subset_value (control : Wire) (xs region : List Wire)
 (sub : ∀q∈xs,q∈region) (b : BasisState) :
 regValue xs (complementBasis control region b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 rw[regValue_congr xs _ (complementBasis control xs b) (by intro q hq;simp[complementBasis,hq,sub q hq])]
 exact complementBasis_value control xs b

theorem getD_testBit (xs : List Wire) (i : Nat) (b : BasisState) (hi:i<xs.length) :
 b (xs.getD i 0)=Nat.testBit (regValue xs b) i := by
 have h:=regValue_bit xs i 0 b hi
 rw[Nat.testBit_eq_decide_div_mod_eq]
 cases eq:b (xs.getD i 0) <;> simp only[eq,Bool.toNat_false,Bool.toNat_true] at h ⊢ <;>
   simp[←h]

theorem front_low_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue (L.y.take 255) (frontBasis L b)=
 if b (L.Y 255) then 2^255-1-regValue L.y b%2^255 else regValue L.y b%2^255 := by
 rw[regValue_congr (L.y.take 255) _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inl (List.mem_of_mem_take hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_left _ hq)]
 have len:=hw.1
 rw[CuccaroStreamedSquareWideLayout.regValue_take_mod L.y 255 (by omega) b]
 simp only[List.length_take,len,Nat.min_eq_left (by omega : 255≤256)]

theorem front_r_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue L.r (frontBasis L b)=
 if b (L.Y 255) then 2^256-1-regValue L.r b else regValue L.r b := by
 rw[regValue_congr L.r _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inr (Or.inl hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_right _ hq)]
 rw[hw.2.1]

theorem front_h_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean:b L.h=false) :
 frontBasis L b L.h=
   (Nat.testBit (regValue L.r (frontBasis L b)) 0 ^^
    Nat.testBit (regValue (L.y.take 255) (frontBasis L b)) 0) := by
 rw[front_h L hn b clean]
 have r:=getD_testBit L.r 0 (frontBasis L b) (by have len:=hw.2.1;omega)
 have y:=getD_testBit (L.y.take 255) 0 (frontBasis L b) (by simp[hw.1])
 have yget:(L.y.take 255).getD 0 0=L.Y 0 :=by
   cases eq:L.y with
   |nil=>have len:=hw.1;simp[eq] at len
   |cons a as=>simp[DecoderLayout.Y,eq]
 rw[yget] at y
 change frontBasis L b (L.R 0)=_ at r
 rw[front_on_banks L hn b (L.R 0) (Or.inr (Or.inl (r_mem L hw 0 (by omega))))] at r
 rw[front_on_banks L hn b (L.Y 0) (Or.inl (y_mem L hw 0 (by omega)))] at y
 rw[r,y]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.TerminalGraph
open Secp256k1

def M : Int:=2^256
def C : Int:=2^32+977
def Q : Int:=((p:Int)-1)/2

theorem constants : (p:Int)=M-C ∧ M%2=0 ∧ C%2=1 ∧ C%4=1 ∧ C%4<2 ∧ Q%3=0 := by
  norm_num [M,C,Q,p]

/-- One's-complement normalization leaves only a nonnegative single-bit modular correction. -/
theorem normalized_equation (z r j sigma sy : Int)
    (eq : r=(3-2*sigma)*z-j*(p:Int))
    (sg : z=(1-2*sy)*((if sy=0 then z else -z-1)+sy))
    (hs : sy=0 ∨ sy=1) :
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    let h:=(1-2*sy)*j
    t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int) := by
  rcases hs with rfl|rfl <;> dsimp <;> simp [eq] <;> ring


theorem positive_correction (y t h sigma sy : Int)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (3-2*sigma)*y+2*(1-sigma)*sy+h*C=t+h*M := by
  rw [constants.1] at eq
  linear_combination -eq

/-- The quotient flag can be copied from the low parity, without a wide comparator. -/
theorem quotient_low (y t h sigma sy : Int)
    (hs : sigma=0 ∨ sigma=1) (hh : h=0 ∨ h=1)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (t-y)%2=h := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [p] at eq ⊢ <;> omega

/-- A paid comparator can clear the quotient after the graph carries are erased. -/
theorem quotient_threshold (y t h sy : Int)
    (hy : 0≤y) (hs : sy=0 ∨ sy=1) (hh : h=0 ∨ h=1)
    (eq : t=3*y+2*sy-h*(p:Int)) (bounds : -Q-sy≤t ∧ t≤Q) :
    h=1 ↔ Q/3<y ∨ (sy=1 ∧ y=Q/3) := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [Q,p] at eq bounds ⊢ <;> omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FpQuotient
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem center_triple (z : Int) (hz : Centered z) :
    centerFp (3*(z:Fp)) =
      if q<3*z then 3*z-(p:Int) else if 3*z< -q then 3*z+(p:Int) else 3*z := by
  have hp := BalancedField.constants
  have pc : ((p:Int):Fp)=0 := by simp
  unfold Centered at hz
  split_ifs with hi hlo
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_sub,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_add,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp

/-- The signed modular quotient has one bit of magnitude and follows the source sign. -/
theorem quotient_exists (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    ∃ j : Int, r=(if sigma then 1 else 3)*z-j*(p:Int) ∧
      -1≤j ∧ j≤1 ∧ (0≤z → 0≤j) ∧ (z<0 → j≤0) ∧ (sigma=true → j=0) := by
  have hz:=centerFp_bounds Y
  have hp:=BalancedField.constants
  cases sigma
  · dsimp
    have eq:=center_triple (centerFp Y) hz
    rw [centerFp_cast] at eq
    unfold Centered at hz
    by_cases hi : q<3*centerFp Y
    · refine ⟨1,?_,by omega,by omega,?_,?_,by simp⟩
      · simpa [hi] using eq
      · intro _; omega
      · intro hn; omega
    · by_cases hlo : 3*centerFp Y< -q
      · refine ⟨-1,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro hn; omega
        · intro _; omega
      · refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro _; omega
        · intro _; omega
  · dsimp; refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
    · simp
    · intro _; omega
    · intro _; omega

/-- Actual Fp inputs supply every signed/range premise of the checked decoder algebra. -/
theorem normalized_bridge (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    let sy:Int:=if z<0 then 1 else 0
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    ∃ h : Int, (h=0 ∨ h=1) ∧ 0≤y ∧ -TerminalGraph.Q-sy≤t ∧ t≤TerminalGraph.Q ∧
      t=(3-2*(if sigma then 1 else 0))*y+
        2*(1-(if sigma then 1 else 0))*sy-h*(p:Int) ∧ (sigma=true → h=0) := by
  dsimp
  obtain ⟨j,he,hlo,hhi,hpos,hneg,hzero⟩:=quotient_exists Y sigma
  have hz:=centerFp_bounds Y
  have hr:=centerFp_bounds ((if sigma then 1 else 3)*Y)
  have he' : centerFp ((if sigma then 1 else 3)*Y)=
      (3-2*(if sigma then 1 else 0 : Int))*centerFp Y-j*(p:Int) := by
    cases sigma <;> simpa using he
  by_cases hs : centerFp Y<0
  · have sg : centerFp Y=(1-2*(1:Int))*(-centerFp Y-1+1) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 1 he' sg (Or.inr rfl)
    simp only [show ¬(1:Int)=0 by omega,if_false] at hn
    unfold Centered at hz hr
    refine ⟨-j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hneg hs; omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · intro ht; rw [hzero ht]; omega
  · have sg : centerFp Y=(1-2*(0:Int))*(centerFp Y+0) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 0 he' sg (Or.inl rfl)
    simp only [mul_zero,sub_zero,if_pos rfl,zero_add,one_mul] at hn
    unfold Centered at hz hr
    refine ⟨j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hpos (by omega); omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · exact hzero
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT WordBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem normalized_source_bounds (Y : Fp) :
    0≤(if centerFp Y<0 then -centerFp Y-1 else centerFp Y) ∧
    (if centerFp Y<0 then -centerFp Y-1 else centerFp Y)≤TerminalGraph.Q := by
  have h:=centerFp_bounds Y
  unfold Centered at h
  have eq : q=TerminalGraph.Q := rfl
  split_ifs <;> omega

theorem centerWord_msb (Y : Fp) :
    (centerWord Y).testBit 255=decide (centerFp Y<0) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hs:=centerWord_sign Y
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : centerWord Y / 2^255 < 2 := by
    norm_num only [Nat.reducePow] at hb ⊢
    omega
  rw [Nat.mod_eq_of_lt hd]
  have eq : centerWord Y / 2^255 = 1 ↔ centerFp Y<0 := by
    norm_num only [Nat.reducePow] at hb hs ⊢
    omega
  simp only [eq]

/-- Complementing a complete canonical256-bit word is exact one's complement. -/
theorem full_complement_word (Y : Fp) :
    2^256-1-centerWord Y=encodeWord 256 (-centerFp Y-1) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hc : 2^256-1-centerWord Y<2^256 := by omega
  have dec : signedDecode 256 (2^256-1-centerWord Y)= -centerFp Y-1 := by
    unfold signedDecode at hd ⊢
    norm_num only [Nat.reduceSub,Nat.reducePow] at hd hb ⊢
    split_ifs at hd ⊢ <;> omega
  rw [←dec,encode_decodeWord 256 _ hc]

def lowNormalize (w : Nat) (sign : Bool) : Nat :=
  if sign then 2^255+(2^255-1-w%2^255) else w

/-- Low255 complement retains the original source MSB and exposes the nonnegative magnitude. -/
theorem low_complement_word (Y : Fp) :
    lowNormalize (centerWord Y) (decide (centerFp Y<0))=
      (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat+
        (decide (centerFp Y<0)).toNat*2^255 := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hs:=centerWord_sign Y
  have hz:=centerFp_bounds Y
  unfold Centered at hz
  have hq:=BalancedField.constants
  unfold lowNormalize signedDecode at *
  norm_num only [Nat.reduceSub,Nat.reducePow] at *
  by_cases hn : centerFp Y<0
  · have ge : 2^255≤centerWord Y := hs.mpr hn
    norm_num only [Nat.reducePow] at ge
    have hdec : ¬centerWord Y<57896044618658097711785492504343953926634992332820282019728792003956564819968 := by omega
    simp only [if_neg hdec] at hd
    have pos : 0≤ -centerFp Y-1 := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
  · have lt : centerWord Y<2^255 := by have :=hs.not.mpr hn;omega
    norm_num only [Nat.reducePow] at lt
    simp only [if_pos lt] at hd
    have pos : 0≤centerFp Y := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT FrontMath
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem encoded_positive (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 encodeWord 256 t=
 ((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 := by
 have corr:=TerminalGraph.positive_correction (y:Int) t (h.toNat:Int) (sigma.toNat:Int) (sy.toNat:Int) eq
 apply Int.ofNat_injective
 change (encodeWord 256 t:Int)=((((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 : Nat):Int)
 rw [encodeWord_cast,Int.natCast_emod]
 cases sigma <;> cases sy <;> cases h <;>
   norm_num [TerminalGraph.C,TerminalGraph.M] at corr ⊢ <;> omega

theorem encoded_parity (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 (Nat.testBit (encodeWord 256 t) 0 ^^ Nat.testBit y 0)=h := by
 have e:=encoded_positive y sigma sy h t eq
 rw [e,Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
 simp only [Nat.pow_zero,Nat.div_one]
 have parityEq : (((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256)%2=(y+h.toNat)%2 := by
   cases sigma <;> cases sy <;> cases h <;> norm_num at * <;> omega
 rw [parityEq]
 cases h <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
 · simp
 · have bound : y%2<2:=Nat.mod_lt _ (by omega)
   by_cases h0:y%2=0
   · have h1 : (y+1)%2=1:=by omega
     simp [h0,h1]
   · have h1 : y%2=1:=by omega
     have h2 : (y+1)%2=0:=by omega
     simp [h1,h2]
def frontY (Y : Fp) : Nat := (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat

def frontR (Y : Fp) (sigma : Bool) : Nat :=
 if centerFp Y<0 then 2^256-1-centerWord ((if sigma then 1 else 3)*Y)
 else centerWord ((if sigma then 1 else 3)*Y)

def frontH (Y : Fp) (sigma : Bool) : Bool := Nat.testBit (frontR Y sigma) 0 ^^ Nat.testBit (frontY Y) 0

theorem actual_front_equations (Y : Fp) (sigma : Bool) :
 frontR Y sigma=((if sigma then frontY Y else 3*frontY Y)+
  2*(decide (centerFp Y<0) && !sigma).toNat+(frontH Y sigma).toNat*(2^32+977))%2^256 ∧
 frontH Y sigma=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!decide (centerFp Y<0)).toNat)) := by
 let sy:=decide (centerFp Y<0)
 let yi:=if centerFp Y<0 then -centerFp Y-1 else centerFp Y
 let ti:=if centerFp Y<0 then -centerFp ((if sigma then 1 else 3)*Y)-1 else centerFp ((if sigma then 1 else 3)*Y)
 have norm : ∃h:Int,(h=0 ∨ h=1) ∧ 0≤yi ∧ -TerminalGraph.Q-(sy.toNat:Int)≤ti ∧ ti≤TerminalGraph.Q ∧
   ti=(3-2*(sigma.toNat:Int))*yi+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-h*(p:Int) ∧ (sigma=true→h=0) := by
   have nn:=normalized_bridge Y sigma
   cases sigma <;> by_cases hs:centerFp Y<0 <;> simpa [sy,yi,ti,hs] using nn
 obtain ⟨h,hh,hy,hlo,hhi,he,hzero⟩:=norm
 let hb:=decide (h=1)
 have hc : (hb.toNat:Int)=h := by
   rcases hh with h0|h1
   · simp [hb,h0]
   · simp [hb,h1]
 have yc : (frontY Y:Int)=yi := Int.toNat_of_nonneg hy
 have he' : ti=(3-2*(sigma.toNat:Int))*(frontY Y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(hb.toNat:Int)*(p:Int) := by rw [yc,hc];exact he
 have rwrd : frontR Y sigma=encodeWord 256 ti := by
   by_cases hs:centerFp Y<0
   · simpa [frontR,ti,hs] using full_complement_word ((if sigma then 1 else 3)*Y)
   · simp [frontR,ti,hs,centerWord]
 have par : frontH Y sigma=hb := by
   unfold frontH
   rw [rwrd]
   exact encoded_parity _ _ _ _ _ he'
 constructor
 · rw [par,rwrd]
   exact encoded_positive _ _ _ _ _ he'
 · rw [par]
   have threshold : hb=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!sy).toNat)) := by
     cases eqs:sigma with
     | true =>
       have hz:=hzero eqs
       simp [hb,hz]
     | false =>
       have hef : ti=3*yi+2*(sy.toNat:Int)-h*(p:Int) := by simpa [eqs] using he
       have hs : (sy.toNat:Int)=0 ∨ (sy.toNat:Int)=1 := by cases sy <;> simp
       have ht:=TerminalGraph.quotient_threshold yi ti h (sy.toNat:Int) hy hs hh hef ⟨hlo,hhi⟩
       have yn : 0≤(frontY Y:Int):=by omega
       norm_num [TerminalGraph.Q,p] at ht ⊢
       dsimp [hb]
       by_cases sign:sy=true
       · simp [sign] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
       · have sf:sy=false:=Bool.eq_false_iff.mpr sign
         simp [sf] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
   simpa [sy] using threshold
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT ActualFront
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField TerminalGraphFp

theorem normalized_low_word (Y : Fp) :
 (if decide (centerFp Y<0) then 2^255-1-centerWord Y%2^255 else centerWord Y%2^255)=frontY Y := by
 have h:=low_complement_word Y
 have hs:=centerWord_sign Y
 by_cases neg:centerFp Y<0
 · simp [lowNormalize,frontY,neg] at h ⊢
   omega
 · have lt:centerWord Y<2^255:=by have nn:=hs.not.mpr neg;omega
   simp [lowNormalize,frontY,neg] at h ⊢
   simpa only[Nat.reducePow] using (Nat.mod_eq_of_lt lt).trans h

theorem actual_front_values (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue (L.y.take 255) f=frontY Y ∧ regValue L.r f=frontR Y sigma ∧
 f L.h=frontH Y sigma ∧ f L.bias=(decide (centerFp Y<0) && !sigma) ∧
 f L.sigma=sigma ∧ f (L.Y 255)=decide (centerFp Y<0) := by
 have msb:b (L.Y 255)=decide (centerFp Y<0) := by
   have g:=getD_testBit L.y 255 b (by have len:=hw.1;omega)
   rw[ys,centerWord_msb] at g
   exact g
 have fy:regValue (L.y.take 255) (frontBasis L b)=frontY Y := by
   rw[front_low_value L hw hn,ys,msb]
   exact normalized_low_word Y
 have fr:regValue L.r (frontBasis L b)=frontR Y sigma := by
   rw[front_r_value L hw hn,rs,msb]
   simp only[frontR]
   split_ifs <;>simp_all
 have fh:frontBasis L b L.h=frontH Y sigma := by
   rw[front_h_value L hw hn b hc,fy,fr]
   rfl
 refine ⟨fy,fr,fh,?_,?_,?_⟩
 · rw[front_bias L hw hn b bc,msb,sig]
 · rw[front_source_sigma L hn b,sig]
 · rw[front_on_banks L hn b (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))]
   simp only[complementBasis,if_neg (normalize_nd L hw hn).2,msb]

theorem actual_front_scalar (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue L.r f=((if f L.sigma then regValue (L.y.take 255) f else 3*regValue (L.y.take 255) f)+
   2*(f L.bias).toNat+(f L.h).toNat*(2^32+977))%2^256 ∧
 f L.h=(!f L.sigma && !(decide (regValue (L.y.take 255) f<((p-1)/2)/3+(!f (L.Y 255)).toNat))) := by
 have v:=actual_front_values L hw hn b Y sigma ys rs sig hc bc
 dsimp only
 rw[v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2]
 exact actual_front_equations Y sigma
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddCarrySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aStepValue (L : DecoderLayout) (s : BasisState) (i : Nat) : Bool:=
 if i=0 then carryBit false (s L.sigma) (s (L.Y 0) ^^ s L.sigma)
 else carryBit (s (L.Y (i-1))) (s (L.Y i) ^^ s L.sigma) (s (L.A (i-1)))

theorem step_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    [L.Y i,L.A (i-1),L.A i].Nodup := by
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
  not_or,not_false_eq_true,and_true]
 exact ⟨⟨y_ne_a L hw hn i (i-1) (by omega) (by omega),
   y_ne_a L hw hn i i (by omega) hi⟩,
   carry_ne_carry L hw hn (i-1) i (by omega) hi (by omega)⟩

theorem step_source_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    ∀q∈(some (L.Y (i-1))),q∉[L.Y i,L.A (i-1),L.A i] := by
 intro q hq
 have eq:L.Y (i-1)=q:=by simpa using hq
 subst q
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
 exact ⟨y_ne_y L hw hn (i-1) i (by omega) (by omega) (by omega),
   y_ne_a L hw hn (i-1) (i-1) (by omega) (by omega),
   y_ne_a L hw hn (i-1) i (by omega) hi⟩

theorem addCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool) :
    run (addCarry L i) m s=
      ⟨s.phase,writeBit s.basis (L.A i) (s.basis (L.A i) ^^ aStepValue L s.basis i)⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   change run (cxWindow L.sigma (L.Y 0) [.CCX L.sigma (L.Y 0) (L.A 0)]) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   simp [run,cxBasis,writeBit,sy,Ne.symm sy,Ne.symm sa,Ne.symm ya,aStepValue,carryBit]
 · have h:=windowMajority_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m
   simpa only [addCarry,h0,ite_false,cxWindow,mappedMajority,Bool.false_eq_true,
     aStepValue,MappedBit.value,Bool.xor_false,Bool.false_xor,Option.map_some,Option.getD_some] using h

theorem eraseAddCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool)
    (known : s.basis (L.A i)=aStepValue L s.basis i) :
    run (eraseAddCarry L i) m s=⟨s.phase,writeBit s.basis (L.A i) false⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   have nd:[L.sigma,L.Y 0,L.A 0].Nodup:=by simp [sy,sa,ya]
   change run (cxWindow L.sigma (L.Y 0)
     (mappedEraseCarry ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0))) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   apply mappedEraseCarry_correct ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0) nd (by simp)
   simpa [cxBasis,writeBit,sy,Ne.symm sy,Ne.symm ya,MappedBit.value,aStepValue] using known
 · have h:=windowErase_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m (by simpa [aStepValue,h0,MappedBit.value] using known)
   simpa only [eraseAddCarry,h0,ite_false,cxWindow,mappedEraseCarry,Bool.false_eq_true] using h
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddChain
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aExpected (L : DecoderLayout) (origin : BasisState) : Nat→Bool
 | 0 => carryBit false (origin L.sigma) (origin (L.Y 0) ^^ origin L.sigma)
 | j+1 => carryBit (origin (L.Y j)) (origin (L.Y (j+1)) ^^ origin L.sigma) (aExpected L origin j)

structure AddFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 sigma : s.basis L.sigma=origin.basis L.sigma
 source : ∀ i, i<256 → s.basis (L.Y i)=origin.basis (L.Y i)
 computed : ∀ i, i< nDone → s.basis (L.A i)=aExpected L origin.basis i
 clean : ∀ i, nDone≤ i → i<255 → s.basis (L.A i)=false

theorem addFrame_initial (L : DecoderLayout) (s : State)
 (clean : ∀ i, i<255 → s.basis (L.A i)=false) : AddFrame L s 0 s := by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_,?_⟩
 · intro i hi;omega
 · intro i _ hi;exact clean i hi

theorem value_expected (L : DecoderLayout) (origin s : State) (nDone i : Nat)
 (f : AddFrame L origin nDone s) (hi : i<255) (hd : i≤nDone) :
 aStepValue L s.basis i=aExpected L origin.basis i := by
 by_cases h0:i=0
 · subst i
   simp only [aStepValue,ite_true,aExpected]
   rw [f.sigma,f.source 0 (by omega)]
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   simp only [aStepValue,Nat.add_sub_cancel,show ¬j+1=0 by omega,ite_false,aExpected]
   rw [f.source j (by omega),f.source (j+1) (by omega),f.sigma,f.computed j (by omega)]

theorem addFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin i s) (m : List Bool) :
 AddFrame L origin (i+1) (run (addCarry L i) m s) := by
 have val:=value_expected L origin s i i f hi (le_refl _)
 have zero:=f.clean i (le_refl _) hi
 rw [addCarry_run L hw hn i hi s m,zero,val,Bool.false_xor]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i (by omega) hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   have ne:=carry_ne_carry L hw hn j i hj hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem addFrame_erase_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin (i+1) s) (m : List Bool) :
 AddFrame L origin i (run (eraseAddCarry L i) m s) := by
 have val:=value_expected L origin s (i+1) i f hi (by omega)
 have known:s.basis (L.A i)=aStepValue L s.basis i:=(f.computed i (by omega)).trans val.symm
 rw [eraseAddCarry_run L hw hn i hi s m known]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   have ne:=carry_ne_carry L hw hn j i (by omega) hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i hj hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem add_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 AddFrame L origin n (run ((List.range n).flatMap (addCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply addFrame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

theorem add_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n≤255) (s : State) (f : AddFrame L origin n s) (m : List Bool) :
 AddFrame L origin 0 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply ih (by omega)
   exact addFrame_erase_step L hw hn origin s n (by omega) f _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddOutside
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry

theorem add_forward_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (n : Nat) (bound : n ≤ 255) (s : State) (m : List Bool) (q : Wire)
 (away : q ∉ L.carry) :
 (run ((List.range n).flatMap (addCarry L)) m s).basis q=s.basis q := by
 induction n generalizing m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [addCarry_run L hw hn n (by omega)]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
   exact ih (by omega) _

theorem add_reverse_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n ≤ 255) (s : State)
 (f : AddFrame L origin n s) (m : List Bool) (q : Wire) (away : q ∉ L.carry) :
 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s).basis q=s.basis q := by
 induction n generalizing s m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   have f' := addFrame_erase_step L hw hn origin s n (by omega) f m
   rw [ih (by omega) _ f' _]
   have val:=value_expected L origin s (n+1) n f (by omega) (by omega)
   have known:s.basis (L.A n)=aStepValue L s.basis n := (f.computed n (by omega)).trans val.symm
   rw [eraseAddCarry_run L hw hn n (by omega) s m known]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamReverse
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run xorList streamCarry eraseCorrectionCarry

theorem stream_to_erase (L : DecoderLayout) (origin s : State)
 (f : StreamFrame L origin 255 s) : EraseBFrame L origin 255 s := by
 refine ⟨f.phase,f.outside,f.stored,?_⟩
 intro j hj hbound
 have eq:j=255:=by omega
 subst j
 exact f.current

theorem eraseBFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 EraseBFrame L origin (i-1) (run (eraseCorrectionCarry L i) m s) := by
 rw [eraseCorrectionCarry_run L hw hn origin s i hlo hi graph f m]
 refine ⟨f.phase,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R (i-1):=fun e=>hq (e ▸ r_mem L hw (i-1) (by omega))
   simpa only [writeBit,Function.update_of_ne ne] using f.outside q hq
 · intro j hj
   have ne:=r_ne_r L hw hn j (i-1) (by omega) (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.live j (by omega)
 · intro j hji hj
   by_cases eq:j=i-1
   · subst j;simp [writeBit]
   · have ne:=r_ne_r L hw hn j (i-1) hj (by omega) eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem eraseB_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis) (n : Nat) (bound : n ≤ 255)
 (s : State) (f : EraseBFrame L origin n s) (m : List Bool) :
 EraseBFrame L origin 0 (run ((List.range' 1 n).reverse.flatMap (eraseCorrectionCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take,Nat.add_comm 1 n]
   apply ih (by omega)
   have a:=eraseBFrame_step L hw hn origin s (n+1) (by omega) bound graph f
     m
   simpa only [Nat.add_sub_cancel] using a

def bBlock (L : DecoderLayout) : Program:=
 xorList (bSources L 0) (L.R 0)++(List.range' 1 255).flatMap (streamCarry L)++
   (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)

theorem bBlock_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) (m : List Bool) :
 (run (bBlock L) m origin).phase=origin.phase ∧
 (∀q,q∉L.r → (run (bBlock L) m origin).basis q=origin.basis q) ∧
 ∀i,i<256 → (run (bBlock L) m origin).basis (L.R i)=false := by
 have f : EraseBFrame L origin 0 (run (bBlock L) m origin) := by
   rw [bBlock,List.append_assoc,run_append,run_take]
   rw [run_append,run_take]
   apply eraseB_reverse_frame L hw hn origin graph 255 (le_refl _)
   apply stream_to_erase
   apply stream_forward_frame L hw hn origin _ _ 255 (le_refl _)
   exact stream_initial L hw hn origin _ low
 exact ⟨f.phase,f.outside,fun i hi=>f.clean i (by omega) hi⟩
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CoreStages
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock

def aProgram (L : DecoderLayout) : Program := (List.range 255).flatMap (addCarry L)
def eraseAProgram (L : DecoderLayout) : Program := (List.range 255).reverse.flatMap (eraseAddCarry L)

theorem aProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false) (m : List Bool) :
 AddFrame L s 255 (run (aProgram L) m s) :=
 add_forward_frame L hw hn s s (addFrame_initial L s clean) 255 (le_refl _) m

theorem eraseAProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 255 s) (m : List Bool) :
 AddFrame L origin 0 (run (eraseAProgram L) m s) :=
 add_reverse_frame L hw hn origin 255 (le_refl _) s f m

attribute [local irreducible] aProgram eraseAProgram

theorem bBlock_addFrame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin a : State) (af : AddFrame L origin 255 a)
 (graph : BGraph L a.basis) (low : a.basis (L.R 0)=parity (bSources L 0) a.basis)
 (m : List Bool) : AddFrame L origin 255 (run (bBlock L) m a) := by
 have bc:=bBlock_correct L hw hn a graph low m
 refine ⟨bc.1.trans af.phase,?_,?_,?_,?_⟩
 · exact (bc.2.1 L.sigma (source_r_away L hn _ (by tauto))).trans af.sigma
 · intro i hi
   exact (bc.2.1 (L.Y i) (source_r_away L hn _ (Or.inl (y_mem L hw i hi)))).trans (af.source i hi)
 · intro i hi
   exact (bc.2.1 (L.A i) (source_r_away L hn _ (Or.inr (Or.inl (a_mem L hw i hi))))).trans (af.computed i hi)
 · intro i hi hb;omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalCarryMath
open Arithmetic

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sums : List Bool → List Bool → Bool → List Bool
  | a::as,b::bs,c => sumBit a b c::sums as bs (carryBit a b c)
  | _,_,_ => []

def carryAt : List Bool → List Bool → Bool → Nat → Bool
  | _,_,c,0 => c
  | a::as,b::bs,c,n+1 => carryAt as bs (carryBit a b c) n
  | _,_,_,_ => false

theorem sums_length (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    (sums A B c).length=A.length := by
  induction A generalizing B c with
  | nil => cases B <;> simp_all [sums]
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs => simp only [sums,List.length_cons];rw [ih bs _ (by simpa using hlen)]

theorem sums_value (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    value (sums A B c)=(value A+value B+c.toNat)%2^A.length := by
  induction A generalizing B c with
  | nil => cases B with
    | nil => cases c <;> decide
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      simp only [sums,value,List.length_cons]
      rw [ih bs _ (by simpa using hlen)]
      exact sum_value_step a b c (value as) (value bs) as.length

theorem value_injective (A B : List Bool) (hlen : A.length=B.length)
    (hv : value A=value B) : A=B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      have head : a=b := by
        cases a <;> cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst b
      have tail : value as=value bs := by simp only [value] at hv;omega
      rw [ih bs (by simpa using hlen) tail]

theorem graph_eq_sums (A B R : List Bool) (c : Bool)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) : R=sums A B c :=
  value_injective R _ (hr.trans (sums_length A B c hlen).symm)
    (hv.trans (sums_value A B c hlen).symm)

theorem sums_at (A B : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hi : i<A.length) :
    (sums A B c).getD i false=
      sumBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
  induction i generalizing A B c with
  | zero =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs => rfl
  | succ i ih =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs =>
        simpa only [sums,carryAt,List.getD_cons_succ] using
          ih as bs (carryBit a b c) (by simpa using hlen) (by simpa using hi)

theorem graph_carry_extract (A B R : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) (hi : i<A.length) :
    carryAt A B c i=R.getD i false ^^ A.getD i false ^^ B.getD i false := by
  rw [graph_eq_sums A B R c hlen hr hv,sums_at A B c i hlen hi]
  cases A.getD i false <;> cases B.getD i false <;> cases carryAt A B c i <;> decide
end ECDSAAdd.Entrant.TerminalCarryMath


-- TERMINAL GRAPH COMPONENT GraphValues
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

def bitVector (n : Nat) (f : Nat → Bool) : List Bool := (List.range n).map f
@[simp] theorem bitVector_length (n : Nat) (f : Nat → Bool) : (bitVector n f).length=n := by simp [bitVector]
theorem bitVector_get (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i<n) :
 (bitVector n f).getD i false=f i := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi)]
 simp [bitVector]

theorem carryAt_next (A B : List Bool) (c : Bool) (i : Nat)
 (ha : i<A.length) (hb : i<B.length) :
 carryAt A B c (i+1)=carryBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
 induction i generalizing A B c with
 | zero => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simp [carryAt]
 | succ i ih => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simpa only [carryAt,List.getD_cons_succ] using ih as bs (carryBit a b c) (by simpa using ha) (by simpa using hb)

theorem correctionSources_parity (L : DecoderLayout) (i : Nat) (s : BasisState) :
 parity (correctionSources L i) s=(correction L i).value s := by
 unfold correctionSources correction
 split_ifs <;> simp [MappedBit.value,parity]

theorem parity_cat (xs ys : List Wire) (s : BasisState) :
 parity (xs++ys) s=(parity xs s ^^ parity ys s) := by
 induction xs with
 | nil => simp [parity]
 | cons x xs ih =>
   change (s x ^^ parity (xs++ys) s)=((s x ^^ parity xs s) ^^ parity ys s)
   rw [ih,Bool.xor_assoc]

def rawBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>parity (rawSources L i) s)
def correctionBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>(correction L i).value s)
def resultBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>s (L.R i))

theorem graph_of_bit_values (L : DecoderLayout) (s : BasisState)
 (hv : value (resultBits L s)=(value (rawBits L s)+value (correctionBits L s))%2^256) :
 BGraph L s ∧ s (L.R 0)=parity (bSources L 0) s := by
 let A:=rawBits L s
 let B:=correctionBits L s
 let R:=resultBits L s
 have la:A.length=256:=bitVector_length _ _
 have lb:B.length=256:=bitVector_length _ _
 have lr:R.length=256:=bitVector_length _ _
 have av (i : Nat) (hi : i<256) : A.getD i false=parity (rawSources L i) s:=bitVector_get _ _ _ hi
 have bv (i : Nat) (hi : i<256) : B.getD i false=(correction L i).value s:=bitVector_get _ _ _ hi
 have rv (i : Nat) (hi : i<256) : R.getD i false=s (L.R i):=bitVector_get _ _ _ hi
 have val : value R=(value A+value B+false.toNat)%2^A.length := by simpa [la] using hv
 have extract (i : Nat) (hi : i<256) : carryAt A B false i=bExpected L s i := by
   have old:=graph_carry_extract A B R false i (la.trans lb.symm) (lr.trans la.symm) val (by omega)
   have e : carryAt A B false i=(R.getD i false ^^ A.getD i false ^^ B.getD i false) := by
     cases hc:carryAt A B false i <;> cases hr:R.getD i false <;> cases ha:A.getD i false <;> cases hb:B.getD i false <;> simp_all
   rw [rv i hi,av i hi,bv i hi] at e
   rw [e]
   simp only [bExpected,bSources,parity_cat,correctionSources_parity,Bool.xor_assoc]
 constructor
 · intro i hl hi
   rw [←extract i (by omega)]
   have eq : i-1+1=i:=by omega
   have step:=carryAt_next A B false (i-1) (by omega) (by omega)
   rw [eq] at step
   rw [step]
   have prev : carryAt A B false (i-1)=(if i=1 then false else bExpected L s (i-1)) := by
     split_ifs with e
     · subst i;rfl
     · exact extract _ (by omega)
   rw [prev,av (i-1) (by omega),bv (i-1) (by omega)]
   cases (correction L (i-1)).value s <;> cases parity (rawSources L (i-1)) s <;> cases (if i=1 then false else bExpected L s (i-1)) <;> decide
 · have e:=sums_at A B false 0 (la.trans lb.symm) (by rw [la];omega)
   have eq:=graph_eq_sums A B R false (la.trans lb.symm) (lr.trans la.symm) val
   rw [←eq] at e
   rw [rv 0 (by omega),av 0 (by omega),bv 0 (by omega)] at e
   simpa [bSources,parity_cat,correctionSources_parity,sumBit,carryAt] using e
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphRaw
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

theorem value_append_bits (xs ys : List Bool) :
 value (xs++ys)=value xs+2^xs.length*value ys := by
 induction xs with
 | nil => simp [value]
 | cons x xs ih => simp only [List.cons_append,value,List.length_cons,ih,Nat.pow_succ];ring

theorem value_map_register (xs : List Wire) (s : BasisState) : value (xs.map s)=regValue xs s := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   change (s x).toNat+2*value (xs.map s)=(if s x then 1 else 0)+2*regValue xs s
   rw [ih];cases s x <;> rfl

theorem getD_map_valid {α β : Type} (xs : List α) (f : α→β) (d : α) (e : β) (i : Nat) (hi : i<xs.length) :
 (xs.map f).getD i e=f (xs.getD i d) := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
 simp

theorem bitVector_register (xs : List Wire) (s : BasisState) :
 bitVector xs.length (fun i=>s (xs.getD i 0))=xs.map s := by
 apply List.ext_getElem (by simp)
 intro i hi hj
 have bound:i<xs.length:=by simpa using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [bitVector_get _ _ _ bound,getD_map_valid xs s 0 false i bound]

theorem resultBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 value (resultBits L s)=regValue L.r s := by
 change value (bitVector 256 (fun i=>s (L.r.getD i 0)))=_
 rw [←hw.2.1,bitVector_register,value_map_register]

theorem complement_value (xs : List Bool) : value (xs.map not)=2^xs.length-1-value xs := by
 have hs : value (xs.map not)+value xs+1=2^xs.length := by
   induction xs with
   | nil => rfl
   | cons x xs ih => simp only [List.map_cons,value,List.length_cons,Nat.pow_succ];cases x <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] <;> omega
 omega

def lowBits (L : DecoderLayout) (s : BasisState) : List Bool := (L.y.take 255).map s

theorem lowBits_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) : (lowBits L s).length=255 := by simp [lowBits,hw.1]

theorem lowBits_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 (lowBits L s).getD i false=s (L.Y i) := by
 unfold lowBits DecoderLayout.Y
 rw [getD_map_valid _ s 0 false i (by simp [hw.1];omega)]
 rw [List.getD_eq_getElem _ _ (by simp [hw.1];omega),List.getD_eq_getElem _ _ (by rw [hw.1];omega)]
 simp [lowBits,DecoderLayout.Y]

def sourceA (L : DecoderLayout) (s : BasisState) : List Bool := false::lowBits L s
def sourceB (L : DecoderLayout) (s : BasisState) : List Bool := (lowBits L s++[false]).map (fun b=>b^^s L.sigma)

theorem sources_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (sourceA L s).length=256 ∧ (sourceB L s).length=256 := by simp [sourceA,sourceB,lowBits_length L hw s]

theorem sources_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (value (sourceA L s)+value (sourceB L s)+(s L.sigma).toNat)%2^256=
 (if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 have vy : value (lowBits L s)=regValue (L.y.take 255) s:=value_map_register _ _
 have ly:=lowBits_length L hw s
 have h:=regValue_lt (L.y.take 255) s
 have ln : (L.y.take 255).length=255:=by simp [hw.1]
 rw [ln] at h
 cases eq:s L.sigma with
 | false => simp [sourceA,sourceB,eq,value_append_bits,value,vy];congr 1;omega
 | true =>
   have bb : sourceB L s=(lowBits L s++[false]).map not := by
     simp only [sourceB,eq];congr 1;funext b;cases b <;> rfl
   rw [bb,complement_value]
   simp only [sourceA,value,List.length_append,List.length_singleton,ly,value_append_bits,vy,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,eq,Bool.toNat_true,ite_true]
   norm_num only [Nat.reducePow] at h ⊢
   omega
theorem sourceA_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceA L s).getD i false=(if i=0 then false else s (L.Y (i-1))) := by
 cases i with
 | zero => rfl
 | succ i => simpa only [sourceA,List.getD_cons_succ,Nat.add_sub_cancel,show ¬i+1=0 by omega,ite_false] using lowBits_get L hw s i (by omega)

theorem sourceB_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceB L s).getD i false=(if i<255 then s (L.Y i) ^^ s L.sigma else s L.sigma) := by
 unfold sourceB
 rw [getD_map_valid _ _ false false i (by simp [lowBits_length L hw s];omega)]
 by_cases h:i<255
 · rw [if_pos h,List.getD_append _ _ _ _ (by rw [lowBits_length L hw s];omega),lowBits_get L hw s i h]
 · have e:i=255:=by omega
   subst i
   rw [List.getD_eq_getElem _ _ (by simp [lowBits_length L hw s])]
   simp [List.getElem_append,lowBits_length L hw s]

theorem source_carry (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 carryAt (sourceA L s) (sourceB L s) (s L.sigma) (i+1)=aExpected L s i := by
 induction i with
 | zero =>
   rw [carryAt_next _ _ _ 0 (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s 0 (by omega),sourceB_get L hw s 0 (by omega)]
   simp only [ite_true,show 0<255 by omega,aExpected,carryAt]
   cases s L.sigma <;> cases s (L.Y 0) <;> decide
 | succ i ih =>
   rw [carryAt_next _ _ _ (i+1) (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s (i+1) (by omega),sourceB_get L hw s (i+1) (by omega),ih (by omega)]
   simp [aExpected,show ¬i+1=0 by omega,show i+1<255 by omega]

theorem raw_bit_sum (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) (i : Nat) (hi : i<256) :
 parity (rawSources L i) s=sumBit ((sourceA L s).getD i false) ((sourceB L s).getD i false)
   (carryAt (sourceA L s) (sourceB L s) (s L.sigma) i) := by
 rw [sourceA_get L hw s i hi,sourceB_get L hw s i hi]
 by_cases z:i=0
 · subst i
   simp only [rawSources,ite_true,show 0<255 by omega,parity,List.foldr_cons,List.foldr_nil,carryAt,sumBit]
   cases s (L.Y 0) <;> cases s L.sigma <;> decide
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   rw [source_carry L hw s j (by omega)]
   simp only [rawSources,show ¬j+1=0 by omega,ite_false,Nat.add_sub_cancel]
   by_cases h:j+1<255
   · simp only [h,ite_true,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries j (by omega)]
     cases s (L.Y j) <;> cases s (L.Y (j+1)) <;> cases s L.sigma <;> cases aExpected L s j <;> decide
   · have e:j=254:=by omega
     subst j
     simp only [show ¬254+1<255 by omega,ite_false,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries 254 (by omega)]
     cases s (L.Y 254) <;> cases s L.sigma <;> cases aExpected L s 254 <;> decide

theorem rawBits_eq_sums (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 rawBits L s=sums (sourceA L s) (sourceB L s) (s L.sigma) := by
 have lens: (sourceA L s).length=(sourceB L s).length:=(sources_length L hw s).1.trans (sources_length L hw s).2.symm
 apply List.ext_getElem (by rw [sums_length _ _ _ lens];simp [rawBits,(sources_length L hw s).1])
 intro i hi hj
 have h:i<256:=by simpa [rawBits] using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [rawBits,bitVector_get _ _ _ h,sums_at _ _ _ _ lens (by rw [(sources_length L hw s).1];omega)]
 exact raw_bit_sum L hw s carries i h

theorem rawBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 value (rawBits L s)=(if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 rw [rawBits_eq_sums L hw s carries,sums_value _ _ _ ((sources_length L hw s).1.trans (sources_length L hw s).2.symm),(sources_length L hw s).1]
 exact sources_value L hw s
theorem correction_literal (h b : Bool) :
 value (bitVector 256 (fun i=>if i=1 then b else if Nat.testBit (2^32+977) i then h else false))=
 h.toNat*(2^32+977)+2*b.toNat := by
 cases h <;> cases b <;> decide +kernel

theorem correctionBits_value (L : DecoderLayout) (s : BasisState) :
 value (correctionBits L s)=(s L.h).toNat*(2^32+977)+2*(s L.bias).toNat := by
 have eq : correctionBits L s=bitVector 256 (fun i=>if i=1 then s L.bias else if Nat.testBit (2^32+977) i then s L.h else false) := by
   unfold correctionBits
   congr 1
   funext i
   unfold correction
   split_ifs <;> simp [MappedBit.value]
 rw [eq,correction_literal]

theorem graph_of_register_values (L : DecoderLayout)
 (hw : L.Widths) (hn : L.wires.Nodup) (basis : BasisState)
 (carries : ∀i,i<255→basis (L.A i)=aExpected L basis i)
 (hv : regValue L.r basis=
 ((if basis L.sigma then regValue (L.y.take 255) basis else 3*regValue (L.y.take 255) basis)+
  2*(basis L.bias).toNat+(basis L.h).toNat*(2^32+977))%2^256) :
 BGraph L basis ∧ basis (L.R 0)=parity (bSources L 0) basis := by
 apply graph_of_bit_values
 rw [resultBits_value L hw,rawBits_value L hw basis carries,correctionBits_value]
 rw [hv,Nat.mod_add_mod]
 congr 1
 ring
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock aProgram eraseAProgram

def graphCore (L : DecoderLayout) : Program := aProgram L ++ (bBlock L ++ eraseAProgram L)

theorem graphCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis) (m : List Bool) :
 (run (graphCore L) m s).phase=s.phase ∧
 (∀q,q∉L.carry → q∉L.r → (run (graphCore L) m s).basis q=s.basis q) ∧
 (∀i,i<255 → (run (graphCore L) m s).basis (L.A i)=false) ∧
 (∀i,i<256 → (run (graphCore L) m s).basis (L.R i)=false) := by
 have result:=run_three_states (aProgram L) (bBlock L) (eraseAProgram L)
   (fun a d => a=s → d.phase=s.phase ∧
    (∀q,q∉L.carry → q∉L.r → d.basis q=s.basis q) ∧
    (∀i,i<255 → d.basis (L.A i)=false) ∧
    (∀i,i<256 → d.basis (L.R i)=false)) (by
   intro a b c d m1 m2 m3 hab hbc hcd eq
   subst a
   have af:=aProgram_frame L hw hn s clean m1
   have g:=graph m1
   have l:=low m1
   rw [hab] at af g l
   have bc:=bBlock_correct L hw hn b g l m2
   have bf:=bBlock_addFrame L hw hn s b af g l m2
   rw [hbc] at bc bf
   have final:=eraseAProgram_frame L hw hn s c bf m3
   rw [hcd] at final
   have out (q : Wire) (hq:q∉L.carry) : d.basis q=c.basis q := by
     rw [←hcd]
     simpa only [eraseAProgram] using add_reverse_outside L hw hn s 255 (le_refl _) c bf m3 q hq
   refine ⟨final.phase,?_,fun i hi=>final.clean i (by omega) hi,?_⟩
   · intro q hc hr
     have first : b.basis q=s.basis q := by
       rw [←hab]
       simpa only [aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m1 q hc
     exact (out q hc).trans ((bc.2.1 q hr).trans first)
   · intro i hi
     have away : L.R i∉L.carry := by
       intro ha
       exact source_r_away L hn _ (Or.inr (Or.inl ha)) (r_mem L hw i hi)
     exact (out (L.R i) away).trans (bc.2.2 i hi)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CleanedCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run graphCore biasErase clearQuotient

def CoreResult (L : DecoderLayout) (s t : State) : Prop :=
 t.phase=s.phase ∧ (∀q,q∉L.carry → q∉L.r → t.basis q=s.basis q) ∧
 (∀i,i<255 → t.basis (L.A i)=false) ∧ (∀i,i<256 → t.basis (L.R i)=false)

def cleanedCore (L : DecoderLayout) : Program :=graphCore L++(biasErase L++clearQuotient L)

theorem source_outside (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry ∧ q∉L.r := by
 refine ⟨carry_source_away L hn q hq,?_⟩
 apply source_r_away L hn q
 rcases hq with h|h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inr (Or.inl h))
 · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
 · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem cleanedCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis)
 (bias : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma))
 (quotient : s.basis L.h=(!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat))))
 (m : List Bool) :
 ∃t,CoreResult L s t ∧ run (cleanedCore L) m s=
   ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩ := by
 have result:=run_three_states (graphCore L) (biasErase L) (clearQuotient L)
   (fun a d=>a=s → ∃t,CoreResult L s t ∧ d=
     ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩) (by
   intro a t u v m1 m2 m3 hat htu huv eq
   subst a
   have tc:=graphCore_correct L hw hn s clean graph low m1
   rw [hat] at tc
   have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
     tc.2.1 q (source_outside L hn q hq).1 (source_outside L hn q hq).2
   have tsy:=stable (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))
   have ts:=stable L.sigma (by tauto)
   have th:=stable L.h (by tauto)
   have tb:=stable L.bias (by tauto)
   have bknown:t.basis L.bias=(t.basis (L.Y 255) && !t.basis L.sigma) := by rw[tb,tsy,ts];exact bias
   have ub:=biasErase_run L hw hn t m2 bknown
   rw[htu] at ub
   have baway:L.bias∉L.y:=flag_y_away L hn _ (by simp)
   have nd: [L.sigma,L.h,L.bias].Nodup := by
     apply List.nodup_iff_count.mpr
     intro q
     have h:=List.nodup_iff_count.mp hn q
     simp only[DecoderLayout.wires,List.count_append] at h
     omega
   have sh:L.sigma≠L.bias :=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
   have hb:L.h≠L.bias :=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
   have yb:L.Y 255≠L.bias :=fun e=>baway (e ▸ y_mem L hw 255 (by omega))
   have uy:u.basis (L.Y 255)=s.basis (L.Y 255) :=by rw[ub];simpa[writeBit,yb] using tsy
   have us:u.basis L.sigma=s.basis L.sigma :=by rw[ub];simpa[writeBit,sh] using ts
   have uh:u.basis L.h=s.basis L.h :=by rw[ub];simpa[writeBit,hb] using th
   have uv:regValue (L.y.take 255) u.basis=regValue (L.y.take 255) s.basis := by
     apply regValue_congr
     intro q hq
     have qb:q≠L.bias:=fun e=>baway (e ▸ List.mem_of_mem_take hq)
     rw[ub]
     simpa[writeBit,qb] using stable q (Or.inl (List.mem_of_mem_take hq))
   have uq:u.basis L.h=(!u.basis L.sigma && !(decide (regValue (L.y.take 255) u.basis<((p-1)/2)/3+(!u.basis (L.Y 255)).toNat))) := by
     rw[uy,us,uh,uv];exact quotient
   have uc:∀q∈L.carry,u.basis q=false := by
     intro q hq
     obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
     have i255:i<255:=by have len:=hw.2.2;omega
     have aeq:L.A i=q:=by
       change L.carry.getD i 0=q
       rw[List.getD_eq_getElem _ _ hi]
       exact eq
     have qb:q≠L.bias:=fun e=>carry_source_away L hn _ (by tauto) (e ▸ hq)
     rw[ub]
     simpa only[writeBit,Function.update_of_ne qb,←aeq] using tc.2.2.1 i i255
   have vc:=clearQuotient_correct L hw hn u m3 uc uq
   rw[huv] at vc
   refine ⟨t,tc,?_⟩
   rw[vc,ub]
   simp only[tc.1]) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT PostAGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run aProgram

theorem aExpected_congr (L : DecoderLayout) (a b : BasisState)
 (sigma : a L.sigma=b L.sigma) (ys : ∀i,i<256→a (L.Y i)=b (L.Y i))
 (i : Nat) (hi:i<255) : aExpected L a i=aExpected L b i := by
 induction i with
 |zero=>simp only[aExpected];rw[sigma,ys 0 (by omega)]
 |succ i ih=>simp only[aExpected];rw[ys i (by omega),ys (i+1) (by omega),sigma,ih (by omega)]

theorem aProgram_graph (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean:∀i,i<255→s.basis (L.A i)=false)
 (hv : regValue L.r s.basis=
 ((if s.basis L.sigma then regValue (L.y.take 255) s.basis else 3*regValue (L.y.take 255) s.basis)+
  2*(s.basis L.bias).toNat+(s.basis L.h).toNat*(2^32+977))%2^256) (m : List Bool) :
 BGraph L (run (aProgram L) m s).basis ∧
 (run (aProgram L) m s).basis (L.R 0)=parity (bSources L 0) (run (aProgram L) m s).basis := by
 let t:=run (aProgram L) m s
 have af:=aProgram_frame L hw hn s clean m
 have out (q : Wire) (hq:q∉L.carry) : t.basis q=s.basis q :=by
   simpa only[t,aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m q hq
 have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
   out q (carry_source_away L hn q hq)
 apply graph_of_register_values L hw hn t.basis
 · intro i hi
   exact (af.computed i hi).trans (aExpected_congr L s.basis t.basis af.sigma.symm
     (fun j hj=>(af.source j hj).symm) i hi)
 · have rv:regValue L.r t.basis=regValue L.r s.basis :=by
     apply regValue_congr
     intro q hq
     apply out
     intro hc
     exact source_r_away L hn q (Or.inr (Or.inl hc)) hq
   have yv:regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis :=by
     apply regValue_congr
     intro q hq
     exact stable q (Or.inl (List.mem_of_mem_take hq))
   rw[rv,yv,stable L.sigma (by tauto),stable L.h (by tauto),stable L.bias (by tauto)]
   exact hv
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Back
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run restoreSource copySource

theorem index_zero_mem (xs : List Wire) (b : BasisState)
 (zero:∀i,i<xs.length→b (xs.getD i 0)=false) (q : Wire) (hq:q∈xs) : b q=false := by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 have get:xs.getD i 0=q := by rw[List.getD_eq_getElem _ _ hi];exact eq
 rw[←get]
 exact zero i hi

def zeroR (L : DecoderLayout) (b : BasisState) : BasisState :=
 fun q=>if q∈L.r then false else complementBasis (L.Y 255) (L.y.take 255) b q

theorem cleaned_front_basis (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (t : State)
 (f : CoreResult L ⟨phase,frontBasis L b⟩ t)
 (ch:b L.h=false) (cb:b L.bias=false) (cc:∀q∈L.carry,b q=false) :
 writeBit (writeBit t.basis L.bias false) L.h false=zeroR L b := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 have hy:=flag_y_away L hn L.h (by simp)
 have byy:=flag_y_away L hn L.bias (by simp)
 have hr:=source_r_away L hn L.h (by tauto)
 have br:=source_r_away L hn L.bias (by tauto)
 have tr:∀q∈L.r,t.basis q=false := index_zero_mem L.r t.basis (by intro i hi;exact f.2.2.2 i (by have len:=hw.2.1;omega))
 have tc:∀q∈L.carry,t.basis q=false :=index_zero_mem L.carry t.basis (by intro i hi;exact f.2.2.1 i (by have len:=hw.2.2;omega))
 funext q
 by_cases qh:q=L.h
 · subst q
   simp[writeBit,zeroR,hr,complementBasis,show L.h∉L.y.take 255 from fun h=>hy (List.mem_of_mem_take h),ch]
 · by_cases qb:q=L.bias
   · subst q
     simp[writeBit,Ne.symm hb,zeroR,br,complementBasis,show L.bias∉L.y.take 255 from fun h=>byy (List.mem_of_mem_take h),cb]
   · simp only[writeBit,Function.update_of_ne qh,Function.update_of_ne qb]
     by_cases qr:q∈L.r
     · simp[zeroR,qr,tr q qr]
     · by_cases qc:q∈L.carry
       · have qy:q∉L.y:=fun h=>carry_source_away L hn q (Or.inl h) qc
         simp[zeroR,qr,tc q qc,complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),cc q qc]
       · rw[f.2.1 q qc qr]
         simp[frontBasis,writeBit,qh,qb,zeroR,qr,complementBasis]

theorem restore_zeroR (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 run (restoreSource L) m ⟨phase,zeroR L b⟩=
  ⟨phase,fun q=>if q∈L.r then false else b q⟩ := by
 rw[restoreSource_run L hw hn]
 have nd:=normalize_nd L hw hn
 have sig:zeroR L b (L.Y 255)=b (L.Y 255):=by
   simp[zeroR,complementBasis,show L.Y 255∉L.y.take 255 from fun h=>nd.2 (List.mem_append_left _ h),
     show L.Y 255∉L.r from fun h=>nd.2 (List.mem_append_right _ h)]
 apply congrArg (State.mk phase)
 funext q
 simp only[complementBasis,sig]
 by_cases qr:q∈L.r
 · have qt:q∉L.y.take 255 := by
     intro h
     exact source_r_away L hn q (Or.inl (List.mem_of_mem_take h)) qr
   simp[qr,qt,zeroR]
 · by_cases qt:q∈L.y.take 255
   · simp[zeroR,complementBasis,qr,qt,Bool.xor_assoc]
   · simp[zeroR,complementBasis,qr,qt]

def back (L : DecoderLayout) : Program :=restoreSource L++copySource L

theorem back_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 (run (back L) m ⟨phase,zeroR L b⟩).phase=phase ∧
 (∀q,q∉L.r → (run (back L) m ⟨phase,zeroR L b⟩).basis q=b q) ∧
 regValue L.r (run (back L) m ⟨phase,zeroR L b⟩).basis=regValue L.y b := by
 rw[back,run_append,run_take,restore_zeroR L hw hn]
 let v : State:=⟨phase,fun q=>if q∈L.r then false else b q⟩
 have c:=copySource_correct L hw hn v (m.drop (measurementCount (restoreSource L)))
 refine ⟨c.1,?_,?_⟩
 · intro q hq
   simpa only[v,if_neg hq] using c.2.1 q hq
 · rw[c.2.2]
   have rz:regValue L.r v.basis=0 :=(regValue_zero _ _).mpr (by intro q hq;simp[v,hq])
   have yv:regValue L.y v.basis=regValue L.y b :=by
     apply regValue_congr
     intro q hq
     have qr:q∉L.r:=source_r_away L hn q (Or.inl hq)
     simp[v,qr]
   rw[rz,yv,Nat.zero_xor]
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT DecoderCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run front cleanedCore back aProgram

theorem decoder_parts (L : DecoderLayout) : decoder L=front L++(cleanedCore L++back L) := by
 simp only[decoder,front,cleanedCore,graphCore,aProgram,eraseAProgram,bBlock,bSources,back,List.append_assoc]

theorem decoder_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
 (ys:regValue L.y s.basis=centerWord Y)
 (rs:regValue L.r s.basis=centerWord ((if sigma then 1 else 3)*Y))
 (sig:s.basis L.sigma=sigma) (hc:s.basis L.h=false) (bc:s.basis L.bias=false)
 (cc:∀q∈L.carry,s.basis q=false) :
 (run (decoder L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (decoder L) m s).basis q=s.basis q) ∧
 regValue L.r (run (decoder L) m s).basis=centerWord Y := by
 have result:=run_three_states (front L) (cleanedCore L) (back L)
   (fun a d=>a=s → d.phase=s.phase ∧ (∀q,q∉L.r → d.basis q=s.basis q) ∧
     regValue L.r d.basis=centerWord Y) (by
   intro a n u d m1 m2 m3 han hnu hud eq
   subst a
   have nf:=front_run L hw hn s m1
   rw[han] at nf
   let f : State:=⟨s.phase,frontBasis L s.basis⟩
   have neq:n=f:=nf
   subst n
   rw[nf] at hnu
   have scalar:=actual_front_scalar L hw hn s.basis Y sigma ys rs sig hc bc
   have nc:∀i,i<255→f.basis (L.A i)=false :=by
     intro i hi
     exact front_carry_clean L hn s.basis cc (L.A i) (a_mem L hw i hi)
   have bb:f.basis L.bias=(f.basis (L.Y 255) && !f.basis L.sigma) :=by
     have facts:=actual_front_values L hw hn s.basis Y sigma ys rs sig hc bc
     change frontBasis L s.basis L.bias=(frontBasis L s.basis (L.Y 255) && !frontBasis L s.basis L.sigma)
     rw[facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2]
   have cg:=cleanedCore_correct L hw hn f nc
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).1)
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).2) bb scalar.2 m2
   obtain ⟨t,tf,ut⟩:=cg
   rw[hnu] at ut
   have cleanbasis:=cleaned_front_basis L hw hn s.basis s.phase t tf hc bc cc
   have uz:u=⟨s.phase,zeroR L s.basis⟩ :=by
     rw[ut,cleanbasis]
   have done:=back_correct L hw hn s.basis s.phase m3
   rw[uz] at hud
   rw[hud] at done
   exact ⟨done.1,done.2.1,done.2.2.trans ys⟩) s m
 rw[decoder_parts]
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Caller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run decoder

def work (L : DecoderLayout) : List Wire:=L.carry++[L.h,L.bias]

theorem work_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire) (hq:q∈work L) :
 q∉L.r ∧ q∉L.y := by
 simp only[work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with hc|rfl|rfl
 · refine ⟨source_r_away L hn q (Or.inr (Or.inl hc)),?_⟩
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hc
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩

theorem terminal_relation (X Y : Fp) (sigma : Bool)
 (h:(X+(if sigma then Y else -Y))/2=Y) : X=(if sigma then 1 else 3)*Y := by
 have two:(2:Fp)≠0:=by decide
 have e: X+(if sigma then Y else -Y)=Y*2 := (div_eq_iff two).mp h
 cases sigma <;> simp only[Bool.false_eq_true,if_false,if_true] at e ⊢ <;> linear_combination e

theorem decoder_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : BasisState) (clean : ∀q∈work L,origin q=false) (X Y : Fp)
 (hend:(X+(if origin L.sigma then Y else -Y))/2=Y) :
 Triple (PairFrame L.r L.y origin (centerWord X) (centerWord Y)) (decoder L)
   (PairFrame L.r L.y origin (centerWord Y) (centerWord Y)) := by
 intro s m input
 have cleanS (q : Wire) (hq:q∈work L) : s.basis q=false :=
   (input.2.2 q (work_away L hn q hq).1 (work_away L hn q hq).2).trans (clean q hq)
 have sig:s.basis L.sigma=origin L.sigma:=input.2.2 L.sigma
   (source_r_away L hn _ (by tauto)) (flag_y_away L hn _ (by simp))
 have rel:=terminal_relation X Y (origin L.sigma) hend
 have rword:regValue L.r s.basis=centerWord ((if origin L.sigma then 1 else 3)*Y) := by
   rw[input.1,rel]
 have c:=decoder_correct L hw hn Y (origin L.sigma) s m input.2.1 rword sig
   (cleanS L.h (by simp[work])) (cleanS L.bias (by simp[work]))
   (fun q hq=>cleanS q (by simp[work,hq]))
 refine ⟨c.1,c.2.2,?_,?_⟩
 · exact (regValue_congr L.y _ _ (fun q hq=>c.2.1 q (source_r_away L hn q (Or.inl hq)))).trans input.2.1
 · intro q qr qy
   exact (c.2.1 q qr).trans (input.2.2 q qr qy)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT EndpointCaller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEndpoint
open Arithmetic Secp256k1 BalancedField TerminalGraph
attribute [local irreducible] run TerminalGraph.decoder

def half (divide : Bool) (w : Nat→Wire) (sign : Wire) : Program :=
 if divide then decoder (ofBalanced (Q6EndpointCell.ports w sign)) else Q6EndpointCell.half false w sign

def endpoint (divide : Bool) (w : Nat→Wire) (b g sign : Wire) (ig : Bool) : Program :=
 transcriptSelectWindow b g sign ig (half divide w sign)

theorem clean_decoder (w : Nat→Wire) (sign : Wire) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) :
 ∀q∈work (ofBalanced (Q6EndpointCell.ports w sign)),origin q=false := by
 have cl:=Q6EndpointCell.clean_work w sign origin hc
 intro q hq
 apply cl
 simp only[work,ofBalanced,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 simp only[BalancedCircuit.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rcases hq with (h|rfl)|rfl|rfl
 · exact Or.inr (List.mem_of_mem_take h)
 all_goals tauto

theorem half_frame (divide : Bool) (w : Nat→Wire) (sign : Wire)
 (hn:(Q6EndpointCell.ports w sign).wires.Nodup) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) (X Y : Fp)
 (hend:divide=true→(X+(if origin sign then Y else -Y))/2=Y) :
 Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin (centerWord X) (centerWord Y))
   (half divide w sign)
   (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
     (centerWord (if divide then (X+(if origin sign then Y else -Y))/2 else 2*X+(if origin sign then -Y else Y)))
     (centerWord Y)) := by
 cases divide
 · exact Q6EndpointCell.half_frame false w sign hn origin hc X Y
 · have c:=decoder_frame (ofBalanced (Q6EndpointCell.ports w sign))
     (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign)) (ofBalanced_nodup _ hn)
     origin (clean_decoder w sign origin hc) X Y (by simpa only[ofBalanced,Q6EndpointCell.ports_sign] using hend rfl)
   simpa only[half,ofBalanced,if_true,hend rfl] using c

theorem endpoint_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup) (nd : [b,g,sign].Nodup)
    (hb : b∉(Q6EndpointCell.ports w sign).r ∧ b∉(Q6EndpointCell.ports w sign).y)
    (hg : g∉(Q6EndpointCell.ports w sign).r ∧ g∉(Q6EndpointCell.ports w sign).y)
    (hs : sign∉(Q6EndpointCell.ports w sign).r ∧ sign∉(Q6EndpointCell.ports w sign).y)
    (origin : BasisState) (hz : origin sign=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (hend : divide=true → (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2=Y) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
      (centerWord X) (centerWord Y)) (endpoint divide w b g sign ig)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord (if divide then (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit origin b g ig then -Y else Y))) (centerWord Y)) := by
 have ns:=OwnQ6Core5.sign_work (Q6EndpointCell.ports w sign) hn
 have cl:Q6EndpointCell.Clean w (mixedTranscriptBase origin b g sign ig) :=by
   intro q hq
   have nq:q≠sign:=fun e=>ns (by simpa only[Q6EndpointCell.ports_work] using e ▸ hq)
   simpa only[mixedTranscriptBase,writeBit,Function.update_of_ne nq] using hc q hq
 have body:=half_frame divide w sign hn (mixedTranscriptBase origin b g sign ig) cl X Y
   (by simpa only[mixedTranscriptBase,writeBit,Function.update_self] using hend)
 simp only[mixedTranscriptBase,writeBit,Function.update_self] at body
 exact transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs origin hz _ _ _ _ _ body

theorem half_counts (divide : Bool) (w : Nat→Wire) (sign : Wire) :
 toffoliCount (half divide w sign)=(if divide then 512 else 1020) ∧
 measurementCount (half divide w sign)=(if divide then 766 else 1021) := by
 cases divide
 · exact Q6EndpointCell.half_counts false w sign
 · exact decoder_counts _ (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign))
end ECDSAAdd.Entrant.TerminalGraphEndpoint


-- TERMINAL GRAPH COMPONENT TerminalReplayDefs
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
abbrev Context := OneFlagReplay.Context
abbrev firstPacket := OneFlagReplay.firstPacket
abbrev groups := OneFlagReplay.groups

def rawEnd (divide : Bool) : Program :=
 TerminalGraphEndpoint.endpoint divide base (base 2400) (base 510) (base 2409)
   (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program :=renameProgram (shifted Placement5.pi0) (rawEnd divide)
def logicalReplay (divide : Bool) : Program :=
 if divide then firstPacket true++groups true 1 101++endPacket true
 else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program :=renameProgram (OB5.sig 511) (logicalReplay divide)
end ECDSAAdd.Entrant.TerminalGraphReplay
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed HalfFieldOB5

def program (divide : Bool) : Program :=
 if divide then OwnQ5Endpoint.centerT++(TerminalGraphReplay.replay true++(copyN++OwnQ5Endpoint.canonT))
 else OwnQ5Endpoint.centerT++(copyN++(TerminalGraphReplay.replay false++OwnQ5Endpoint.canonT))

def segH (divide : Bool) : Program :=
 [.X (base 511)]++(renameProgram HostOB5.hostSwap (program divide)++[.X (base 511)])
end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalSW
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSW
open Arithmetic MappedCompressed CompressedFieldSupport Secp256k1 DirectSkywalk SW
attribute [local irreducible] wires TerminalGraphEndpoint.half Q6EndpointCell.halfE
abbrev firstPacketS := OneFlagSW.firstPacketS
abbrev groupsS := OneFlagSW.groupsS

def rawEndS (divide : Bool) : Program :=
 selW (base 510) (base 2409) (TerminalGraphEndpoint.half divide base (base 2409))
def endPacketS (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEndS divide)
def logicalReplayS (divide : Bool) : Program :=
 if divide then firstPacketS true++groupsS true 1 101++endPacketS true
 else endPacketS false++groupsS false 1 101++firstPacketS false

def replayS (divide : Bool) : Program :=renameProgram (OB5.sig 511) (logicalReplayS divide)
def segmentS (divide : Bool) : Program :=
 if divide then OwnQ5Endpoint.centerT++(replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
 else OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++(replayS false++OwnQ5Endpoint.canonT))

theorem selEnd_sel
 (sub:∀d,wires (TerminalGraphEndpoint.half d base (base 2409))⊆wires (Q6EndpointCell.halfE d base (base 2409)))
 (divide : Bool) :
 Sel (base 2400) 1 (endPacketS divide) (TerminalGraphReplay.endPacket divide) := by
 have n:[base 2400,base 510,base 2409].Nodup:=by decide
 have away:base 2400∉wires (TerminalGraphEndpoint.half divide base (base 2409)):=fun h=>OneFlagSW.selHalfE_away divide (sub divide h)
 have b:Sel (base 2400) 1 (rawEndS divide) (TerminalGraphReplay.rawEnd divide) :=
   ((Sel.refl _ _ away).window (base 510) (base 2409)
     (mixedTranscriptUnitTrace.getD 510 (false,false)).1 n).cast (by norm_num) rfl rfl
 exact b.rename (shifted Placement5.pi0) OneFlagSW.selShift0_fix

theorem selLogical_sel
 (sub:∀d,wires (TerminalGraphEndpoint.half d base (base 2409))⊆wires (Q6EndpointCell.halfE d base (base 2409)))
 (divide : Bool) :
 Sel (base 2400) 1020 (logicalReplayS divide) (TerminalGraphReplay.logicalReplay divide) := by
 have g:=OneFlagSW.selGroups_sel divide 1 101 (by omega)
 have e:=selEnd_sel sub divide
 have f:=OneFlagSW.selFirstPacket_sel divide
 cases divide
 · exact ((e.append g).append f).cast (by norm_num) rfl rfl
 · exact ((f.append g).append e).cast (by norm_num) rfl rfl

theorem selReplay_sel
 (sub:∀d,wires (TerminalGraphEndpoint.half d base (base 2409))⊆wires (Q6EndpointCell.halfE d base (base 2409)))
 (divide : Bool) :
 Sel (base 2400) 1020 (replayS divide) (TerminalGraphReplay.replay divide) :=
 ((selLogical_sel sub divide).rename_inj (OB5.sig 511) (OB5.sig_injective 511 (by decide))).castb OneFlagSW.selSig_2400
end ECDSAAdd.Entrant.TerminalGraphSW


-- TERMINAL GRAPH COMPONENT TerminalReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
open OneFlagReplay
attribute [local irreducible] run wires

theorem rawEnd_disjoint (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d))
 (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
 (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
 Disjoint (wires (History5.allEncode base 102)) (wires (rawEnd divide)) :=
 (OneFlagReplay.rawEnd_disjoint divide hn hp).mono_right (sub divide)

theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 510 (by decide)) ctx.ho
  rw [mixedTape_base_getD 510 (by decide)] at layout
  have newLayout := Q6EndpointCell.ports_transcript base (base 2400) (base 510) (base 1538)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have result := TerminalGraphEndpoint.endpoint_frame divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 newLayout.kernel (by decide)
    (newLayout.outside _ (by simp)) (newLayout.outside _ (by simp))
    (newLayout.outside _ (by simp [Q6EndpointCell.ports])) origin ctx.hg0
    (Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity) X Y (fun h => by
      have e := hend h
      subst h
      simpa only [Replay5.endPayload,if_true] using e)
  simpa only [rawEnd,Replay5.endPayload,Prod.fst,Prod.snd] using result

theorem endPacket_frame (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := History5.encoded_disjoint_step base (base 2409)
    (skywalkShared_integer_nodup base ctx.hn) origin X Y _ _ _ (rawEnd_disjoint sub divide ctx.hn ctx.hp)
    (rawEnd_frame divide origin ctx X Y hend) s m input
  have eq := Replay5.placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame sub true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame sub false origin ctx Y Y (fun e => absurd e (by decide)) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  FieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame sub origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (sub : ∀d,wires (rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  FieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame sub origin ctx x hx0 hx trace Y) s m input


















end ECDSAAdd.Entrant.TerminalGraphReplay


-- TERMINAL GRAPH COMPONENT TerminalSegment
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic Secp256k1 BalancedField MappedCompressed OffsetBorrowedCanonical History5 HalfFieldOB5
attribute [local irreducible] run wires HalfFieldOB5.centerT HalfFieldOB5.canonT TerminalGraphReplay.replay TerminalGraphReplay.rawEnd OneFlagReplay.rawEnd TerminalGraphEndpoint.endpoint TerminalGraphEndpoint.half TerminalGraph.decoder

private theorem run_four_states (a b c d : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 : State) (m1 m2 m3 m4 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → run d m4 s3=s4 → P s s4)
    (s : State) (m : List Bool) : P s (run (a++(b++(c++d))) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

private theorem double_half (Y W : Fp) : 2*(Y/2*W)=Y*W := by
  have two : (2:Fp) ≠ 0 := by decide
  field_simp

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp) ≠ 0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem double_half_one (Y : Fp) : 2*(Y/2)=Y := by
  have two : (2:Fp) ≠ 0 := by decide
  exact mul_div_cancel₀ Y two

/-- Same hypotheses and conclusion as the protected selected field segment. -/
theorem program_spec (sub : ∀d,wires (TerminalGraphReplay.rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let out := run (program divide) m s
    out.phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let ctx : TerminalGraphReplay.Context origin := ⟨hn,ho,hp,hf,hg0,hs0,env,legal,hr⟩
  cases divide
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out
    have all := run_four_states OwnQ5Endpoint.centerT copyN (TerminalGraphReplay.replay false) OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := copy_fill hn origin (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := TerminalGraphReplay.inverse_frame sub origin ctx
        x hx0 hx trace (Y/2) s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y := by
        unfold fieldResult
        split
        · simp only [Bool.false_eq_true,if_false]; exact double_half Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,Bool.false_eq_true,if_false] using all input
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out
    have all := run_four_states OwnQ5Endpoint.centerT (TerminalGraphReplay.replay true) copyN OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := TerminalGraphReplay.forward_frame sub origin ctx x hx0 hx trace
        (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := copy_clear hn origin _ s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2/(x:Fp) else Y/2)=fieldResult true origin x Y := by
        unfold fieldResult
        split
        · simp only [if_true]; exact double_half_div Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,if_true] using all input

theorem program_state_eq (sub : ∀d,wires (TerminalGraphReplay.rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    run (program divide) m s=run (OneFlagSegment.program divide) m s := by
  have a := program_spec sub divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have b := OneFlagSegment.program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  exact OneFlagSegment.canonical_frame_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem program_state_eq_q6 (sub : ∀d,wires (TerminalGraphReplay.rawEnd d)⊆wires (OneFlagReplay.rawEnd d)) (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    run (program divide) m s=run (Q6EndpointSegment.program divide) m s := by
  have a := program_spec sub divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have b := Q6EndpointSegment.program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  exact OneFlagSegment.canonical_frame_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalSupportOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSupportOnly
open Arithmetic MappedCompressed TerminalGraph

def actualLayout (sign : Nat) : DecoderLayout :=
  ofBalanced (Q6EndpointCell.ports base (base sign))
def actualDecoder (sign : Nat) : Program := decoder (actualLayout sign)

private abbrev footprint (s q : Nat) : Prop :=
 q=base s ∨ q=base 1027 ∨ q=base 768 ∨ q=base 1797 ∨ q=base 1540 ∨
 (base 770≤q ∧ q<base 1026) ∨ (base 2056≤q ∧ q<base 2312) ∨
 (base 512≤q ∧ q<base 765)

private theorem block_mem (q start n : Nat) :
 q∈wireBlock base start n ↔ base start≤q ∧ q<base (start+n) := by
 simp only [wireBlock,List.mem_map,List.mem_range'_1]
 constructor
 · rintro ⟨a,⟨ha,hb⟩,he⟩
   change a+16=q at he
   constructor
   · change start+16≤q
     rw [←he]
     exact Nat.add_le_add_right ha 16
   · change q<start+n+16
     rw [←he]
     exact Nat.add_lt_add_right hb 16
 · rintro ⟨hlo,hhi⟩
   change start+16≤q at hlo
   change q<start+n+16 at hhi
   have hq : 16≤q := le_trans (Nat.le_add_left 16 start) hlo
   have eq : q-16+16=q := Nat.sub_add_cancel hq
   refine ⟨q-16,⟨?_,?_⟩,?_⟩
   · have hh : start+16≤q-16+16 := by rw [eq]; exact hlo
     exact (show start+16≤q-16+16 ↔ start≤q-16 from Nat.add_le_add_iff_right).mp hh
   · have hh : q-16+16<start+n+16 := by rw [eq]; exact hhi
     exact (show q-16+16<start+n+16 ↔ q-16<start+n from Nat.add_lt_add_iff_right).mp hh
   · exact eq

private theorem actual_carry (s : Nat) :
 (actualLayout s).carry=wireBlock base 512 253++[base 1540,base 1797] := by
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,List.take_append,
   show (wireBlock base 512 253).length=253 from by simp [wireBlock],
   show (wireBlock base 512 253).take 254=wireBlock base 512 253 from
     List.take_of_length_le (by simp [wireBlock]),Nat.reduceSub,List.take_succ_cons,
   List.take_zero,List.nil_append,List.append_assoc,List.singleton_append]

private theorem actual_y (s : Nat) :
 (actualLayout s).y=wireBlock base 770 256 := by rfl
private theorem actual_r (s : Nat) :
 (actualLayout s).r=wireBlock base 2056 256 := by rfl

private theorem actual_sites (s q : Nat) :
 q∈(actualLayout s).wires.toFinset ↔ footprint s q := by
 simp only [List.mem_toFinset,DecoderLayout.wires,List.mem_append,
   List.mem_cons,List.not_mem_nil,or_false,actual_carry,actual_y,actual_r,block_mem]
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,footprint]
 tauto

private def correctionCheck (s : Nat) : List Correction→Bool
 | []=>true
 | .Z t::cs=>decide (footprint s t) && correctionCheck s cs
 | .CZ a b::cs=>decide (footprint s a) && decide (footprint s b) && correctionCheck s cs

private theorem correctionCheck_iff (s : Nat) (cs : List Correction) :
 correctionCheck s cs=true ↔ correctionWires cs⊆(actualLayout s).wires.toFinset := by
 induction cs with
 | nil=>simp [correctionCheck,correctionWires]
 | cons c cs ih=>
   cases c <;>
     simp only [correctionCheck,correctionWires,Bool.and_eq_true,decide_eq_true_eq,
       Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
       Finset.empty_subset,and_true,ih,actual_sites]

private def instructionCheck (s : Nat) : Instr→Bool
 | .X t=>decide (footprint s t)
 | .CX a t=>decide (footprint s a) && decide (footprint s t)
 | .CCX a b t=>decide (footprint s a) && decide (footprint s b) && decide (footprint s t)
 | .measureX t c d=>decide (footprint s t) && correctionCheck s c && correctionCheck s d

private theorem instructionCheck_iff (s : Nat) (i : Instr) :
 instructionCheck s i=true ↔ i.wires⊆(actualLayout s).wires.toFinset := by
 cases i <;>
   simp only [instructionCheck,Instr.wires,Bool.and_eq_true,decide_eq_true_eq,
     Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
     Finset.empty_subset,and_true,actual_sites,correctionCheck_iff,and_assoc]

private def supportCheck (s : Nat) (P : Program) : Bool := P.all (instructionCheck s)
private theorem supportCheck_correct (s : Nat) (P : Program)
 (h : supportCheck s P=true) : wires P⊆(actualLayout s).wires.toFinset := by
 induction P with
 | nil=>simp [wires]
 | cons i P ih=>
   have hh : instructionCheck s i=true ∧ supportCheck s P=true := by
     simpa only [supportCheck,List.all_cons,Bool.and_eq_true] using h
   simp only [wires,Finset.union_subset_iff]
   exact ⟨(instructionCheck_iff s i).mp hh.1,ih hh.2⟩

theorem actual_decoder_support :
    wires (actualDecoder 2409)⊆(ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset ∧
    wires (actualDecoder 2410)⊆(ofBalanced (Q6EndpointCell.ports base (base 2410))).wires.toFinset := by
  constructor <;> apply supportCheck_correct <;> decide +kernel

end ECDSAAdd.Entrant.TerminalGraphSupportOnly


-- TERMINAL GRAPH COMPONENT TerminalFootprint
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic MappedCompressed
attribute [local irreducible] wires CoherentTail.addPrefix Q6Structural.rawAdd Q6EndpointStructural.forwardE Q6EndpointCell.halfE
theorem prefix_sites (x y c : List Wire) (a t z cin : Wire)
 (hy:y.length=x.length) (hc:c.length=x.length) :
 wires (CoherentTail.addPrefix x y c a t z cin)=(x++y++c++[a,t,z,cin]).toFinset := by
 induction x generalizing y c cin with
 | nil=>
   have ey:y=[]:=List.eq_nil_of_length_eq_zero hy
   have ec:c=[]:=List.eq_nil_of_length_eq_zero hc
   subst y; subst c
   ext q
   simp [CoherentTail.addPrefix,CoherentTail.program,wires,Instr.wires]
   tauto
 | cons b xs ih=>
   cases y with
   | nil=>simp at hy
   | cons d ys=>
     cases c with
     | nil=>simp at hc
     | cons k ks=>
       have hy':ys.length=xs.length:=by simpa using hy
       have hc':ks.length=xs.length:=by simpa using hc
       rw [CoherentTail.addPrefix,wires_append,wires_append,wires_append,ih _ _ _ hy' hc']
       ext q
       simp [majority,eraseCarry,wires,Instr.wires,correctionWires]
       tauto

theorem layout_subset_forwardE (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).wires.toFinset⊆wires (Q6EndpointStructural.forwardE L) := by
 have len:=hw.2.2
 have yw:=hw.2.1
 have rw:=hw.1
 have ct:(Q6Structural.carryLayout L).carry.take 255=L.carry.take 254++[L.lower] := by
   simp [Q6Structural.carryLayout,Q6Structural.q6Carry,List.take_append,List.length_take,len]
 have plen:((Q6Structural.carryLayout L).carry.take 255).length=L.ylow.length :=by
   rw[ct]
   simp[yw,len]
 have ylen:L.low.length=L.ylow.length:=by simp[BalancedCleanup.Layout.low,rw,yw]
 have pref:=prefix_sites L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign ylen plen
 have rawsub:wires (CoherentTail.addPrefix L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign)⊆wires (Q6Structural.rawAdd L) :=by
   simp only[Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,FieldRename.mapCircuit] at *
   intro q hq
   simp only[wires_append]
   exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
 have allsub:wires (GuardCompression.seed L)∪wires (Q6Structural.rawAdd L)⊆wires (Q6EndpointStructural.forwardE L) :=by
   intro q hq
   simp only[Q6EndpointStructural.forwardE,Q6StructuralCell.forwardPrefix,wires_append,Finset.mem_union] at hq ⊢
   tauto
 intro q hq
 apply allsub
 by_cases parity:q=L.parity
 · subst q
   exact Finset.mem_union_left _ (by simp[GuardCompression.seed,wires,Instr.wires])
 · apply Finset.mem_union_right
   apply rawsub
   rw[pref,ct]
   simp only[DecoderLayout.wires,ofBalanced,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
     BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low] at hq ⊢
   tauto

theorem actual_layout_subset_halfE :
 (ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset⊆
 wires (Q6EndpointCell.halfE true base (base 2409)) := by
 have core:=layout_subset_forwardE (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths _ _)
 intro q hq
 have h:=core hq
 rw[Q6EndpointCell.halfE_true,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT TerminalSupport
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSupport
open Arithmetic MappedCompressed TerminalGraph
attribute [local irreducible] wires TerminalGraphEndpoint.half Q6EndpointCell.halfE TerminalGraphReplay.rawEnd OneFlagReplay.rawEnd

theorem half_subset (d : Bool) :
 wires (TerminalGraphEndpoint.half d base (base 2409))⊆wires (Q6EndpointCell.halfE d base (base 2409)) := by
 cases d
 · rw[TerminalGraphEndpoint.half,Q6EndpointCell.halfE_false]
   exact Finset.Subset.refl _
 · simp only[TerminalGraphEndpoint.half,ite_true]
   exact TerminalGraphSupportOnly.actual_decoder_support.1.trans actual_layout_subset_halfE

theorem window_subset (b source flag : Wire) (constant : Bool) (P Q : Program)
 (sub:wires P⊆wires Q) : wires (transcriptSelectWindow b source flag constant P)⊆wires (transcriptSelectWindow b source flag constant Q) := by
 simp only[transcriptSelectWindow,wires_append]
 gcongr

theorem rawEnd_subset (d : Bool) : wires (TerminalGraphReplay.rawEnd d)⊆wires (OneFlagReplay.rawEnd d) := by
 unfold TerminalGraphReplay.rawEnd OneFlagReplay.rawEnd TerminalGraphEndpoint.endpoint Q6EndpointCell.endpoint
 exact window_subset _ _ _ _ _ _ (half_subset d)

theorem endPacket_subset (d : Bool) : wires (TerminalGraphReplay.endPacket d)⊆wires (OneFlagReplay.endPacket d) :=
 OneFlagReplay.rename_subset _ _ _ (rawEnd_subset d)

theorem logicalReplay_subset (d : Bool) : wires (TerminalGraphReplay.logicalReplay d)⊆wires (OneFlagReplay.logicalReplay d) := by
 have e:=endPacket_subset d
 cases d <;> simp only[TerminalGraphReplay.logicalReplay,OneFlagReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,wires_append]
 · exact Finset.union_subset_union (Finset.union_subset_union e (Finset.Subset.refl _)) (Finset.Subset.refl _)
 · exact Finset.union_subset_union (Finset.Subset.refl _) e

theorem replay_subset (d : Bool) : wires (TerminalGraphReplay.replay d)⊆wires (OneFlagReplay.replay d) :=
 OneFlagReplay.rename_subset _ _ _ (logicalReplay_subset d)

theorem program_subset (d : Bool) : wires (TerminalGraphSegment.program d)⊆wires (OneFlagSegment.program d) := by
 have r:=replay_subset d
 cases d <;> simp only[TerminalGraphSegment.program,OneFlagSegment.program,Bool.false_eq_true,if_false,if_true,wires_append]
 · exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union r (Finset.Subset.refl _)))
 · exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union r (Finset.Subset.refl _))
end ECDSAAdd.Entrant.TerminalGraphSupport
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic MappedCompressed
 theorem replay_subset_old (d : Bool) : wires (replay d)⊆wires (Q6EndpointReplay.replay d) :=
  (TerminalGraphSupport.replay_subset d).trans (OneFlagReplay.replay_subset_old d)
 theorem rename_subset (f : Wire→Wire) (P Q : Program) (h:wires P⊆wires Q) :
  wires (renameProgram f P)⊆wires (renameProgram f Q) :=OneFlagReplay.rename_subset f P Q h
end ECDSAAdd.Entrant.TerminalGraphReplay
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed
 theorem segH_subset (d : Bool) : wires (segH d)⊆wires (OneFlagSegment.segH d) :=by
  have r:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ (TerminalGraphSupport.program_subset d)
  simp only[segH,OneFlagSegment.segH,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union r (Finset.Subset.refl _))
 theorem hosted1542_free (d : Bool) : base 1542∉wires (segH d) :=
  fun h=>OneFlagSegment.hosted1542_free d (segH_subset d h)
end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalEntryRaw
namespace ECDSAAdd.Entrant.TerminalGraphProviderSupport
open Arithmetic
 theorem replay_support (d : Bool) : wires (TerminalGraphReplay.replay d)⊆OB5Support.segSites := by
  exact (TerminalGraphReplay.replay_subset_old d).trans (Q6EndpointReplaySupport.replay_support d)
end ECDSAAdd.Entrant.TerminalGraphProviderSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI EntryFuse
attribute [local irreducible] run wires

def field5 : Program := TerminalGraphReplay.replay true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5 : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5 ++ [.X (base 511)])
def kernel5 : Program := NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
  hostField5 ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem field_support : wires field5⊆OB5Support.segSites := by
  simp only [field5,wires_append,Finset.union_subset_iff]
  exact ⟨TerminalGraphProviderSupport.replay_support true,HalfFieldOB5Support.copy_support,OwnQ5Endpoint.support.2⟩

theorem field_free : base 511∉wires field5 ∧ base 1542∉wires field5 :=
  ⟨fun h=>OB5Support.seg_host_free.1 (field_support h),fun h=>OB5Support.seg_host_free.2 (field_support h)⟩

theorem field5_unhosted_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run field5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (SegmentOB5.program true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) := by
    exact (regValue_congr _ _ _ paired.2.2).trans value
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hpPool : base 2409∉skywalkPoolWires base := by
    intro bad
    exact ho _ (by simp) (arith_block_subset_shared base 0 1798 (by omega) bad)
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have centerEq := center5_compare hn hpPool origin.basis facts.env legal facts.targetHigh
    facts.sourceHigh facts.sourceZero Y a3 v3 placedInput paired.1 paired.2.1 target
    ((List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4).take
      (measurementCount OwnQ5Endpoint.centerT))
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have oldReplacement:=Q6EndpointSegment.program_state_eq true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 (dummy++m4) placedInput
  have newReplacement:=TerminalGraphSegment.program_state_eq_q6 TerminalGraphSupport.rawEnd_subset true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 (dummy++m4) placedInput
  have replacement := newReplacement.trans oldReplacement
  change run (SegmentOB5.program true) (dummy++m4) a3=v4
  rw [←replacement]
  have shape : TerminalGraphSegment.program true=OwnQ5Endpoint.centerT++field5 := by
    simp only [TerminalGraphSegment.program,field5,if_true]
  change run (TerminalGraphSegment.program true) (dummy++m4) a3=v4
  rw [shape,run_append]
  have drop : (dummy++m4).drop (measurementCount OwnQ5Endpoint.centerT)=m4 := by simp [dummy]
  rw [drop,centerEq]
  exact h4

theorem kernel5_field_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (KernelOB5.segH true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  let oldRecords := dummy++m4
  let v4' := run field5 m4 v3
  have unEq := field5_unhosted_state hn hlo ho x Y hx0 hx s t m1 m2 m3 m4 hg0 hs0 hf hin
    phase same value v1 v2 v3 v4' h1 h2 h3 rfl
  change run (SegmentOB5.program true) oldRecords a3=v4' at unEq
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have fresh := SegmentOB5.program_spec true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 oldRecords placedInput
  have inS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 placedInput
  have outS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero _ _ fresh.2
  have hostBits := encoded_host_bits5 x hx0 hx origin t3 a3 facts.trace encEq e3
  have in2409 : a3.basis (base 2409)=false := inS.1
  have in2410 : a3.basis (base 2410)=false := inS.2
  have in511 : a3.basis (base 511)=true := hostBits.1
  have in1542 : a3.basis (base 1542)=false := hostBits.2
  have out2409 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2409)=false := outS.1
  have out2410 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2410)=false := outS.2
  have away (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 := by
    intro mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have e := base_injective eq
    omega
  have inT (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
    (paired.2.1 _ (away i hi)).symm
  have freeP := KernelOB5.seg_free true
  have freeQ511 : base 511∉wires field5 := field_free.1
  have freeQ1542 : base 1542∉wires field5 := field_free.2
  have hosted := hosted_pair5 (SegmentOB5.program true) field5 a3 v3 oldRecords m4
    freeP.1 freeP.2 freeQ511 freeQ1542 in2409 in511 in2410 in1542
    ((inT 2409 (by omega)).trans in2409) ((inT 511 (by omega)).trans in511)
    ((inT 2410 (by omega)).trans in2410) ((inT 1542 (by omega)).trans in1542)
    out2409 out2410 unEq
  change run (KernelOB5.segH true) oldRecords a3=v4
  rw [show KernelOB5.segH true=[.X (base 511)]++
    (renameProgram HostOB5.hostSwap (SegmentOB5.program true)++[.X (base 511)]) from rfl,hosted]
  simpa only [hostField5] using h4

theorem kernel5_states
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 v5 v6 v7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4)
    (h5 : run (skywalkArithmeticClear base) m5 v4=v5)
    (h6 : run (stackReverseT) m6 v5=v6)
    (h7 : run (NativeFirstKnown.inverse base) m7 v6=v7) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s v7 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have old4 := kernel5_field_state hn hlo ho hf x Y hx0 hx s t m1 m2 m3 m4 hin hg0 hs0
    phase same value v1 v2 v3 v4 h1 h2 h3 h4
  exact KernelOB5.program_states true hn hlo ho hf x Y hx0 hx s
    m1 m2 m3 (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) m5 m6 m7
    hin hg0 hs0 a1 a2 a3 v4 v5 v6 v7 rfl rfl rfl old4 h5 h6 h7

theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  let P : State → State → Prop := fun initial out =>
    initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) hostField5 (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hp hs hv
      exact kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 hp hs hv v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 h4 h5 h6 h7) t m
  simpa only [kernel5,List.append_assoc] using all phase same value

end ECDSAAdd.Entrant.TerminalGraphEntryRaw


-- TERMINAL GRAPH COMPONENT TerminalSelected
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] run wires kernel5
def field5S : Program := TerminalGraphSW.replayS true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def kernel5S : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostField5S ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem selField5 : SW.Sel (base 2400) 1020 field5S field5 := by
  have r:=TerminalGraphSW.selReplay_sel TerminalGraphSupport.half_subset true
  have old:=Q5FusionFields.selField5
  have canonAway : base 2400∉wires OwnQ5Endpoint.canonT := by
    intro h
    exact old.away (by simp only [Q5FusionFields.field5S,wires_append,Finset.mem_union];exact Or.inr (Or.inr h))
  have cp:=SW.Sel.refl (base 2400) HalfFieldOB5.copyN SW.selCenter_away.2.2
  have cn:=SW.Sel.refl (base 2400) OwnQ5Endpoint.canonT canonAway
  simpa only [field5S,field5,Nat.add_zero] using r.append (cp.append cn)

theorem selHostField5 : SW.Sel (base 2400) 1020 hostField5S hostField5 := by
  have r := (selField5.rename_inj HostOB5.hostSwap HostOB5.hostSwap_injective).castb SW.selHost_fix
  have h := (SW.Sel.refl _ _ SW.selX511_away).append
    (r.append (SW.Sel.refl _ _ SW.selX511_away))
  simpa only [hostField5S,hostField5,Nat.zero_add,Nat.add_zero] using h

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 := by
  have native := NativeFirstDirect.prefix_support base
  have known := NativeFirstKnown.inverse_support base
  have fw : base 2400∉wires (NativeFirstDirect.forward base) := fun h => SW.selPrefix_away (native.1 h)
  have iv : base 2400∉wires (NativeFirstKnown.inverse base) := fun h => SW.selPrefix_away (known h)
  have ints := SW.selInt_away
  have h := ((((((SW.Sel.refl _ _ fw).append (SW.Sel.refl _ _ ints.1)).append
    (SW.Sel.refl _ _ SW.selClear_away)).append selHostField5).append
    (SW.Sel.refl _ _ SW.selClear_away)).append (SW.Sel.refl _ _ ints.2)).append (SW.Sel.refl _ _ iv)
  simpa only [kernel5S,kernel5,Nat.zero_add,Nat.add_zero] using h


attribute [local irreducible] kernel5S
def forceControl5 (s : State) : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩

theorem forceControl5_keep (s : State) (q : Wire) (hq : q≠base 2400) :
    (forceControl5 s).basis q=s.basis q := by simp [forceControl5,writeBit,Function.update_of_ne hq]

theorem forceControl5_true (s : State) : (forceControl5 s).basis (base 2400)=true := by
  simp [forceControl5,writeBit]

/-- The shortened selector-free division receives a half-centered numerator. -/
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := forceControl5 s
  let b := forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := forceControl5_true s
  have bb : b.basis (base 2400)=true := forceControl5_true t
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [forceControl5_true,forceControl5_true]
    · rw [forceControl5_keep t q e,forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong := kernel5_correct hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half
  obtain ⟨equiv,_⟩ := selKernel5.eq m b bb
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab,←equiv] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree := pool_run_agrees kernel5S (wires kernel5S) (Finset.Subset.refl _) m t b rfl
    (fun q hq => (forceControl5_keep t q (fun e => selKernel5.away (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run kernel5S m t).basis q=(run kernel5S m b).basis q := by
    by_cases used : q∈wires kernel5S
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e => numAway (e ▸ hq))
  · intro q hq
    by_cases e : q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ selKernel5.away).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (forceControl5_keep s q e))


end ECDSAAdd.Entrant.TerminalGraphEntryRaw


-- TERMINAL GRAPH COMPONENT TerminalEntrySupport
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraphEntrySupport
open Arithmetic MappedCompressed TerminalGraphEntryRaw
attribute [local irreducible] wires
 theorem field_subset : wires field5⊆wires Q6EndpointEntryRaw.field5 := by
  simp only [field5,Q6EndpointEntryRaw.field5,wires_append]
  exact Finset.union_subset_union (TerminalGraphReplay.replay_subset_old true) (Finset.Subset.refl _)
 theorem host_subset : wires hostField5⊆wires Q6EndpointEntryRaw.hostField5 := by
  have h:=TerminalGraphReplay.rename_subset HostOB5.hostSwap _ _ field_subset
  simp only [hostField5,Q6EndpointEntryRaw.hostField5,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
 theorem hostS_subset : wires hostField5S⊆wires Q6EndpointEntryRaw.hostField5 :=
  selHostField5.sub.wires_sub.trans host_subset
 theorem host1542_free : base 1542∉wires hostField5 := by
  intro used
  apply TerminalGraphSegment.hosted1542_free true
  have sub : wires field5⊆wires (TerminalGraphSegment.program true) := by
   simp only [field5,TerminalGraphSegment.program,if_true,wires_append]
   exact Finset.subset_union_right
  have h:=TerminalGraphReplay.rename_subset HostOB5.hostSwap _ _ sub
  have full : wires hostField5⊆wires (TerminalGraphSegment.segH true) := by
   simp only [hostField5,TerminalGraphSegment.segH,wires_append]
   exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
  exact full used
 theorem hostS1542_free : base 1542∉wires hostField5S := fun h=>host1542_free (selHostField5.sub.wires_sub h)
end ECDSAAdd.Entrant.TerminalGraphEntrySupport


-- TERMINAL GRAPH COMPONENT TerminalPhaseKernels
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryQ5
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5
  TerminalGraphEntryRaw Q5Global718
attribute [local irreducible] run wires TerminalGraphEntryRaw.kernel5 TerminalGraphEntryRaw.kernel5S

def kernel5 : Program:=Q5FusionPhase.relocated hostField5
def kernel5S : Program:=Q5FusionPhase.relocated hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free : base 1026∉wires hostField5 := by
 exact fun used=>EndpointEntryQ5.hostField5_free (TerminalGraphEntrySupport.host_subset used)
theorem hostField5S_free : base 1026∉wires hostField5S := by
 exact fun used=>EndpointEntryQ5.hostField5_free (TerminalGraphEntrySupport.hostS_subset used)
theorem old_shape : Q5FusionPhase.kernel hostField5=TerminalGraphEntryRaw.kernel5 := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,TerminalGraphEntryRaw.kernel5,List.append_assoc]
theorem old_shapeS : Q5FusionPhase.kernel hostField5S=TerminalGraphEntryRaw.kernel5S := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,TerminalGraphEntryRaw.kernel5S,List.append_assoc]
theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old := TerminalGraphEntryRaw.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have contract : DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5) m t) := by
    simpa only [old_shape] using old
  have eq := Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5 true
    hin same hostField5_free contract
  rw [kernel5,eq]
  exact contract

theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old := TerminalGraphEntryRaw.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q5FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shapeS] using old.2.2
  have eq := Q5FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S
    hin same hostField5S_free frame
  simp only [kernel5S,eq,old_shapeS]
  exact old


end ECDSAAdd.Entrant.TerminalGraphEntryQ5


-- TERMINAL GRAPH COMPONENT TerminalKernelsQ6
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 TerminalGraphEntryRaw
attribute [local irreducible] run wires

def kernel5 : Program:=Q6FusionPhase.relocated TerminalGraphEntryRaw.hostField5
def kernel5S : Program:=Q6FusionPhase.relocated TerminalGraphEntryRaw.hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free1541 : base 1541∉wires TerminalGraphEntryRaw.hostField5 := by
 exact fun used=>OwnEndpointEntryQ6.hostField5_free1541 (TerminalGraphEntrySupport.host_subset used)
theorem hostField5S_free1541 : base 1541∉wires TerminalGraphEntryRaw.hostField5S := by
 exact fun used=>OwnEndpointEntryQ6.hostField5_free1541 (TerminalGraphEntrySupport.hostS_subset used)

theorem outer_shape (F : Program) : Q6FusionPhase.kernel F=Q5FusionPhase.relocated F := by
 simp only [Q6FusionPhase.kernel,Q5FusionPhase.relocated,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase]
theorem old_shape_kernel5 : Q6FusionPhase.kernel TerminalGraphEntryRaw.hostField5=TerminalGraphEntryQ5.kernel5 := by
 simpa only [TerminalGraphEntryQ5.kernel5] using outer_shape TerminalGraphEntryRaw.hostField5
theorem old_shape_kernel5S : Q6FusionPhase.kernel TerminalGraphEntryRaw.hostField5S=TerminalGraphEntryQ5.kernel5S := by
 simpa only [TerminalGraphEntryQ5.kernel5S] using outer_shape TerminalGraphEntryRaw.hostField5S
theorem kernel5_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=TerminalGraphEntryQ5.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel TerminalGraphEntryRaw.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m TerminalGraphEntryRaw.hostField5 hin same hostField5_free1541 frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
theorem kernel5S_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=TerminalGraphEntryQ5.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel TerminalGraphEntryRaw.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m TerminalGraphEntryRaw.hostField5S hin same hostField5S_free1541 frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old

end ECDSAAdd.Entrant.TerminalGraphEntryQ6


-- TERMINAL GRAPH COMPONENT TerminalGeometryQ6
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryGeometry
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires run
set_option maxHeartbeats 1000000 in
theorem host_support (P : Program) (hp:wires P⊆OB5Support.segSites) : wires ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)]))⊆OB5Support.logicalSites := by
  have mem (i : Nat) (hi : i ∈ OB5Support.logicalIndices) : base i ∈ OB5Support.logicalSites :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have m511 : base 511 ∈ OB5Support.logicalSites := mem 511 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have m1542 : base 1542 ∈ OB5Support.logicalSites := mem 1542 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have x (r : Wire) (hr : r ∈ wires [Instr.X (base 511)]) : r = base 511 := by
    simpa [wires, Instr.wires] using hr
  intro q hq
  simp only [wires_append, Finset.mem_union] at hq
  rcases hq with h|h|h
  · rw [x q h]; exact m511
  · rw [renameProgram_support] at h
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp h
    have hs := hp hold
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    unfold HostOB5.hostSwap
    split_ifs with c d e f
    · exact m511
    · exfalso
      have := base_injective d
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · exact m1542
    · exfalso
      have := base_injective f
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · apply mem
      have c' : i ≠ 2409 := fun h => c (by rw [h])
      have e' : i ≠ 2410 := fun h => e (by rw [h])
      simp only [OB5Support.segIndices, OB5Support.logicalIndices, List.mem_append, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
  · rw [x q h]; exact m511

theorem raw_support : wires TerminalGraphEntryRaw.kernel5⊆OB5Support.logicalSites := by
 have first:=(NativeFirstDirect.prefix_support base).1.trans OB5Support.prefixSites_sub_logical
 have f:=stackForwardT_subset.trans (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
 have c:=OB5Support.clear_support_logical
 have b:=host_support TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.field_support
 have r:=stackReverseT_subset.trans (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
 have last:=(NativeFirstKnown.inverse_support base).trans OB5Support.prefixSites_sub_logical
 simp only [TerminalGraphEntryRaw.kernel5,wires_append,Finset.union_subset_iff,and_assoc]
 exact ⟨first,f,c,b,c,r,last⟩

theorem q5support (F : Program) (old:wires (Q5FusionPhase.kernel F)⊆OB5Support.logicalSites) :
 wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites := by
 simp only [Q5FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
 simp only [Q5FusionPhase.relocated,wires_append,Finset.union_subset_iff]
 exact ⟨OwnQ5Integer.rename_support _ old.1,old.2.1,OwnQ5Integer.rename_support _ old.2.2⟩
theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=719∨i=1541) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1541
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 719 (Or.inl rfl)
  · by_cases b:q=base 719
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1541 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)

theorem q6support (F : Program) (old : wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←TerminalGraphEntryQ6.outer_shape] at old
  simp only [Q6FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q6FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩

theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q6FusionPhase.relocated G) (Q6FusionPhase.relocated F) := by
  have fp : base 2400∉wires q5First := by
    simpa only [q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires q5Last := by
    simpa only [q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q6FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh

end ECDSAAdd.Entrant.TerminalGraphEntryGeometry
namespace ECDSAAdd.Entrant.TerminalGraphEntryQ6
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires

theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
 apply TerminalGraphEntryGeometry.q6support
 apply TerminalGraphEntryGeometry.q5support
 simpa only [TerminalGraphEntryQ5.old_shape] using TerminalGraphEntryGeometry.raw_support

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 :=
 TerminalGraphEntryGeometry.sel _ _ TerminalGraphEntryRaw.selHostField5

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 selKernel5.sub.wires_sub.trans kernel5_support
end ECDSAAdd.Entrant.TerminalGraphEntryQ6


-- TERMINAL GRAPH COMPONENT TerminalKernelsQ7
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 TerminalGraphEntryRaw
attribute [local irreducible] run wires

def kernel5 : Program:=Q7FusionPhase.relocated TerminalGraphEntryRaw.hostField5
def kernel5S : Program:=Q7FusionPhase.relocated TerminalGraphEntryRaw.hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free1542 : base 1542∉wires TerminalGraphEntryRaw.hostField5 := TerminalGraphEntrySupport.host1542_free
theorem hostField5S_free1542 : base 1542∉wires TerminalGraphEntryRaw.hostField5S := TerminalGraphEntrySupport.hostS1542_free

theorem outer_shape (F : Program) : Q7FusionPhase.kernel F=Q6FusionPhase.relocated F := Q7FusionPhase.old_shape F
theorem old_shape_kernel5 : Q7FusionPhase.kernel TerminalGraphEntryRaw.hostField5=TerminalGraphEntryQ6.kernel5 := by
 simpa only [TerminalGraphEntryQ6.kernel5] using outer_shape TerminalGraphEntryRaw.hostField5
theorem old_shape_kernel5S : Q7FusionPhase.kernel TerminalGraphEntryRaw.hostField5S=TerminalGraphEntryQ6.kernel5S := by
 simpa only [TerminalGraphEntryQ6.kernel5S] using outer_shape TerminalGraphEntryRaw.hostField5S
theorem kernel5_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=TerminalGraphEntryQ6.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel TerminalGraphEntryRaw.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m TerminalGraphEntryRaw.hostField5 hin same hostField5_free1542 frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
theorem kernel5S_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=TerminalGraphEntryQ6.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel TerminalGraphEntryRaw.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m TerminalGraphEntryRaw.hostField5S hin same hostField5S_free1542 frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old

end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7


-- TERMINAL GRAPH COMPONENT TerminalGeometryQ7
namespace ECDSAAdd.Entrant.TerminalGraphEntryGeometryQ7
open Arithmetic MappedCompressed Q7IntegerHost
attribute [local irreducible] wires
 theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=720∨i=1542) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1542
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 720 (Or.inl rfl)
  · by_cases b:q=base 720
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1542 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq
 theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)
 theorem support (F : Program) (old : wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q7FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←Q7FusionPhase.old_shape] at old
  simp only [Q7FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q7FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩
 theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q7FusionPhase.relocated G) (Q7FusionPhase.relocated F) := by
  have fix6 : Q6IntegerHost.swap (base 2400)=base 2400 := by decide +kernel
  have fp : base 2400∉wires Q7FusionPhase.q6First := by
    unfold Q7FusionPhase.q6First
    apply OwnPlusHost.rename_avoid _ _ _ fix6
    simpa only [Q6IntegerHost.q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires Q7FusionPhase.q6Last := by
    unfold Q7FusionPhase.q6Last
    apply OwnPlusHost.rename_avoid _ _ _ fix6
    simpa only [Q6IntegerHost.q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q7FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh
end ECDSAAdd.Entrant.TerminalGraphEntryGeometryQ7
namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic MappedCompressed
attribute [local irreducible] wires
 theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
  apply TerminalGraphEntryGeometryQ7.support
  exact TerminalGraphEntryQ6.kernel5_support
 theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 :=
  TerminalGraphEntryGeometryQ7.sel _ _ TerminalGraphEntryRaw.selHostField5
 theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
  selKernel5.sub.wires_sub.trans kernel5_support
end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7


-- TERMINAL GRAPH COMPONENT TerminalCallers
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section
namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- A renamed replay receives the same pool as a canonical virtual state,
while its actual numerator has already been half-centered. -/
theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires OwnTerminalGraphEntryQ7.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f OwnTerminalGraphEntryQ7.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := OwnTerminalGraphEntryQ7.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective OwnTerminalGraphEntryQ7.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run OwnTerminalGraphEntryQ7.kernel5S m b).basis
      (run (renameProgram f OwnTerminalGraphEntryQ7.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain OwnTerminalGraphEntryQ7.kernel5S sites m t q image).trans (same q hq)


end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires toffoliCount measurementCount
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) OwnTerminalGraphEntryQ7.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ kernel5S_support

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (OwnTerminalGraphEntryQ7.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
end


namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] run arithEntryS arithS fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep
end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7


-- TERMINAL GRAPH COMPONENT TerminalResources
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem raw_counts_diff (divide : Bool) :
 toffoliCount (rawEnd divide)+(if divide then 254 else 0)=toffoliCount (OneFlagReplay.rawEnd divide) ∧
 measurementCount (rawEnd divide)+(if divide then 255 else 0)=measurementCount (OneFlagReplay.rawEnd divide) := by
 have nc:=TerminalGraphEndpoint.half_counts divide base (base 2409)
 have nw:=transcriptSelectWindow_counts (base 2400) (base 510) (base 2409)
   (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (TerminalGraphEndpoint.half divide base (base 2409))
 have oc:=Q6EndpointCell.endpoint_counts divide base (base 2400) (base 510) (base 2409)
   (mixedTranscriptUnitTrace.getD 510 (false,false)).1
 change toffoliCount (transcriptSelectWindow _ _ _ _ _)+_=_ ∧ measurementCount (transcriptSelectWindow _ _ _ _ _)+_=_
 cases divide <;> simp only [Bool.false_eq_true,ite_false,ite_true] at nc oc ⊢ <;>
   simp only [OneFlagReplay.rawEnd] <;> constructor <;> omega

theorem packet_counts_diff (divide : Bool) :
 toffoliCount (endPacket divide)+(if divide then 254 else 0)=toffoliCount (OneFlagReplay.endPacket divide) ∧
 measurementCount (endPacket divide)+(if divide then 255 else 0)=measurementCount (OneFlagReplay.endPacket divide) := by
 simpa only [endPacket,OneFlagReplay.endPacket,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using raw_counts_diff divide

theorem logical_counts_diff (divide : Bool) :
 toffoliCount (logicalReplay divide)+(if divide then 254 else 0)=toffoliCount (OneFlagReplay.logicalReplay divide) ∧
 measurementCount (logicalReplay divide)+(if divide then 255 else 0)=measurementCount (OneFlagReplay.logicalReplay divide) := by
 have h:=packet_counts_diff divide
 cases divide <;> simp only [logicalReplay,OneFlagReplay.logicalReplay,firstPacket,groups,Bool.false_eq_true,ite_false,ite_true,toffoliCount_append,measurementCount_append] at h ⊢ <;> constructor <;> omega

theorem replay_counts_diff (divide : Bool) :
 toffoliCount (replay divide)+(if divide then 254 else 0)=toffoliCount (OneFlagReplay.replay divide) ∧
 measurementCount (replay divide)+(if divide then 255 else 0)=measurementCount (OneFlagReplay.replay divide) := by
 simpa only [replay,OneFlagReplay.replay,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using logical_counts_diff divide
end ECDSAAdd.Entrant.TerminalGraphReplay
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem counts_diff (divide : Bool) :
 toffoliCount (program divide)+(if divide then 254 else 0)=toffoliCount (OneFlagSegment.program divide) ∧
 measurementCount (program divide)+(if divide then 255 else 0)=measurementCount (OneFlagSegment.program divide) := by
 have h:=TerminalGraphReplay.replay_counts_diff divide
 cases divide <;> simp only [program,OneFlagSegment.program,Bool.false_eq_true,ite_false,ite_true,toffoliCount_append,measurementCount_append] at h ⊢ <;> constructor <;> omega

theorem segH_counts_diff (divide : Bool) :
 toffoliCount (segH divide)+(if divide then 254 else 0)=toffoliCount (OneFlagSegment.segH divide) ∧
 measurementCount (segH divide)+(if divide then 255 else 0)=measurementCount (OneFlagSegment.segH divide) := by
 have h:=counts_diff divide
 simpa only [segH,OneFlagSegment.segH,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,toffoliCount,measurementCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero] using h
end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalSlots
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic MappedCompressed

theorem selectWindow_slots (b source flag : Wire) (constant : Bool) (body : Program) :
 Challenge.gateSlots (transcriptSelectWindow b source flag constant body)=
 Challenge.gateSlots body+(if constant then 8 else 3) := by
 cases constant <;> simp [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

attribute [local irreducible] Challenge.gateSlots TerminalGraph.decoder

theorem raw_slots_le (divide : Bool)
 (hs : Challenge.gateSlots (TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))))≤24000) :
 Challenge.gateSlots (rawEnd divide)≤Challenge.gateSlots (OneFlagReplay.rawEnd divide)+24000 := by
 have n:=selectWindow_slots (base 2400) (base 510) (base 2409) (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (TerminalGraphEndpoint.half divide base (base 2409))
 have o:=selectWindow_slots (base 2400) (base 510) (base 2409) (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (Q6EndpointCell.halfE divide base (base 2409))
 change Challenge.gateSlots (transcriptSelectWindow _ _ _ _ _)≤Challenge.gateSlots (transcriptSelectWindow _ _ _ _ _)+24000
 rw [n,o]
 cases divide
 · simp only [TerminalGraphEndpoint.half,Q6EndpointCell.halfE,Bool.false_eq_true,ite_false];omega
 · simp only [TerminalGraphEndpoint.half,ite_true];omega

theorem replay_slots_le (divide : Bool)
 (hs : Challenge.gateSlots (TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))))≤24000) :
 Challenge.gateSlots (replay divide)≤Challenge.gateSlots (OneFlagReplay.replay divide)+24000 := by
 have h:=raw_slots_le divide hs
 cases divide <;> simp only [replay,OneFlagReplay.replay,logicalReplay,OneFlagReplay.logicalReplay,firstPacket,groups,endPacket,OneFlagReplay.endPacket,Bool.false_eq_true,ite_false,ite_true,Baselines.rename_gateSlots,Challenge.gateSlots_append] at h ⊢ <;> omega
end ECDSAAdd.Entrant.TerminalGraphReplay
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed
attribute [local irreducible] Challenge.gateSlots TerminalGraph.decoder

theorem slots_le (divide : Bool)
 (hs : Challenge.gateSlots (TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))))≤24000) :
 Challenge.gateSlots (program divide)≤Challenge.gateSlots (OneFlagSegment.program divide)+24000 := by
 have h:=TerminalGraphReplay.replay_slots_le divide hs
 cases divide <;> simp only [program,OneFlagSegment.program,Bool.false_eq_true,ite_false,ite_true,Challenge.gateSlots_append] at h ⊢ <;> omega

theorem segH_slots_le (divide : Bool)
 (hs : Challenge.gateSlots (TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base 2409))))≤24000) :
 Challenge.gateSlots (segH divide)≤Challenge.gateSlots (OneFlagSegment.segH divide)+24000 := by
 have h:=slots_le divide hs
 simp only [segH,OneFlagSegment.segH,Challenge.gateSlots_append,Baselines.rename_gateSlots]
 omega
end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalPhysicalOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.TerminalGraphPhysicalOnly
open Arithmetic MappedCompressed

def actualDecoder (sign : Nat) : Program :=
 TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base sign)))
attribute [local irreducible] GatePhysical actualDecoder TerminalGraph.decoder

theorem physical : GatePhysical (actualDecoder 2409) :=
 physicalGateCheck_correct _ (by decide +kernel)

theorem slots : Challenge.gateSlots (actualDecoder 2409)≤23900 := by
 decide +kernel
end ECDSAAdd.Entrant.TerminalGraphPhysicalOnly


-- TERMINAL GRAPH COMPONENT TerminalSupportPhysical
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphReplay
open Arithmetic MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires TerminalGraphEndpoint.half Q6EndpointCell.halfE
 theorem half_physical (d : Bool) : GatePhysical (TerminalGraphEndpoint.half d base (base 2409)) :=by
  cases d
  · simpa only [TerminalGraphEndpoint.half, Bool.false_eq_true, if_false] using Q6EndpointCell.half_physical false base base_injective
  · simpa only [TerminalGraphEndpoint.half, if_true, TerminalGraphPhysicalOnly.actualDecoder] using TerminalGraphPhysicalOnly.physical
 theorem rawEnd_physical (d : Bool) : GatePhysical (rawEnd d) :=by
  exact transcriptWindow_physical _ _ _ _ _ (by decide) (by decide) (half_physical d)
 theorem endPacket_physical (d : Bool) : GatePhysical (endPacket d) :=
  gatePhysical_rename _ (shifted Placement5.pi0).injective _ (rawEnd_physical d)
 theorem replay_physical (d : Bool) (hn : (skywalkSharedWires base).Nodup)
  (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
  GatePhysical (replay d) :=by
  have first:=OneFlagReplay.firstPacket_physical d hn ho hf
  have rest:=OneFlagReplay.groups_physical d 1 101 (by decide) hn ho (Replay5.letters_layouts hf)
  have last:=endPacket_physical d
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by decide))
  cases d <;>simp only[logicalReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,rest⟩,first⟩
  · exact ⟨⟨first,rest⟩,last⟩
end ECDSAAdd.Entrant.TerminalGraphReplay
namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed CompressedFieldSupport HalfFieldOB5
 theorem physical (d : Bool) (hn : (skywalkSharedWires base).Nodup)
  (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
  GatePhysical (program d) :=by
  have c:=OwnQ5Endpoint.endpoint_physical hn
  have r:=TerminalGraphReplay.replay_physical d hn ho hf
  cases d <;>simp only[program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨c.1,c.2.2,r,c.2.1⟩
  · exact ⟨c.1,r,c.2.2,c.2.1⟩
end ECDSAAdd.Entrant.TerminalGraphSegment

namespace ECDSAAdd.Entrant.TerminalGraphSegment
open Arithmetic MappedCompressed
 theorem gateSlots_le (d : Bool) : Challenge.gateSlots (program d)≤14124000 :=by
  have h:=slots_le d (by have h:=TerminalGraphPhysicalOnly.slots;exact le_trans h (by decide))
  have old:=OneFlagSegment.gateSlots_le d
  omega
end ECDSAAdd.Entrant.TerminalGraphSegment


-- TERMINAL GRAPH COMPONENT TerminalKernelResources
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryResources
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] wires run toffoliCount measurementCount

theorem field_sub : InstrSub TerminalGraphEntryRaw.field5 (TerminalGraphSegment.program true) := by
 constructor
 · intro i hi
   left
   change i∈OwnQ5Endpoint.centerT++TerminalGraphEntryRaw.field5
   exact List.mem_append_right _ hi
 · change Challenge.gateSlots TerminalGraphEntryRaw.field5≤
     Challenge.gateSlots (OwnQ5Endpoint.centerT++TerminalGraphEntryRaw.field5)
   rw [Challenge.gateSlots_append]
   omega

theorem raw_physical : GatePhysical TerminalGraphEntryRaw.kernel5 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have f:=field_sub.physical (TerminalGraphSegment.physical true cfg.1 cfg.2.1 cfg.2.2)
 have hosted:=Q5FusionFields.host_physical TerminalGraphEntryRaw.field5 f
 have first:=(NativeFirstDirect.programs_physical base base_pool_nodup).1
 have last:=NativeFirstKnown.inverse_physical base base_pool_nodup
 simp only [TerminalGraphEntryRaw.kernel5,gatePhysical_append]
 exact ⟨⟨⟨⟨⟨⟨first,stackForwardT_physical⟩,mappedClear_physical⟩,hosted⟩,
   mappedClear_physical⟩,stackReverseT_physical⟩,last⟩

theorem raw_slots : Challenge.gateSlots TerminalGraphEntryRaw.kernel5≤20524006 := by
 have native:=Baselines.nativeFirst_gateSlots_le base
 have integer:=Stack5.slots_le base base_pool_nodup 1 511 (by omega)
 have f:=StackOB5.forward_counts.2.2
 have r:=StackOB5.reverse_counts.2.2
 have ft:=stackForwardT_metrics.2.2
 have rt:=stackReverseT_metrics.2.2
 have field:=field_sub.slots.trans (TerminalGraphSegment.gateSlots_le true)
 have clear:Challenge.gateSlots (skywalkArithmeticClear base)=3:=by
   simp [skywalkArithmeticClear,skywalkTerminalClear,Challenge.gateSlots,Challenge.instructionSlots]
 have x:Challenge.gateSlots [.X (base 511)]=1:=rfl
 simp only [TerminalGraphEntryRaw.kernel5,TerminalGraphEntryRaw.hostField5,
   Challenge.gateSlots_append,Baselines.rename_gateSlots,clear,x]
 omega

/-- Exact counts use the new field body and protected integer budget, not a mutable old parent. -/
theorem raw_counts : toffoliCount TerminalGraphEntryRaw.kernel5=1048650 ∧
 measurementCount TerminalGraphEntryRaw.kernel5=720512 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have r:=TerminalGraphReplay.replay_counts_diff true
 simp only[ite_true] at r
 have oldr:=OneFlagReplay.replay_counts_eq true cfg.1 (cfg.2.1 _ (by simp))
 have fields : toffoliCount TerminalGraphEntryRaw.field5+254=toffoliCount Q6EndpointEntryRaw.field5 ∧
     measurementCount TerminalGraphEntryRaw.field5+255=measurementCount Q6EndpointEntryRaw.field5 := by
  simp only [TerminalGraphEntryRaw.field5,Q6EndpointEntryRaw.field5,toffoliCount_append,measurementCount_append]
  constructor <;> omega
 have ren:=renameProgram_counts HostOB5.hostSwap TerminalGraphEntryRaw.field5
 have renOld:=renameProgram_counts HostOB5.hostSwap Q6EndpointEntryRaw.field5
 have prior:=EndpointEntryResources.raw_counts
 simp only [TerminalGraphEntryRaw.kernel5,TerminalGraphEntryRaw.hostField5,
   Q6EndpointEntryRaw.kernel5,Q6EndpointEntryRaw.hostField5,
   toffoliCount_append,measurementCount_append,ren.1,ren.2,renOld.1,renOld.2] at prior ⊢
 constructor <;> omega

theorem q5_physical (F : Program) (h:GatePhysical (Q5FusionPhase.kernel F)) :
 GatePhysical (Q5FusionPhase.relocated F) := by
 simp only [Q5FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q5FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.2.2⟩

theorem q6_physical (F : Program) (h:GatePhysical (Q5FusionPhase.relocated F)) :
 GatePhysical (Q6FusionPhase.relocated F) := by
 rw [←TerminalGraphEntryQ6.outer_shape] at h
 simp only [Q6FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q6FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.2.2⟩

theorem q7_physical (F : Program) (h:GatePhysical (Q6FusionPhase.relocated F)) :
 GatePhysical (Q7FusionPhase.relocated F) := by
 rw [←Q7FusionPhase.old_shape] at h
 simp only [Q7FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q7FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q7IntegerHost.swap Q7IntegerHost.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q7IntegerHost.swap Q7IntegerHost.swap.injective _ h.2.2⟩

theorem outer_slots (F : Program) :
 Challenge.gateSlots (Q7FusionPhase.relocated F)=Challenge.gateSlots (Q5FusionPhase.kernel F) := by
 simp only [Q7FusionPhase.relocated,Q7FusionPhase.q6First,Q7FusionPhase.q6Last,
   Q5FusionPhase.kernel,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase,
   Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem outer_counts (F : Program) :
 toffoliCount (Q7FusionPhase.relocated F)=toffoliCount (Q5FusionPhase.kernel F) ∧
 measurementCount (Q7FusionPhase.relocated F)=measurementCount (Q5FusionPhase.kernel F) := by
 have a:=Q7FusionPhase.relocated_counts F
 rw [Q7FusionPhase.old_shape] at a
 have b:=Q6FusionPhase.relocated_counts F
 rw [TerminalGraphEntryQ6.outer_shape] at b
 have c:=Q5FusionPhase.relocated_counts F
 exact ⟨a.1.trans (b.1.trans c.1),a.2.trans (b.2.trans c.2)⟩
end ECDSAAdd.Entrant.TerminalGraphEntryResources

namespace ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk TerminalGraphEntryRaw
attribute [local irreducible] run wires toffoliCount measurementCount

theorem kernel5_physical : GatePhysical kernel5 := by
 apply TerminalGraphEntryResources.q7_physical
 apply TerminalGraphEntryResources.q6_physical
 apply TerminalGraphEntryResources.q5_physical
 simpa only [TerminalGraphEntryQ5.old_shape] using TerminalGraphEntryResources.raw_physical

theorem kernel5S_physical : GatePhysical kernel5S := selKernel5.sub.physical kernel5_physical

theorem kernel5_slots_le : Challenge.gateSlots kernel5≤20524006 := by
 rw [kernel5,TerminalGraphEntryResources.outer_slots,TerminalGraphEntryQ5.old_shape]
 exact TerminalGraphEntryResources.raw_slots

theorem kernel5S_slots_le : Challenge.gateSlots kernel5S≤20524006 :=
 selKernel5.sub.slots.trans kernel5_slots_le

theorem kernel5_counts : toffoliCount kernel5=1048650 ∧ measurementCount kernel5=720512 := by
 have h:=TerminalGraphEntryResources.outer_counts TerminalGraphEntryRaw.hostField5
 rw [TerminalGraphEntryQ5.old_shape] at h
 simpa only [kernel5,h.1,h.2] using TerminalGraphEntryResources.raw_counts

theorem kernel5S_counts : toffoliCount kernel5S=1047630 ∧ measurementCount kernel5S=720512 := by
 have c:=kernel5_counts
 have t:=selKernel5.tc
 have m:=selKernel5.mc
 constructor <;> omega

theorem arithEntryS_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 GatePhysical (arithEntryS L) := by
 apply gatePhysical_rename_support (wireFn2 L) kernel5S
 · intro a ha b hb eq
   exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernel5S_support ha))
     b (ArithmeticOB5.logical_sub_old (kernel5S_support hb)) eq
 · exact kernel5S_physical

theorem arithEntryS_counts (L : ControlledPointLayout) :
 toffoliCount (arithEntryS L)=1047630 ∧ measurementCount (arithEntryS L)=720512 := by
 simpa only [arithEntryS,(renameProgram_counts (wireFn2 L) kernel5S).1,
   (renameProgram_counts (wireFn2 L) kernel5S).2] using kernel5S_counts

theorem arithEntryS_gateSlots_le (L : ControlledPointLayout) :
 Challenge.gateSlots (arithEntryS L)≤20524006 := by
 simpa only [arithEntryS,Baselines.rename_gateSlots] using kernel5S_slots_le

theorem fusedDivisionF_counts (L : ControlledPointLayout) (hw:L.Widths) (k:Fp) :
 toffoliCount (fusedDivisionF L k)=1048396 ∧ measurementCount (fusedDivisionF L k)=721279 := by
 have a:=EntryFuse.fusedY_counts L hw k
 have b:=arithEntryS_counts L
 simp only [fusedDivisionF,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
 constructor <;> trivial
end ECDSAAdd.Entrant.OwnTerminalGraphEntryQ7


-- TERMINAL GRAPH COMPONENT TerminalOmissions
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEntryOmissions
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 CompressedPointDialog
attribute [local irreducible] wires
private theorem placed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i k : Nat)
 (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
 (free : base i∉wires P) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) P) := by
 rw [renameProgram_support]
 intro h
 obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
 have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
 have back := (placement2 L hw hn).injectiveOnSlots old
   (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
 exact free (back ▸ used)
private theorem logical (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 omega
private theorem entry_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnEntryFuseQ5.kernel5S := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact OwnEntryFuseQ5.kernel5S_1026_free

private theorem q5_free (i : Nat) (hi : i∈[2312,766,765,767,1026]) :
 base i∉wires (Q5FusionPhase.relocated TerminalGraphEntryRaw.hostField5S) := by
 have h:=entry_old i hi
 have newField : base i∉wires TerminalGraphEntryRaw.hostField5S := by
  intro used
  have oldField : base i∉wires Q6EndpointEntryRaw.hostField5 := by
   apply Q6EndpointOmissions.host_free _ i
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega
   · apply Q6EndpointOmissions.field_free
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega
  exact oldField (TerminalGraphEntrySupport.hostS_subset used)
 simp only [OwnEntryFuseQ5.kernel5S,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] at h ⊢
 exact ⟨h.1,newField,h.2.2⟩

private theorem kernel_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∉wires TerminalGraphEntryQ6.kernel5S := by
 by_cases last : i=1541
 · subst i
   simpa only [TerminalGraphEntryQ6.kernel5S] using
    Q6FusionPhase.relocated_1541_free _ TerminalGraphEntryQ6.hostField5S_free1541
 · have prior : i∈[2312,766,765,767,1026] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
   have old:=q5_free i prior
   rw [←TerminalGraphEntryQ6.outer_shape] at old
   simp only [Q6FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q6IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq; exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
      omega
   have first:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.1
   have final:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.2.2
   simpa only [TerminalGraphEntryQ6.kernel5S,Q6FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
     And.intro first (And.intro old.2.1 final)

theorem kernel_free7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires OwnTerminalGraphEntryQ7.kernel5S := by
 by_cases last : i=1542
 · subst i
   simpa only [OwnTerminalGraphEntryQ7.kernel5S] using
    Q7FusionPhase.relocated_1542_free _ TerminalGraphEntrySupport.hostS1542_free
 · have prior : i∈[2312,766,765,767,1026,1541] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto
   have old:=kernel_free i prior
   change base i∉wires (Q6FusionPhase.relocated TerminalGraphEntryRaw.hostField5S) at old
   rw [←Q7FusionPhase.old_shape] at old
   simp only [Q7FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q7IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq;exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior;omega
   change base i∉wires (Q7FusionPhase.relocated TerminalGraphEntryRaw.hostField5S)
   simp only [Q7FusionPhase.relocated,wires_append,Finset.mem_union,not_or]
   exact ⟨OwnPlusHost.rename_avoid _ _ _ fix old.1,old.2.1,OwnPlusHost.rename_avoid _ _ _ fix old.2.2⟩
private theorem logical7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
 theorem entry_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
 L.core.poolWire k∉wires (OwnTerminalGraphEntryQ7.arithEntryS L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 2312 1800
     (logical7 2312 (by simp)) (by rfl) (kernel_free7 2312 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 766 766
     (logical7 766 (by simp)) (by rfl) (kernel_free7 766 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 765 765
     (logical7 765 (by simp)) (by rfl) (kernel_free7 765 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 767 767
     (logical7 767 (by simp)) (by rfl) (kernel_free7 767 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 1026 770
     (logical7 1026 (by simp)) (by rfl) (kernel_free7 1026 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 1541 1285
     (logical7 1541 (by simp)) (by rfl) (kernel_free7 1541 (by simp))
 · exact placed L hw hn OwnTerminalGraphEntryQ7.kernel5S OwnTerminalGraphEntryQ7.kernel5S_support 1542 1286
     (logical7 1542 (by simp)) (by rfl) (kernel_free7 1542 (by simp))
end ECDSAAdd.Entrant.TerminalGraphEntryOmissions


-- TERMINAL GRAPH COMPONENT TerminalEntryProperties
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.TerminalGraphEntryProperties
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount
theorem division_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (OwnTerminalGraphEntryQ7.fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [OwnTerminalGraphEntryQ7.fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    OwnTerminalGraphEntryQ7.arithEntryS_support L hw⟩

theorem division_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (OwnTerminalGraphEntryQ7.fusedDivisionF L k) := by
  simp only [OwnTerminalGraphEntryQ7.fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,OwnTerminalGraphEntryQ7.arithEntryS_physical L hw hn⟩

theorem division_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285,1286]) (c : Fp) :
    L.core.poolWire k∉wires (OwnTerminalGraphEntryQ7.fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [OwnTerminalGraphEntryQ7.fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),TerminalGraphEntryOmissions.entry_avoids L hw hn k hk⟩


theorem division_slots (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 gateSlots (OwnTerminalGraphEntryQ7.fusedDivisionF L k)≤20549006 := by
 have d:=OwnTerminalGraphEntryQ7.arithEntryS_gateSlots_le L
 have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
 simp only [OwnTerminalGraphEntryQ7.fusedDivisionF,EntryFuse.fusedY,gateSlots_append]
 omega

theorem division_counts_diff (Dold : Program)
 (oldCounts : toffoliCount Dold=1048650 ∧ measurementCount Dold=721534)
 (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 toffoliCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k)+254=toffoliCount Dold ∧
 measurementCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k)+255=measurementCount Dold := by
 have a:=OwnTerminalGraphEntryQ7.fusedDivisionF_counts L hw k
 constructor <;> omega
end ECDSAAdd.Entrant.TerminalGraphEntryProperties


-- TERMINAL GRAPH COMPONENT TerminalProducer
-- ONEFLAG COMPONENT ProducerOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphProducer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] wires run toffoliCount measurementCount fastConstAdd fastConstNeg
 def generic (L : ControlledPointLayout) (P : Program) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnTerminalGraphEntryQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L) P cx cy
 def gen (L : ControlledPointLayout) (P : Program) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnTerminalGraphEntryQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L) P cx cy
 theorem generic_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (P : Program) (cx cy : Fp) :
   toffoliCount (generic L P cx cy)+254=toffoliCount (OneFlagProducer.generic L P cx cy) ∧
   measurementCount (generic L P cx cy)+255=measurementCount (OneFlagProducer.generic L P cx cy) := by
  have d:=OwnTerminalGraphEntryQ7.fusedDivisionF_counts L hw (-cy)
  have old:=OwnOneFlagEntryQ7.fusedDivisionF_counts L hw (-cy)
  simp only [generic,OneFlagProducer.generic,All12Generic.generic,toffoliCount_append,measurementCount_append]
  constructor <;> omega
 theorem gen_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (P : Program) (cx cy : Fp) :
   toffoliCount (gen L P cx cy)+254=toffoliCount (OneFlagProducer.gen L P cx cy) ∧
   measurementCount (gen L P cx cy)+255=measurementCount (OneFlagProducer.gen L P cx cy) := by
  have h:=generic_counts_diff L hw P cx cy
  simp only [generic,OneFlagProducer.generic] at h
  simp only [gen,OneFlagProducer.gen,All12Generic.gen,All12Generic.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega
 theorem square_step (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
   (X Y : Fp) (G : Bool) (origin : BasisState) :
   Triple (PointDialogValues L X Y G origin) (OwnDiagAll12PlacedQ7.program L)
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1:Nat) else 0)) Y G origin) := by
  have h:=OwnDiagAll12PlacedQ7.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnDiagAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h
end ECDSAAdd.Entrant.TerminalGraphProducer


-- ONEFLAG COMPONENT ProducerPropertiesOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraphProducer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] wires run fastConstAdd fastConstNeg
 theorem generic_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (ps : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
  wires (generic L P cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (TerminalGraphEntryProperties.division_support L hw)
   (OwnDiagAll12PlacedQ7.support L hw hn) ps cx cy
 theorem gen_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (ps : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
  wires (gen L P cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen,All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn P ps cx cy)
 theorem gen_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (pp : GatePhysical P) (cx cy : Fp) : GatePhysical (gen L P cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (TerminalGraphEntryProperties.division_physical L hw hn)
   (OwnDiagAll12PlacedQ7.physical L hw hn) pp cx cy
theorem terminal_generic_slots_le (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (hD : ∀k,gateSlots (D k) ≤ 20549006)
    (hS : gateSlots S ≤ 8000000) (hP : gateSlots P ≤ 20500006) (cx cy : Fp) :
    gateSlots (All12Generic.generic L D S P cx cy) ≤ 49124000 := by
  have add (k : Fp) : gateSlots (fastConstAdd L L.point.x k) ≤ 15368 := by
    simpa only [fastConstAdd] using FastConst.fastAdd_gateSlots_le
      (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have neg : gateSlots (fastConstNeg L cx) ≤ 17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a := add (-cx)
  have b := add (3*cx-(2^163-1 : Nat))
  have d := hD (-cy)
  have e := exitY_slots L hw cy
  simp only [All12Generic.generic,gateSlots_append]
  omega

theorem terminal_gen_slots_le (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (hD : ∀k,gateSlots (D k) ≤ 20549006)
    (hS : gateSlots S ≤ 8000000) (hP : gateSlots P ≤ 20500006) (cx cy : Fp) :
    gateSlots (All12Generic.gen L D S P cx cy) ≤ 49224000 := by
  have g := terminal_generic_slots_le L hw D S P hD hS hP cx cy
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  simp only [All12Generic.gen,All12Generic.mid,gateSlots_append,rename_gateSlots]
  omega

 theorem gen_slots (L : ControlledPointLayout) (hw:L.Widths) (P : Program)
  (pp : gateSlots P≤20500006) (cx cy : Fp) : gateSlots (gen L P cx cy)≤49224000 :=
  terminal_gen_slots_le L hw _ _ _ (TerminalGraphEntryProperties.division_slots L hw)
   (OwnDiagAll12PlacedQ7.slots L hw) pp cx cy
 theorem generic_free (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (pf : ∀k∈[1800,766,765,767,770,1285,1286],L.core.poolWire k∉wires P)
  (k : Nat) (hk:k∈[1800,766,765,767,770,1285,1286]) (cx cy : Fp) :
  L.core.poolWire k∉wires (generic L P cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
   rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
   (TerminalGraphEntryProperties.division_free L hw hn k hk)
   (OwnDiagAll12PlacedQ7.square_free L hw hn k hk) (pf k hk) cx cy
 theorem gen_ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (halfCorrect : ExitFusionResearch.HalfMultiplyCorrect L P)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
  {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L P cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _ halfCorrect
   (OwnTerminalGraphEntryQ7.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
   (square_step L hw hn) hc
 theorem gen_qubits (P : Program)
  (ps : wires P⊆(OB5Support.sites layout).toFinset)
  (pf : ∀k∈[1800,766,765,767,770,1285,1286],layout.core.poolWire k∉wires P)
  (C : Point) (cx cy : Fp) : qubits (Edges.wrapper layout C cy (gen layout P cx cy))≤1592 := by
  rw [gen,All12Generic.gen_shape]
  apply GenericQ7Geometry.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup P ps cx cy)
  · intro k hk
    exact generic_free layout layout_widths layout_nodup P pf k (List.mem_append_left [1285,1286] hk) cx cy
  · exact generic_free layout layout_widths layout_nodup P pf 1285 (by simp) cx cy
  · exact generic_free layout layout_widths layout_nodup P pf 1286 (by simp) cx cy
end ECDSAAdd.Entrant.TerminalGraphProducer




-- TERMINAL GRAPH COMPONENT TerminalActual
-- ONEFLAG COMPONENT ActualOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OwnTerminalGraphActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount
 def generic (L : ControlledPointLayout) (cx cy : Fp) : Program:=
  TerminalGraphProducer.generic L (OwnOneFlagExitQ7.arithExit L) cx cy
 def gen (L : ControlledPointLayout) (cx cy : Fp) : Program:=
  TerminalGraphProducer.gen L (OwnOneFlagExitQ7.arithExit L) cx cy
 theorem exit_support (L : ControlledPointLayout) (hw:L.Widths) :
  wires (OwnOneFlagExitQ7.arithExit L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ OwnOneFlagExitQ7.kernelS_support
 theorem exit_counts_eq (L : ControlledPointLayout) :
  toffoliCount (OwnOneFlagExitQ7.arithExit L)=toffoliCount (OwnExitFuseQ6.arithExit L) ∧
  measurementCount (OwnOneFlagExitQ7.arithExit L)=measurementCount (OwnExitFuseQ6.arithExit L) := by
  have a:=OwnOneFlagExitQ7.arithExit_counts L
  have b:=OwnExitFuseQ5.arithExit_counts L
  have c:=Q6ResourceAdapters.exit_counts_eq L
  constructor <;> omega
 theorem counts_diff (L : ControlledPointLayout) (hw:L.Widths) (cx cy : Fp) :
  toffoliCount (gen L cx cy)+254=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
  measurementCount (gen L cx cy)+255=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  TerminalGraphProducer.gen_counts_diff L hw _ cx cy
 theorem sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy : Fp) :
  wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  TerminalGraphProducer.gen_sites L hw hn _ (exit_support L hw) cx cy
 theorem physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy : Fp) :
  GatePhysical (gen L cx cy) :=
  TerminalGraphProducer.gen_physical L hw hn _ (OwnOneFlagExitQ7.arithExit_physical L hw hn) cx cy
 theorem slots (L : ControlledPointLayout) (hw:L.Widths) (cx cy : Fp) :
  gateSlots (gen L cx cy)≤49224000 :=
  TerminalGraphProducer.gen_slots L hw _ (OwnOneFlagExitQ7.arithExit_slots_le L) cx cy
 theorem ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
  {cx cy : Fp} (hc:curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
  TerminalGraphProducer.gen_ok L hw hn _ (OwnOneFlagExitQ7.arithExit_correct L hw hn)
   logicalND hlo logicalAway logicalReplay hc
 theorem qubits (C : Point) (cx cy : Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1592 :=
  TerminalGraphProducer.gen_qubits _ (exit_support layout layout_widths)
   (OneFlagExitOmissions.exit_avoids layout layout_widths layout_nodup) C cx cy
end ECDSAAdd.Entrant.OwnTerminalGraphActual
end FrontierTerminalGraph

section FrontierJointEntry

section
-- Verified component FrontierEntrySignMath

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 100000
namespace ECDSAAdd.Entrant.DiagonalParity5
open Arithmetic BalancedCircuit BalancedField

theorem magnitude_sign (Y : Int) :
    (magnitude Y).toNat+(negative Y).toNat=Y.natAbs := by
  have cast := Int.natCast_natAbs Y
  by_cases neg : Y<0
  · have mag : magnitude Y= -Y-1 := by simp [magnitude,negative,neg]
    have nonneg := Int.toNat_of_nonneg (show 0≤ -Y-1 by omega)
    rw [abs_of_neg neg] at cast
    rw [mag]
    simp only [negative,neg,decide_true,Bool.toNat_true]
    omega
  · have mag : magnitude Y=Y := by simp [magnitude,negative,neg]
    have nonneg := Int.toNat_of_nonneg (show 0≤Y by omega)
    rw [abs_of_nonneg (by omega)] at cast
    rw [mag]
    simp only [negative,neg,decide_false,Bool.toNat_false,Nat.add_zero]
    omega

end ECDSAAdd.Entrant.DiagonalParity5

namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField

theorem target_nodup (L : Layout) (hn : L.wires.Nodup) : L.r.Nodup := by
  exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp (allND L hn)).2.1).1).1

theorem eraseAnd (a b t : Wire) (ha : a≠t) (hb : b≠t)
    (s : State) (m : List Bool) (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  cases hr : m.head?.getD false <;>
    simp [run,measureAndCorrect,correct,writeBit,ha,hb,ht,hr,Bool.xor_assoc]

end ECDSAAdd.Entrant.EntryHalf5

end

section
-- Verified component FrontierEntryAffine

set_option linter.unusedSimpArgs false

/-! Affine source bits are read through local Clifford views. The views
return before the carry recursion uses another source bit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5.Affine
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run

def parity : List Wire → BasisState → Bool
  | [],_ => false
  | q::qs,s => s q ^^ parity qs s

def fan (qs : List Wire) (a : Wire) : Program := qs.map (fun q => Instr.CX q a)

theorem parity_congr (qs : List Wire) (s t : BasisState)
    (h : ∀q∈qs,s q=t q) : parity qs s=parity qs t := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [parity,h q (by simp),ih (fun q hq => h q (by simp [hq]))]

theorem fan_counts (qs : List Wire) (a : Wire) :
    toffoliCount (fan qs a)=0 ∧ measurementCount (fan qs a)=0 := by
  induction qs with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs ih => simpa only [fan,List.map_cons,toffoliCount,measurementCount] using ih

theorem fan_proper (qs : List Wire) (a : Wire) (ha : a∉qs) : ProperProgram (fan qs a) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun e => ha (e ▸ hq)

theorem fan_correct (qs : List Wire) (a : Wire) (ha : a∉qs) (s : State) (m : List Bool) :
    run (fan qs a) m s=⟨s.phase,writeBit s.basis a (s.basis a ^^ parity qs s.basis)⟩ := by
  induction qs generalizing s with
  | nil => simp [fan,run,parity,writeBit]
  | cons q qs ih =>
    have qa : q≠a := fun e => ha (by simp [e])
    have tail : a∉qs := fun h => ha (by simp [h])
    let t : State := ⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis q)⟩
    have same : parity qs t.basis=parity qs s.basis := by
      apply parity_congr
      intro b hb
      simp [t,writeBit,show b≠a from fun e => tail (e ▸ hb)]
    simp only [fan,List.map_cons,run]
    change run (fan qs a) m t=_
    rw [ih tail,same]
    apply State.extensionality
    · rfl
    · funext b
      by_cases ba : b=a
      · subst b
        simp [t,writeBit,parity,Bool.xor_assoc]
      · simp [t,writeBit,ba]

structure Bit where
  wire : Wire
  terms : List Wire

def Bit.wires (b : Bit) : List Wire := b.wire::b.terms
def Bit.value (b : Bit) (s : BasisState) : Bool := s b.wire ^^ parity b.terms s
def Bit.Valid (b : Bit) : Prop := b.wire∉b.terms

def value : List Bit → BasisState → Nat
  | [],_ => 0
  | b::bs,s => (b.value s).toNat+2*value bs s

def sites (bs : List Bit) : List Wire := bs.flatMap Bit.wires

def view (b : Bit) : Program := fan b.terms b.wire

def majority (b : Bit) (y cin co : Wire) : Program :=
  view b++Arithmetic.majority b.wire y cin co++(view b).reverse

def erase (b : Bit) (y cin co : Wire) : Program :=
  view b++eraseCarry b.wire y cin co++(view b).reverse

def sum (b : Bit) (y cin : Wire) : Program := fan b.wires y++[.CX cin y]

def add : List Bit → List Wire → List Wire → Wire → Program
  | b::b'::bs,y::y'::ys,c::cs,cin => majority b y cin c++add (b'::bs) (y'::ys) cs c++erase b y cin c++sum b y cin
  | [b],[y],_,cin => sum b y cin
  | _,_,_,_ => []

/-- A local view can be undone after a disjoint target update, including
an independently measured update. -/
theorem unview_write (b : Bit) (hb : b.Valid) (q : Wire)
    (hq : q∉wires (view b)) (s : State) (v : Bool) (m : List Bool) :
    run (view b).reverse m ⟨(run (view b) [] s).phase,writeBit (run (view b) [] s).basis q v⟩=
      ⟨s.phase,writeBit s.basis q v⟩ := by
  let t : State := ⟨(run (view b) [] s).phase,writeBit (run (view b) [] s).basis q v⟩
  have p : ProperProgram (view b) := fan_proper _ _ hb
  have e : BalancedCleanup.Except q t (run (view b) [] s) := by
    refine ⟨rfl,?_⟩
    intro a ha
    simp [t,writeBit,ha]
  have h := BalancedCleanup.inverse_except (view b) p q hq s t [] m e
  apply State.extensionality
  · exact h.1
  · funext a
    by_cases aq : a=q
    · subst a
      have keep := run_preserves_outside (view b).reverse m t q (by rwa [wires_reverse])
      simpa only [t,writeBit,Function.update_self] using keep
    · simpa only [writeBit,Function.update_of_ne aq] using h.2 a aq

theorem fan_support (qs : List Wire) (a : Wire) : wires (fan qs a)⊆(a::qs).toFinset := by
  induction qs with
  | nil => simp [fan,wires]
  | cons q qs ih =>
    intro x hx
    simp only [fan,List.map_cons,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with (rfl|rfl)|hx
    · simp
    · simp
    · have h := ih hx
      simp only [List.mem_toFinset,List.mem_cons] at h ⊢
      tauto

theorem Bit.value_congr (b : Bit) (s t : BasisState)
    (h : ∀q∈b.wires,s q=t q) : b.value s=b.value t := by
  rw [Bit.value,Bit.value,h _ (by simp [Bit.wires]),parity_congr _ _ _ (fun q hq => h q (by simp [Bit.wires,hq]))]

theorem value_congr (bs : List Bit) (s t : BasisState)
    (h : ∀q∈sites bs,s q=t q) : value bs s=value bs t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [value,value,Bit.value_congr b s t (fun q hq => h q (by simp [sites,hq])),ih (fun q hq => h q (by simp [sites] at hq ⊢;tauto))]

theorem view_value (b : Bit) (hb : b.Valid) (s : State) :
    (run (view b) [] s).basis b.wire=b.value s.basis := by
  rw [view,fan_correct _ _ hb]
  simp [writeBit,Bit.value]

theorem view_other (b : Bit) (hb : b.Valid) (s : State) (q : Wire) (hq : q≠b.wire) :
    (run (view b) [] s).basis q=s.basis q := by
  rw [view,fan_correct _ _ hb]
  simp [writeBit,hq]

theorem view_away (b : Bit) (q : Wire) (hq : q∉b.wires) : q∉wires (view b) :=
  fun h => hq (List.mem_toFinset.mp (fan_support _ _ h))

theorem majority_correct (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool) :
    run (majority b y cin co) m s=⟨s.phase,writeBit s.basis co
      (s.basis co ^^ carryBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  have nd : [b.wire,y,cin,co].Nodup := List.nodup_cons.mpr ⟨ha _ (by simp [Bit.wires]),hn⟩
  have away (q : Wire) (hq : q∈[y,cin,co]) : q≠b.wire := fun e => ha _ (by simp [Bit.wires]) (e ▸ hq)
  have h := Arithmetic.majority_correct b.wire y cin co nd (run (view b) [] s) m
  rw [view_value b hb s,view_other b hb s y (away _ (by simp)),
    view_other b hb s cin (away _ (by simp)),view_other b hb s co (away _ (by simp))] at h
  have z : measurementCount (view b)=0 := (fan_counts _ _).2
  rw [majority,List.append_assoc,run_append,z,List.take_zero,List.drop_zero,run_append,run_take,h]
  exact unview_write b hb co (view_away b co (fun h => ha co h (by simp))) s _ _

theorem erase_correct (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool)
    (hc : s.basis co=carryBit (b.value s.basis) (s.basis y) (s.basis cin)) :
    run (erase b y cin co) m s=⟨s.phase,writeBit s.basis co false⟩ := by
  have a := ha b.wire (by simp [Bit.wires])
  have ay : b.wire≠y := fun e => a (by simp [e])
  have ai : b.wire≠cin := fun e => a (by simp [e])
  have ac : b.wire≠co := fun e => a (by simp [e])
  have yc : y≠co := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
  have ic : cin≠co := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [e])
  have h := eraseCarry_correct b.wire y cin co ac yc ic (run (view b) [] s)
    (by rw [view_value b hb s,view_other b hb s y ay.symm,view_other b hb s cin ai.symm,
      view_other b hb s co ac.symm];exact hc) m
  have z : measurementCount (view b)=0 := (fan_counts _ _).2
  rw [erase,List.append_assoc,run_append,z,List.take_zero,List.drop_zero,run_append,run_take,h]
  exact unview_write b hb co (view_away b co (fun h => ha co h (by simp))) s false _

theorem sum_correct (b : Bit) (y cin : Wire) (hc : cin≠y)
    (ha : ∀q∈b.wires,q≠y) (s : State) (m : List Bool) :
    run (sum b y cin) m s=⟨s.phase,writeBit s.basis y
      (sumBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
  have yb : y∉b.wires := fun h => ha y h rfl
  have first := fan_correct b.wires y yb s []
  have ci : (run (fan b.wires y) [] s).basis cin=s.basis cin := by
    rw [first];simp [writeBit,hc]
  rw [sum,run_append,(fan_counts _ _).2,List.take_zero,List.drop_zero,first]
  apply State.extensionality
  · simp only [run]
  · funext q
    by_cases qy : q=y
    · subst q
      simp [run,writeBit,hc,parity,Bit.wires,Bit.value,sumBit,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]
    · simp [run,writeBit,qy]

theorem head_mem (b : Bit) (bs : List Bit) (q : Wire) (hq : q∈b.wires) : q∈sites (b::bs) := by
  simp only [sites,List.flatMap_cons,List.mem_append]
  exact Or.inl hq

theorem tail_mem (b : Bit) (bs : List Bit) (q : Wire) (hq : q∈sites bs) : q∈sites (b::bs) := by
  simp only [sites,List.flatMap_cons,List.mem_append] at hq ⊢
  exact Or.inr hq

theorem bit_counts (b : Bit) (y cin co : Wire) :
    toffoliCount (majority b y cin co)=1 ∧ measurementCount (majority b y cin co)=0 ∧
    toffoliCount (erase b y cin co)=0 ∧ measurementCount (erase b y cin co)=1 ∧
    toffoliCount (sum b y cin)=0 ∧ measurementCount (sum b y cin)=0 := by
  have v := fan_counts b.terms b.wire
  have u := fan_counts b.wires y
  simp only [majority,erase,sum,view,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,v.1,v.2,u.1,u.2,Arithmetic.majority,eraseCarry,toffoliCount,measurementCount]
  decide

theorem add_correct (bits : List Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    (run (add bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (add bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (add bits ys carry cin) m s).basis=
      (value bits s.basis+regValue ys s.basis+(s.basis cin).toNat)%2^ys.length := by
  induction ys generalizing bits carry cin s m with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      have cnt := List.nodup_iff_count.mp hn
      have hcy : cin≠y := by
        intro bad; have h := cnt y; subst cin
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have bitAway (q : Wire) (hq : q∈b.wires) : q∉cin::((y::ys)++carry) :=
        hs q (head_mem b bits q hq)
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        have ha : ∀q∈b.wires,q≠y := by
          intro q hq bad
          exact bitAway q hq (by simp [bad])
        rw [add,sum_correct b y cin hcy ha]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
          simp [writeBit,hq]
        · simp only [regValue,List.foldr_cons,List.foldr_nil,writeBit,
            Function.update_self,List.length_cons,List.length_nil,value]
          cases b.value s.basis <;> cases s.basis y <;> cases s.basis cin <;>
            simp [sumBit,Bool.toNat]
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have hyc : y≠c := by
              intro bad; have h := cnt c; subst y
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcc : cin≠c := by
              intro bad; have h := cnt c; subst cin
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have hcytail : c∉y'::ys := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hyytail : y∉y'::ys := by
              intro bad; have h := cnt y
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hcintail : cin∉y'::ys := by
              intro bad; have h := cnt cin
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
              omega
            have hccs : c∉cs := by
              intro bad; have h := cnt c
              have pos := List.count_pos_iff.mpr bad
              simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
              omega
            have h3 : [y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have hbaway : ∀q∈b.wires,q∉[y,cin,c] := by
              intro q hq bad
              exact bitAway q hq (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have nd' : (c::((y'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q; have h := cnt q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have src' : ∀q∈sites (b'::bits),q∉c::((y'::ys)++cs) := by
              intro q hq bad
              exact hs q (tail_mem b (b'::bits) q hq)
                (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
            have sourceAwayC (q : Wire) (hq : q∈sites (b::b'::bits)) : q≠c := by
              intro bad
              exact hs q hq (by simp [bad])
            let A := b.value s.basis
            let B := s.basis y
            let C := s.basis cin
            let K := carryBit A B C
            let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
            have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by
              simp [s1,writeBit,hq]
            have hzero := hclean c (by simp)
            have first (record : List Bool) : run (majority b y cin c) record s=s1 := by
              rw [majority_correct b (hvalid b (by simp)) y cin c h3 hbaway]
              simp [s1,K,A,B,C,hzero]
            have clean' : ∀q∈cs,s1.basis q=false := by
              intro q hq
              rw [keep q (fun bad => hccs (bad ▸ hq))]
              exact hclean q (by simp [hq])
            obtain ⟨hp,he,hv⟩ := ih (b'::bits) cs c nd' src'
              (by simpa using hl) (by simpa using hc) s1 m clean'
              (fun b hb => hvalid b (by simp [hb]))
            let t := run (add (b'::bits) (y'::ys) cs c) m s1
            have ht : t.phase=s.phase := hp
            have ty : t.basis y=B := (he y hyytail).trans (keep y hyc)
            have ti : t.basis cin=C := (he cin hcintail).trans (keep cin hcc)
            have tk : t.basis c=K := by rw [he c hcytail]; simp [s1,writeBit]
            have ta : b.value t.basis=A := by
              apply Bit.value_congr b t.basis s.basis
              intro q hq
              have away := bitAway q hq
              have yt : q∉y'::ys := fun bad => away
                (List.mem_cons_of_mem cin (List.mem_append_left _ (List.mem_cons_of_mem y bad)))
              exact (he q yt).trans (keep q (sourceAwayC q (head_mem b (b'::bits) q hq)))
            have clear (record : List Bool) : run (erase b y cin c) record t=
                ⟨t.phase,writeBit t.basis c false⟩ := by
              apply erase_correct b (hvalid b (by simp)) y cin c h3 hbaway t record
              rw [ta,ty,ti,tk]
            let u : State := ⟨t.phase,writeBit t.basis c false⟩
            have uy : u.basis y=B := by simp [u,writeBit,hyc,ty]
            have ui : u.basis cin=C := by simp [u,writeBit,hcc,ti]
            have ua : b.value u.basis=A := by
              apply Eq.trans (Bit.value_congr b u.basis t.basis ?_) ta
              intro q hq
              simp [u,writeBit,sourceAwayC q (head_mem b (b'::bits) q hq)]
            have finish (record : List Bool) : run (sum b y cin) record u=
                ⟨t.phase,writeBit u.basis y (sumBit A B C)⟩ := by
              rw [sum_correct b y cin hcy (by
                intro q hq bad; exact bitAway q hq (by simp [bad])),ua,uy,ui]
            have mh := bit_counts b y cin c
            rw [add]
            simp only [List.append_assoc,run_append,run_take,mh.2.1,List.take_zero,List.drop_zero]
            rw [first]
            change (run (sum b y cin) _ (run (erase b y cin c) _ t)).phase=_ ∧ _
            rw [clear,finish]
            refine ⟨ht,?_,?_⟩
            · intro q hq
              have hq' : q≠y ∧ q∉y'::ys := by simpa using hq
              by_cases hqc : q=c
              · subst q; simp [u,writeBit,hyc.symm,hzero]
              · simp only [u,writeBit,Function.update_of_ne hq'.1,Function.update_of_ne hqc]
                exact (he q hq'.2).trans (keep q hqc)
            · have tailValue : regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=
                  regValue (y'::ys) t.basis := by
                apply regValue_congr
                intro q hq
                have hqy : q≠y := fun bad => hyytail (bad ▸ hq)
                have hqc : q≠c := fun bad => hcytail (bad ▸ hq)
                simp [u,writeBit,hqy,hqc]
              have sourceValue : value (b'::bits) s1.basis=value (b'::bits) s.basis := by
                apply value_congr
                intro q hq
                exact keep q (sourceAwayC q (tail_mem b (b'::bits) q hq))
              have yValue : regValue (y'::ys) s1.basis=regValue (y'::ys) s.basis :=
                regValue_congr _ _ _ (fun q hq => keep q (fun bad => hcytail (bad ▸ hq)))
              have kc : s1.basis c=K := by simp [s1,writeBit]
              change (if (writeBit u.basis y (sumBit A B C)) y then 1 else 0)+
                  2*regValue (y'::ys) (writeBit u.basis y (sumBit A B C))=_
              rw [show (writeBit u.basis y (sumBit A B C)) y=sumBit A B C by simp [writeBit],
                tailValue,hv,sourceValue,yValue,kc]
              have num := sum_value_step A B C (value (b'::bits) s.basis)
                (regValue (y'::ys) s.basis) (y'::ys).length
              simpa only [regValue,List.foldr_cons,value,List.length_cons,
                Bool.toNat,Bool.cond_eq_ite,A,B,C,K] using num

theorem add_counts (bits : List Bit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length) :
    toffoliCount (add bits ys carry cin)=ys.length-1 ∧
    measurementCount (add bits ys carry cin)=ys.length-1 := by
  induction ys generalizing bits carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bits =>
      cases ys with
      | nil =>
        have hb : bits=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst hb
        simpa [add] using
          And.intro (bit_counts b y cin cin).2.2.2.2.1
            (bit_counts b y cin cin).2.2.2.2.2
      | cons y' ys =>
        cases bits with
        | nil => simp at hl
        | cons b' bits =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have h := ih (b'::bits) cs c (by simpa using hl) (by simpa using hc)
            have head := bit_counts b y cin c
            rw [add]
            constructor
            · simp only [toffoliCount_append,head.1,head.2.2.1,head.2.2.2.2.1]
              rw [h.1]
              simp [Nat.add_comm]
            · simp only [measurementCount_append,head.2.1,head.2.2.2.1,head.2.2.2.2.2]
              rw [h.2]
              simp

end ECDSAAdd.Entrant.EntryRetained5.Affine

end

section
-- Verified component FrontierEntryHalfMath

set_option linter.unusedSimpArgs false

/-! Unary entry half arithmetic. The caller starts with a centered target
and a zero source; these lemmas do not replace an unequal-input cell. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField Secp256k1

def correction (H U : Bool) : Int :=
  if H then (if U then -q-1 else q+1) else (if U then q else -q)

def sourceBit (i : Nat) (P H U : Bool) : Bool :=
  let a := P && H
  let d := P && U
  let e := a && U
  if i=0 then P ^^ a else if i=1 ∨ i=2 then d ^^ e else
    if i=3 then P ^^ d ^^ e else
      if i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then P ^^ d ^^ a else d ^^ a

def virtualSource (P H U : Bool) : Nat :=
  (List.range 256).foldr (fun i acc => (sourceBit i P H U).toNat+2*acc) 0

theorem virtualSource_value (P H U : Bool) :
    virtualSource P H U=encodeWord 256 (if P then correction H U else 0) := by
  cases P <;> cases H <;> cases U <;> decide

theorem unary_half_formula (U : Bool) (Y : Int) (hy : Centered Y) :
    halfResult (signedY U Y)=
      (if U then -(Y/2) else Y/2)+(if originalParity Y then correction (negative Y) U else 0) := by
  have hT := signedY_bounds U Y hy
  have hp := constants
  have hR := (halfResult_spec (signedY U Y) (by unfold Centered at hT; omega)).2
  have negParity : (-Y)%2=Y%2 := by omega
  by_cases he : Y%2=0
  · have ie : signedY U Y%2=0 := by cases U <;> simp [signedY,negParity,he]
    rw [evenLift,if_pos ie] at hR
    cases U <;> simp [signedY,originalParity,he] at hR ⊢ <;> omega
  · have ie : signedY U Y%2≠0 := by cases U <;> simp [signedY,negParity,he]
    rw [evenLift,if_neg ie] at hR
    cases U <;> by_cases hn : Y<0
    all_goals
      simp only [signedY,Bool.false_eq_true,if_false,if_true] at hR ⊢
      simp [originalParity,negative,correction,he,hn]
      split_ifs at hR <;> omega


def threshold : Nat := q.toNat/2
def literalValue : Nat := 2^255-1-threshold

theorem threshold_relation : q=2*(threshold : Int)+1 := by norm_num [threshold,q,p]

theorem threshold_bound : threshold<2^255-1 := by decide

theorem literal_bound : literalValue<2^255 := by unfold literalValue; have b := threshold_bound; omega

theorem carry_predicate (R : Int) :
    decide (2^255≤(magnitude R).toNat+literalValue+(negative R).toNat)=decide (threshold<R.natAbs) := by
  have ms := DiagonalParity5.magnitude_sign R
  have tb := threshold_bound
  have equal : (2^255≤(magnitude R).toNat+literalValue+(negative R).toNat) ↔ threshold<R.natAbs := by
    unfold literalValue
    omega
  simp only [equal]

theorem half_parity (Y : Int) (hy : Centered Y) :
    originalParity Y=decide (threshold<(halfResult Y).natAbs) := by
  have z : Centered (0:Int) := by have := constants; unfold Centered; omega
  have h := halfResult_parity_interval false Y 0 hy z
  have t := threshold_relation
  have a := Int.natCast_natAbs (halfResult Y)
  simp only [rawSum,signedY,Bool.false_eq_true,if_false,add_zero,sub_zero,mul_zero] at h
  rw [abs_mul] at h
  norm_num only [Int.reduceAbs] at h
  apply decide_eq_decide.mpr
  change (Y%2≠0) ↔ threshold<(halfResult Y).natAbs
  omega

end ECDSAAdd.Entrant.EntryHalf5

end

section
-- Verified component FrontierEntryCarry

set_option linter.unusedSimpArgs false

/-! A literal carry prefix with a controlled read and independent measured
carry cleanup. No literal register is allocated. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 150000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

def value : List Bool→Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def literal : Nat→Nat→List Bool
  | 0,_ => []
  | n+1,k => decide (k%2=1)::literal n (k/2)

def bit (b : Bool) : MappedBit := {wire:=none,flip:=b}

def chain : List Bool→List Wire→List Wire→Wire→Wire→Wire→Program
  | b::bs,x::xs,c::cs,cin,ctl,target =>
      mappedMajority (bit b) x cin c++chain bs xs cs c ctl target++mappedEraseCarry (bit b) x cin c
  | [],[],[],cin,ctl,target => [.CCX ctl cin target]
  | _,_,_,_,_,_ => []

theorem literal_length (n k : Nat) : (literal n k).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [literal,ih]

theorem literal_value (n k : Nat) (hk : k<2^n) : value (literal n k)=k := by
  induction n generalizing k with
  | zero =>
    have h : k=0 := by simpa using hk
    simp [literal,value,h]
  | succ n ih =>
    have hd : k/2<2^n := by rw [pow_succ] at hk; omega
    have sp := Nat.mod_add_div k 2
    have sm := Nat.mod_lt k (by decide : 0<2)
    rw [literal,value,ih _ hd]
    by_cases odd : k%2=1 <;> simp [odd] <;> omega

theorem counts (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    toffoliCount (chain bs xs cs cin ctl target)=bs.length+1 ∧
    measurementCount (chain bs xs cs cin ctl target)=bs.length := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,toffoliCount,measurementCount]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have rest := ih xs cs c (by simpa using hx) (by simpa using hc)
        have one := mappedBit_counts (bit b) x cin c
        simp only [chain,toffoliCount_append,measurementCount_append,one.1,one.2.1,
          one.2.2.1,one.2.2.2.1,rest.1,rest.2,List.length_cons]
        omega

private theorem joint_3_threshold (b a c : Bool) (K X n : Nat) :
    (2^(n+1)≤a.toNat+2*X+(b.toNat+2*K)+c.toNat) ↔
      (2^n≤X+K+(carryBit b a c).toNat) := by
  rw [pow_succ]
  cases b <;> cases a <;> cases c <;> simp [carryBit] <;> omega

private theorem joint_3_reg_cons (x : Wire) (xs : List Wire) (s : BasisState) :
    regValue (x::xs) s=(s x).toNat+2*regValue xs s := by
  cases h : s x <;> simp [regValue,h]

theorem correct (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hn : (ctl::target::cin::(xs++cs)).Nodup)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length)
    (s : State) (m : List Bool) (clean : ∀q∈cs,s.basis q=false) :
    (run (chain bs xs cs cin ctl target) m s).phase=s.phase ∧
    (∀q,q≠target → (run (chain bs xs cs cin ctl target) m s).basis q=s.basis q) ∧
    (run (chain bs xs cs cin ctl target) m s).basis target=
      (s.basis target ^^ (s.basis ctl && decide (2^bs.length≤regValue xs s.basis+value bs+(s.basis cin).toNat))) := by
  induction bs generalizing xs cs cin s m with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst xs cs
    have ot : ctl≠target := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have ct : cin≠target := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
    simp only [chain,run]
    refine ⟨trivial,?_,?_⟩
    · intro q hq; simp [writeBit,hq]
    · cases hi : s.basis cin <;> simp [writeBit,value,regValue,hi]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have cnt := List.nodup_iff_count.mp hn
        have loc : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have restND : (ctl::target::c::(xs++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have tc : target≠c := by
          intro bad; have h := cnt c; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have tx : target≠x := by
          intro bad; have h := cnt x; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have ti : target≠cin := by
          intro bad; have h := cnt cin; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have oc : ctl≠c := by
          intro bad; have h := cnt c; subst ctl
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have cxs : c∉xs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        have ccs : c∉cs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        have xc : x≠c := fun h => (List.nodup_cons.mp loc).1 (by simp [h])
        have ic : cin≠c := fun h => (List.nodup_cons.mp (List.nodup_cons.mp loc).2).1 (by simp [h])
        let C := carryBit b (s.basis x) (s.basis cin)
        let u : State := ⟨s.phase,writeBit s.basis c C⟩
        have first (rec : List Bool) : run (mappedMajority (bit b) x cin c) rec s=u := by
          rw [mappedMajority_correct _ _ _ _ loc (by simp [bit])]
          simp [u,bit,MappedBit.value,clean c (by simp),C]
        have uf (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,hq]
        have clean' : ∀q∈cs,u.basis q=false := by
          intro q hq
          rw [uf q (fun h => ccs (h ▸ hq))]
          exact clean q (by simp [hq])
        have rest := ih xs cs c restND (by simpa using hx) (by simpa using hc) u m clean'
        let v := run (chain bs xs cs c ctl target) m u
        have vx : v.basis x=s.basis x := (rest.2.1 x tx.symm).trans (uf x xc)
        have vi : v.basis cin=s.basis cin := (rest.2.1 cin ti.symm).trans (uf cin ic)
        have vc : v.basis c=C := by rw [rest.2.1 c tc.symm]; simp [u,writeBit]
        have erase (rec : List Bool) : run (mappedEraseCarry (bit b) x cin c) rec v=
            ⟨v.phase,writeBit v.basis c false⟩ := by
          apply mappedEraseCarry_correct _ _ _ _ loc (by simp [bit])
          simp [bit,MappedBit.value,vx,vi,vc,C]
        have zeroM : measurementCount (mappedMajority (bit b) x cin c)=0 := (mappedBit_counts _ _ _ _).2.1
        simp only [chain,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
        rw [first,erase]
        refine ⟨rest.1,?_,?_⟩
        · intro q hq
          by_cases qc : q=c
          · subst q; simp [writeBit,clean c (by simp)]
          · simp only [writeBit,Function.update_of_ne qc]
            exact (rest.2.1 q hq).trans (uf q qc)
        · simp only [writeBit,Function.update_of_ne tc]
          rw [rest.2.2]
          have word : regValue xs u.basis=regValue xs s.basis :=
            regValue_congr _ _ _ (fun q hq => uf q (fun h => cxs (h ▸ hq)))
          rw [uf target tc,uf ctl oc,word]
          have uc : u.basis c=C := by simp [u,writeBit]
          rw [uc]
          have hthr := joint_3_threshold b (s.basis x) (s.basis cin) (value bs) (regValue xs s.basis) bs.length
          simp only [C,List.length_cons,value,joint_3_reg_cons,hthr]

end ECDSAAdd.Entrant.DiagonalCarry5

end

section
-- Verified component FrontierEntryCarryResources

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

theorem support (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    wires (chain bs xs cs cin ctl target)⊆(ctl::target::cin::(xs++cs)).toFinset := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,wires,Instr.wires,Finset.subset_iff]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have rest := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell := mappedBit_wires (bit b) x cin c
        have head : wires (mappedMajority (bit b) x cin c)⊆[x,cin,c].toFinset := by
          simpa [bit] using cell.1
        have tail : wires (mappedEraseCarry (bit b) x cin c)⊆[x,cin,c].toFinset := by
          simpa [bit] using cell.2.1
        intro q hq
        simp only [chain,wires_append,Finset.mem_union] at hq
        rcases hq with (h|h)|h
        · have hq := head h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto
        · have hq := rest h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto
        · have hq := tail h
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
          tauto

theorem physical (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hn : (ctl::target::cin::(xs++cs)).Nodup)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    GatePhysical (chain bs xs cs cin ctl target) := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst xs cs
    have ot : ctl≠target := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have ct : cin≠target := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
    simpa [chain,GatePhysical,PhysicalInstr,ProperGate] using And.intro ot ct
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nr : (ctl::target::c::(xs++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have r := ih xs cs c nr (by simpa using hx) (by simpa using hc)
        simp only [chain,gatePhysical_append]
        exact ⟨⟨mappedMajority_physical (bit b) x cin c nd (by simp [bit]),r⟩,
          mappedEraseCarry_physical (bit b) x cin c⟩

theorem slots_le (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    gateSlots (chain bs xs cs cin ctl target)≤7*bs.length+1 := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,gateSlots,instructionSlots]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have r := ih xs cs c (by simpa using hx) (by simpa using hc)
        have cell : gateSlots (mappedMajority (bit b) x cin c)+gateSlots (mappedEraseCarry (bit b) x cin c)≤7 := by
          cases b <;> norm_num [bit,mappedMajority,mappedEraseCarry,gateSlots,instructionSlots]
        simp only [chain,gateSlots_append,List.length_cons]
        omega

end ECDSAAdd.Entrant.DiagonalCarry5

end

section
-- Verified component FrontierEntryParity

set_option linter.unusedSimpArgs false
/-! Unary-half parity recovery from the target magnitude. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run DiagonalCarry5.chain

def parityBits : List Bool := DiagonalCarry5.literal 255 literalValue
def prepareMagnitude (L : Layout) : Program := BalancedCleanup.prepareSign L.toLayout
def parityCarry (L : Layout) (ctl : Wire) : Program :=
  DiagonalCarry5.chain parityBits L.low (L.carry.take 255) L.lower ctl L.parity
def positiveParity (L : Layout) (ctl : Wire) : Program :=
  prepareMagnitude L++(parityCarry L ctl++(prepareMagnitude L).reverse)
def recoverParity (L : Layout) (J : Wire) : Program :=
  [.X J]++positiveParity L J++[.X J]

theorem prepare_counts (L : Layout) :
    toffoliCount (prepareMagnitude L)=0 ∧ measurementCount (prepareMagnitude L)=0 := by
  have h := signComplement_counts L.lower L.r
  simp only [prepareMagnitude,BalancedCleanup.prepareSign,toffoliCount_append,measurementCount_append,
    h.1,h.2,toffoliCount,measurementCount]
  exact ⟨trivial,trivial⟩

theorem parity_counts (L : Layout) (hw : L.Widths) (ctl : Wire) :
    toffoliCount (positiveParity L ctl)=256 ∧ measurementCount (positiveParity L ctl)=255 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have h := DiagonalCarry5.counts parityBits L.low (L.carry.take 255) L.lower ctl L.parity
    (by simp [parityBits,DiagonalCarry5.literal_length,w.1])
    (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have hk : toffoliCount (parityCarry L ctl)=256 ∧ measurementCount (parityCarry L ctl)=255 := by
    simpa only [parityCarry,parityBits,DiagonalCarry5.literal_length] using h
  constructor
  · rw [positiveParity,toffoliCount_append,toffoliCount_append,toffoliCount_reverse,
      (prepare_counts L).1,hk.1]
  · rw [positiveParity,measurementCount_append,measurementCount_append,measurementCount_reverse,
      (prepare_counts L).2,hk.2]

theorem carry_nodup (L : Layout) (hn : L.wires.Nodup) (ctl : Wire) (hctl : ctl∉L.wires) :
    (ctl::L.parity::L.lower::(L.low++L.carry.take 255)).Nodup := by
  have nd := List.nodup_cons.mpr ⟨hctl,hn⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  have t := (List.take_sublist 255 L.carry).count_le q
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.low,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem prepare_low_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    let t := run (prepareMagnitude L) m s
    regValue L.low t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) := by
  have nd := (List.nodup_append'.mp hn).2.1
  have h := BalancedCleanup.prepareSign_value L.toLayout hw nd R hr s m hR hz
  let t := run (prepareMagnitude L) m s
  change regValue L.r t.basis=(magnitude R).toNat ∧ t.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → t.basis q=s.basis q) at h
  have b := magnitude_bounds R hr
  have z := Int.toNat_of_nonneg b.1
  have c := constants
  have bound : (magnitude R).toNat<2^255 := by norm_num only [Nat.reducePow] at ⊢; omega
  have split : regValue L.r t.basis=regValue L.low t.basis+2^255*(t.basis L.rmsb).toNat := by
    rw [BalancedCleanup.Layout.r,regValue_append,(BalancedCleanup.widths L.toLayout hw).1]
    cases k : t.basis L.rmsb <;> simp [regValue,k]
  have low : regValue L.low t.basis=(magnitude R).toNat := by
    rw [h.1] at split
    cases k : t.basis L.rmsb <;> simp only [k,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at split <;> omega
  exact ⟨low,h.2.1,h.2.2⟩

theorem positiveParity_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (ctl : Wire) (hctl : ctl∉L.wires) (B : Bool) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hS : s.basis ctl=B) (hz : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (positiveParity L ctl) m s=
      ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ (B && decide (threshold<R.natAbs)))⟩ := by
  let c := run (prepareMagnitude L) [] s
  let z := run (parityCarry L ctl) m c
  let tail := m.drop 255
  have pv := prepare_low_value L hw hn R hr s [] hR hz
  change regValue L.low c.basis=(magnitude R).toNat ∧ c.basis L.lower=negative R ∧
    (∀q,q∉L.r → q≠L.lower → c.basis q=s.basis q) at pv
  have nd0 := (List.nodup_append'.mp hn).2.1
  have prep : ProperProgram (prepareMagnitude L) := BalancedCleanup.prepareSign_proper _ nd0
  have pa : L.parity∉wires (prepareMagnitude L) :=
    (BalancedCleanup.clifford_parity_away _ hw nd0).1
  have nd := carry_nodup L hn ctl hctl
  have ay (a : Wire) (ha : a∈L.carry) : a∉L.r := by
    intro bad
    have h := List.nodup_iff_count.mp hn a
    have ca := List.count_pos_iff.mpr ha
    have cb := List.count_pos_iff.mpr bad
    simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h cb
    omega
  have al (a : Wire) (ha : a∈L.carry) : a≠L.lower := by
    intro eq
    exact flagAway L hn L.lower (by simp) (by simp [←eq,ha])
  have clean : ∀a∈L.carry.take 255,c.basis a=false := by
    intro a ha
    exact (pv.2.2 a (ay a (List.mem_of_mem_take ha)) (al a (List.mem_of_mem_take ha))).trans
      (hc a (List.mem_of_mem_take ha))
  have sp : c.basis L.parity=s.basis L.parity := run_preserves_outside _ [] s _ pa
  have sy : ctl∉L.r := by
    intro bad
    have zero := List.count_eq_zero.mpr hctl
    have pos := List.count_pos_iff.mpr bad
    simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at zero pos
    omega
  have sl : ctl≠L.lower := fun eq => hctl (by simp [eq,Layout.wires,BalancedCleanup.Layout.wires])
  have ss : c.basis ctl=B := (pv.2.2 ctl sy sl).trans hS
  have one := DiagonalCarry5.correct parityBits L.low (L.carry.take 255) L.lower ctl L.parity nd
    (by simp [parityBits,DiagonalCarry5.literal_length,(BalancedCleanup.widths L.toLayout hw).1])
    (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2]) c m clean
  have cp : z.basis L.parity=(s.basis L.parity ^^ (B && decide (threshold<R.natAbs))) := by
    change (run (DiagonalCarry5.chain parityBits L.low (L.carry.take 255) L.lower ctl L.parity) m c).basis L.parity=_
    rw [one.2.2,sp,ss]
    simp only [parityBits,DiagonalCarry5.literal_length,DiagonalCarry5.literal_value _ _ literal_bound,
      pv.1,pv.2.1,carry_predicate R]
  have ex : BalancedCleanup.Except L.parity z (run (prepareMagnitude L) [] s) := ⟨one.1,one.2.1⟩
  have restore := BalancedCleanup.inverse_except (prepareMagnitude L) prep L.parity pa s z [] tail ex
  have actual : run (positiveParity L ctl) m s=run (prepareMagnitude L).reverse tail z := by
    rw [positiveParity,run_append,(prepare_counts L).2,List.take_zero,List.drop_zero,run_append,run_take]
    have cp := DiagonalCarry5.counts parityBits L.low (L.carry.take 255) L.lower ctl L.parity
      (by simp [parityBits,DiagonalCarry5.literal_length,(BalancedCleanup.widths L.toLayout hw).1])
      (by simp [parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
    rw [show measurementCount (parityCarry L ctl)=255 from by
      simpa only [parityCarry,parityBits,DiagonalCarry5.literal_length] using cp.2]
  rw [actual]
  apply State.extensionality
  · exact restore.1
  · funext a
    by_cases ap : a=L.parity
    · subst a
      have keep := run_preserves_outside (prepareMagnitude L).reverse tail z L.parity (by rwa [wires_reverse])
      simpa only [writeBit,Function.update_self] using keep.trans cp
    · simpa only [writeBit,Function.update_of_ne ap] using restore.2 a ap

theorem recoverParity_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (recoverParity L J)=256 ∧ measurementCount (recoverParity L J)=255 := by
  have h := parity_counts L hw J
  simpa only [recoverParity,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    Nat.zero_add,Nat.add_zero] using h

/-- The control is negated only for the magnitude test. -/
theorem recoverParity_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (B : Bool) (R : Int) (hr : Centered R)
    (s : State) (m : List Bool) (hR : regValue L.r s.basis=encodeWord 256 R)
    (hS : s.basis J=B) (hz : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverParity L J) m s=
      ⟨s.phase,writeBit s.basis L.parity (s.basis L.parity ^^ ((!B) && decide (threshold<R.natAbs)))⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis J (!s.basis J)⟩
  have away (q : Wire) (hq : q∈L.wires) : q≠J := fun e => hJ (e ▸ hq)
  have same (q : Wire) (hq : q∈L.wires) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne (away q hq)]
  have sameR : regValue L.r u.basis=encodeWord 256 R :=
    (regValue_congr _ _ _ (fun q hq => same q (by
      simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
        BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
      tauto))).trans hR
  have hp : L.parity≠J := away _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])
  have a := positiveParity_xor L hw hn J hJ (!B) R hr u m sameR
    (by simp [u,writeBit,hS]) (by rw [same _ (by simp [Layout.wires,BalancedCleanup.Layout.wires])];exact hz)
    (fun q hq => (same q (by simp [Layout.wires,BalancedCleanup.Layout.wires,hq])).trans (hc q hq))
  have first : run [.X J] [] s=u := by simp [u,run,writeBit]
  rw [recoverParity,run_append,run_append,show measurementCount [.X J]=0 from rfl,
    List.take_zero,List.drop_zero,first,measurementCount_append,show measurementCount [.X J]=0 from rfl,Nat.zero_add,run_take,a]
  simp only [run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qj : q=J
    · subst q
      simp [u,writeBit,hp,Ne.symm hp]
    · by_cases qp : q=L.parity
      · subst q
        simp [u,writeBit,hp]
      · simp [u,writeBit,qj,qp]

end ECDSAAdd.Entrant.EntryHalf5

end

section
-- Verified component FrontierEntryErase

set_option linter.unusedSimpArgs false
/-! Phase-correct erasure for the retained-site entry scalars. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

theorem eraseXorAnd (p h d a : Wire) (hp : p≠a) (hh : h≠a) (hd : d≠a)
    (s : State) (m : List Bool)
    (ha : s.basis a=(s.basis p ^^ (s.basis p && s.basis h) ^^ s.basis d)) :
    run [.measureX a [] [.Z p,.CZ p h,.Z d]] m s=
      ⟨s.phase,writeBit s.basis a false⟩ := by
  cases hr : m.head?.getD false <;>
    simp [run,measureAndCorrect,correct,writeBit,hp,hh,hd,ha,hr,
      Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem fillZero (j p u : Wire) (s : State) (m : List Bool)
    (hu : s.basis u=false) :
    run [.CCX j p u] m s=⟨s.phase,writeBit s.basis u (s.basis j && s.basis p)⟩ := by
  simp [run,hu]

def eraseScalars (p a d e u j b h : Wire) : Program :=
  [.measureX e [] [.CZ a u],
   .measureX a [] [.Z p,.CZ p h,.Z d],
   .measureX d [] [.CZ p u],
   .measureX u [] [.CZ j b],
   .CCX j p u]

def erasedBasis (p a d e u j : Wire) (s : BasisState) : BasisState :=
  writeBit (writeBit (writeBit (writeBit s e false) a false) d false)
    u (s j && s p)

theorem erasedBasis_frame (p a d e u j : Wire) (s : BasisState) (q : Wire)
    (hq : q∉[a,d,e,u]) : erasedBasis p a d e u j s q=s q := by
  simp only [List.mem_cons,List.mem_singleton,not_or] at hq
  simp [erasedBasis,writeBit,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2]

theorem eraseScalars_counts (p a d e u j b h : Wire) :
    toffoliCount (eraseScalars p a d e u j b h)=1 ∧
      measurementCount (eraseScalars p a d e u j b h)=4 := by
  simp [eraseScalars,toffoliCount,measurementCount]

theorem eraseScalars_run (p a d e u j b h : Wire)
    (hn : [p,a,d,e,u,j,b,h].Nodup) (s : State) (m : List Bool)
    (he : s.basis e=(s.basis a && s.basis u))
    (ha : s.basis a=((s.basis p && s.basis h) ^^ s.basis p ^^ s.basis d))
    (hd : s.basis d=(s.basis p && s.basis u))
    (hu : s.basis u=(s.basis j && s.basis b)) :
    run (eraseScalars p a d e u j b h) m s=
      ⟨s.phase,erasedBasis p a d e u j s.basis⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨n01,n02,n03,n04,n05,n06,n07⟩,
    ⟨⟨n12,n13,n14,n15,n16,n17⟩,
    ⟨⟨n23,n24,n25,n26,n27⟩,
    ⟨⟨n34,n35,n36,n37⟩,
    ⟨⟨n45,n46,n47⟩,⟨⟨n56,n57⟩,n67⟩⟩⟩⟩⟩⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n40 := Ne.symm n04
  have n50 := Ne.symm n05
  have n60 := Ne.symm n06
  have n70 := Ne.symm n07
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n41 := Ne.symm n14
  have n51 := Ne.symm n15
  have n61 := Ne.symm n16
  have n71 := Ne.symm n17
  have n32 := Ne.symm n23
  have n42 := Ne.symm n24
  have n52 := Ne.symm n25
  have n62 := Ne.symm n26
  have n72 := Ne.symm n27
  have n43 := Ne.symm n34
  have n53 := Ne.symm n35
  have n63 := Ne.symm n36
  have n73 := Ne.symm n37
  have n54 := Ne.symm n45
  have n64 := Ne.symm n46
  have n74 := Ne.symm n47
  have n65 := Ne.symm n56
  have n75 := Ne.symm n57
  have n76 := Ne.symm n67
  have first := EntryHalf5.eraseAnd a u e n13 n43 s m he
  let s₁ : State := ⟨s.phase,writeBit s.basis e false⟩
  have second := eraseXorAnd p h d a n01 n71 n21 s₁ m.tail (by
    simpa [s₁,writeBit,n03,n73,n23,n13,Bool.xor_comm,Bool.xor_left_comm] using ha)
  let s₂ : State := ⟨s.phase,writeBit s₁.basis a false⟩
  have third := EntryHalf5.eraseAnd p u d n02 n42 s₂ m.tail.tail (by
    simpa [s₂,s₁,writeBit,n01,n03,n41,n43,n21,n23] using hd)
  let s₃ : State := ⟨s.phase,writeBit s₂.basis d false⟩
  have fourth := EntryHalf5.eraseAnd j b u n54 n64 s₃ m.tail.tail.tail (by
    simpa [s₃,s₂,s₁,writeBit,n52,n51,n53,n62,n61,n63,n42,n41,n43] using hu)
  let s₄ : State := ⟨s.phase,writeBit s₃.basis u false⟩
  have fill := fillZero j p u s₄ m.tail.tail.tail.tail (by simp [s₄,writeBit])
  change run [.measureX a [] [.Z p,.CZ p h,.Z d],
    .measureX d [] [.CZ p u],.measureX u [] [.CZ j b],.CCX j p u]
    m.tail (run [.measureX e [] [.CZ a u]] m s)=_
  rw [first]
  change run [.measureX d [] [.CZ p u],.measureX u [] [.CZ j b],.CCX j p u]
    m.tail.tail (run [.measureX a [] [.Z p,.CZ p h,.Z d]] m.tail s₁)=_
  rw [second]
  change run [.measureX u [] [.CZ j b],.CCX j p u]
    m.tail.tail.tail (run [.measureX d [] [.CZ p u]] m.tail.tail s₂)=_
  rw [third]
  change run [.CCX j p u] m.tail.tail.tail.tail
    (run [.measureX u [] [.CZ j b]] m.tail.tail.tail s₃)=_
  rw [fourth]
  change run [.CCX j p u] m.tail.tail.tail.tail s₄=_
  rw [fill]
  simp [s₄,s₃,s₂,s₁,erasedBasis,writeBit,n54,n52,n51,n53,n04,n02,n01,n03]

def eraseScalarsAt (L : Layout) (J B : Wire) : Program :=
  eraseScalars L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb

theorem erasePorts_nodup (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    [L.parity,L.lower,L.one,L.sign,L.ylow.getD 0 0,J,B,L.rmsb].Nodup := by
  have jnb : J≠B := by simpa using hJB
  have nd : (J::B::L.wires).Nodup :=
    List.nodup_cons.mpr ⟨by simp [hJ,jnb],List.nodup_cons.mpr ⟨hB,hn⟩⟩
  cases hy : L.ylow with
  | nil => have h := hw.2.1;simp [hy] at h
  | cons y ys =>
    apply List.nodup_iff_count.mpr
    intro q
    have c := List.nodup_iff_count.mp nd q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,hy,List.getD_cons_zero,
      List.count_append,List.count_cons,List.count_nil] at c ⊢
    omega

theorem eraseScalarsAt_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (s : State) (m : List Bool)
    (he : s.basis L.sign=(s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (ha : s.basis L.lower=((s.basis L.parity && s.basis L.rmsb) ^^
      s.basis L.parity ^^ s.basis L.one))
    (hd : s.basis L.one=(s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hu : s.basis (L.ylow.getD 0 0)=(s.basis J && s.basis B)) :
    run (eraseScalarsAt L J B) m s=⟨s.phase,
      erasedBasis L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J s.basis⟩ :=
  eraseScalars_run _ _ _ _ _ _ _ _ (erasePorts_nodup L hw hn J B hJ hB hJB)
    s m he ha hd hu

theorem signedY_parity (U : Bool) (Y : Int) :
    originalParity (signedY U Y)=originalParity Y := by
  cases U
  · rfl
  · change decide ((-Y)%2≠0)=decide (Y%2≠0)
    apply decide_eq_decide.mpr
    omega

/-- The old sign product needs no retained old-sign bit. -/
theorem oldSign_product (U : Bool) (Y : Int) (hy : Centered Y) :
    (originalParity Y && negative Y)=
      ((originalParity Y && negative (halfResult (signedY U Y))) ^^ originalParity Y ^^
        (originalParity Y && U)) := by
  have ht := signedY_bounds U Y hy
  have hc := constants
  have hs := halfResult_sign (signedY U Y) (by unfold Centered at ht;omega)
  change negative (halfResult (signedY U Y))=
    (negative (signedY U Y) ^^ originalParity (signedY U Y)) at hs
  rw [signedY_parity] at hs
  by_cases hp : originalParity Y=false
  · simp [hp]
  · have hp : originalParity Y=true := by cases h : originalParity Y <;> simp_all
    have yn : Y≠0 := by
      intro e
      subst Y
      simp [originalParity] at hp
    have ns : negative (signedY U Y)=(negative Y ^^ U) := by
      cases U
      · simp [signedY]
      · by_cases h : Y<0
        · have pos : ¬0<Y := by omega
          simp [signedY,negative,h,pos]
        · have pos : 0<Y := by omega
          simp [signedY,negative,h,pos]
    rw [ns,hp] at hs
    cases U <;> cases hn : negative Y <;> simp_all

def clearParity (L : Layout) (J : Wire) : Program :=
  [.CX (L.ylow.getD 0 0) L.parity]++EntryHalf5.recoverParity L J

theorem clearParity_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (clearParity L J)=256 ∧ measurementCount (clearParity L J)=255 := by
  simpa only [clearParity,toffoliCount_append,measurementCount_append,toffoliCount,
    measurementCount,Nat.zero_add] using EntryHalf5.recoverParity_counts L hw J

theorem clearParity_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (Jv Bv : Bool) (Y : Int) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity=originalParity Y)
    (hU : s.basis (L.ylow.getD 0 0)=(Jv && originalParity Y))
    (hS : s.basis J=Jv) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  let R := halfResult (signedY (Jv && Bv) Y)
  let u : State := ⟨s.phase,writeBit s.basis L.parity
    (s.basis L.parity ^^ s.basis (L.ylow.getD 0 0))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity :=
    fun e => pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd := List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro eq
    simp [eq,List.count_cons] at nd
    omega
  have jp : J≠L.parity := fun e => hJ (by
    simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have same (q : Wire) (hq : q≠L.parity) : u.basis q=s.basis q := by
    simp [u,writeBit,hq]
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr L.r u.basis s.basis (fun q hq =>
      same q (away q (by simp [hq])))) hR
  have bounds := signedY_bounds (Jv && Bv) Y hy
  have constants := BalancedField.constants
  have rb : Centered R :=
    (halfResult_spec (signedY (Jv && Bv) Y) (by unfold Centered at bounds;omega)).1
  have predicate : decide (EntryHalf5.threshold<R.natAbs)=originalParity Y := by
    rw [←EntryHalf5.half_parity (signedY (Jv && Bv) Y) bounds,signedY_parity]
  have core := EntryHalf5.recoverParity_xor L hw hn J hJ Jv R rb u m ur
    ((same J jp).trans hS) ((same L.lower lp).trans hl)
    (fun q hq => (same q (away q (by simp [hq]))).trans (hc q hq))
  have zero : (u.basis L.parity ^^ ((!Jv) && decide (EntryHalf5.threshold<R.natAbs)))=false := by
    rw [predicate]
    simp only [u,writeBit,Function.update_self,hP,hU]
    cases Jv <;> simp
  have first : run [.CX (L.ylow.getD 0 0) L.parity] [] s=u := rfl
  rw [clearParity,run_append,show measurementCount [.CX (L.ylow.getD 0 0) L.parity]=0 from rfl,
    List.take_zero,List.drop_zero,first,core,zero]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp [writeBit]
    · simp [u,writeBit,qp]

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryProgram

set_option linter.unusedSimpArgs false
/-! Source bit zero is the temporary product U. Its copy is delayed until
all four measured products have been erased. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

def lowY (L : Layout) : Wire := L.ylow.getD 0 0

def source (L : Layout) (i : Nat) : Affine.Bit :=
  if i=0 then ⟨L.parity,[L.lower]⟩ else if i=1 ∨ i=2 then ⟨L.one,[L.sign]⟩ else
    if i=3 then ⟨L.parity,[L.one,L.sign]⟩ else
      if i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then ⟨L.parity,[L.one,L.lower]⟩
      else ⟨L.one,[L.lower]⟩

def sources (L : Layout) : List Affine.Bit := (List.range 256).map (source L)

def prepare (L : Layout) (J B : Wire) : Program :=
  [.CCX J B (lowY L)]++copyRegister (some J) L.r.tail L.y.tail++
    [.CX L.r0 L.parity,.CCX L.parity L.rmsb L.lower,
      .CCX L.parity (lowY L) L.one,.CCX L.lower (lowY L) L.sign,.CX L.parity L.r0]++
    rotateRight L.r++[.CX (L.r.getD 254 0) L.rmsb]++signComplement (lowY L) L.r

def arithmetic (L : Layout) : Program := Affine.add (sources L) L.r (L.carry.take 255) (lowY L)

def prefixProgram (L : Layout) (J B : Wire) : Program := prepare L J B++arithmetic L

def program (L : Layout) (J B : Wire) : Program :=
  prefixProgram L J B++eraseScalarsAt L J B++clearParity L J

theorem sources_length (L : Layout) : (sources L).length=256 := by simp [sources]

theorem prepare_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (prepare L J B)=259 ∧ measurementCount (prepare L J B)=0 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have r : L.r.tail.length=255 := by simp [len.2.1]
  have y : L.y.tail.length=255 := by simp [len.2.2.1]
  have c := copyRegister_counts (some J) L.r.tail L.y.tail (r.trans y.symm)
  have rot := rotate_counts L.r
  have comp := signComplement_counts (lowY L) L.r
  simp only [prepare,toffoliCount_append,measurementCount_append,c.1,c.2,rot.1,rot.2.1,comp.1,comp.2,r]
  norm_num [toffoliCount,measurementCount]

theorem arithmetic_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (arithmetic L)=255 ∧ measurementCount (arithmetic L)=255 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_counts (sources L) L.r (L.carry.take 255) (lowY L)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  simpa only [arithmetic,len.2.1] using h

theorem prefix_counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (prefixProgram L J B)=514 ∧ measurementCount (prefixProgram L J B)=255 := by
  simp only [prefixProgram,toffoliCount_append,measurementCount_append,
    (prepare_counts L hw J B).1,(prepare_counts L hw J B).2,
    (arithmetic_counts L hw).1,(arithmetic_counts L hw).2]
  decide

theorem counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (program L J B)=771 ∧ measurementCount (program L J B)=514 := by
  have e := eraseScalars_counts L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J B L.rmsb
  simp only [program,eraseScalarsAt,toffoliCount_append,measurementCount_append,
    (prefix_counts L hw J B).1,(prefix_counts L hw J B).2,e.1,e.2,
    (clearParity_counts L hw J).1,(clearParity_counts L hw J).2]
  decide

theorem sources_value (L : Layout) (P H U : Bool) (s : BasisState)
    (hp : s L.parity=P) (ha : s L.lower=(P && H))
    (hd : s L.one=(P && U)) (he : s L.sign=((P && H) && U)) :
    Affine.value (sources L) s=EntryHalf5.virtualSource P H U := by
  have bit (i : Nat) : (source L i).value s=EntryHalf5.sourceBit i P H U := by
    simp only [source,EntryHalf5.sourceBit]
    split_ifs <;> simp [Affine.Bit.value,Affine.parity,hp,ha,hd,he,Bool.xor_assoc]
  have map (is : List Nat) : Affine.value (is.map (source L)) s=
      is.foldr (fun i acc => (EntryHalf5.sourceBit i P H U).toNat+2*acc) 0 := by
    induction is with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons,Affine.value,List.foldr_cons,bit,ih]
  exact map (List.range 256)

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryLayout

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

theorem y_cons (L : Layout) (hw : L.Widths) : L.y=lowY L::L.y.tail := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1;simp [hy] at h
  | cons a as => simp [BalancedCleanup.Layout.y,lowY,hy]

theorem r_cons (L : Layout) : L.r=L.r0::L.r.tail := rfl

theorem data_member (L : Layout) (q : Wire) (hq : q∈L.r++L.y++L.carry) : q∈L.wires := by
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
  tauto

theorem copyND (L : Layout) (hn : L.wires.Nodup) : (L.r.tail++L.y.tail).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (allND L hn) q
  have r := (List.tail_sublist L.r).count_le q
  have y := (List.tail_sublist L.y).count_le q
  simp only [List.count_append] at h ⊢
  omega

theorem arithmeticND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (lowY L::(L.r++L.carry.take 255)).Nodup := by
  have hy := y_cons L hw
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (allND L hn) q
  have c := (List.take_sublist 255 L.carry).count_le q
  rw [hy] at h
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem source_sites (L : Layout) (i : Nat) :
    (source L i).wires⊆[L.parity,L.lower,L.one,L.sign] := by
  intro q hq
  unfold source at hq
  split_ifs at hq <;> simp_all [Affine.Bit.wires] <;> tauto

theorem sources_sites (L : Layout) (q : Wire) (hq : q∈Affine.sites (sources L)) :
    q∈[L.parity,L.lower,L.one,L.sign] := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  exact source_sites L i hq

theorem sources_valid (L : Layout) (hn : L.wires.Nodup) :
    ∀b∈sources L,b.Valid := by
  have nd : [L.parity,L.lower,L.one,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or,List.nodup_nil,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03⟩,⟨n12,n13⟩,n23⟩
  have n10 := Ne.symm n01
  have n21 := Ne.symm n12
  intro b hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  unfold source
  split_ifs <;> simp_all [Affine.Bit.Valid]

theorem sources_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀q∈Affine.sites (sources L),q∉lowY L::(L.r++L.carry.take 255) := by
  intro q hq bad
  have member := sources_sites L q hq
  have f := flagAway L hn q (by simp only [List.mem_cons,List.mem_singleton] at member ⊢;tauto)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have h : q∈L.r++L.y++L.carry := by
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with rfl|hr|hc
    · simp [y0]
    · simp [hr]
    · simp [List.mem_of_mem_take hc]
  exact f h

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryMath

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField Secp256k1

theorem half_encoding (Y : Int) (hy : Centered Y) :
    encodeWord 256 Y=(originalParity Y).toNat+2*encodeWord 255 (Y/2) := by
  have h := constants
  have Yb : -((2^256:Nat):Int)≤Y ∧ Y<((2^256:Nat):Int) := by
    unfold Centered at hy
    norm_num only [Nat.reducePow] at h ⊢
    omega
  have Hb : -((2^255:Nat):Int)≤Y/2 ∧ Y/2<((2^255:Nat):Int) := by
    unfold Centered at hy
    norm_num only [Nat.reducePow] at h ⊢
    omega
  have a := BalancedFold.encode_shift 256 Y Yb
  have b := BalancedFold.encode_shift 255 (Y/2) Hb
  have p := originalParity_value Y
  have neg : Y/2<0 ↔ Y<0 := by omega
  simp only [neg] at b
  by_cases n : Y<0 <;> simp only [n,if_true,if_false] at a b
  all_goals
    cases pv : originalParity Y <;> simp only [pv,Bool.false_eq_true,if_true,if_false,
      Bool.toNat_false,Bool.toNat_true] at p ⊢ <;> norm_num only [Nat.reducePow] at a b <;> omega

theorem encode_add (n : Nat) (X Y : Int) :
    (encodeWord n X+encodeWord n Y)%2^n=encodeWord n (X+Y) := by
  have cast : (((encodeWord n X+encodeWord n Y)%2^n:Nat):Int)=
      (encodeWord n (X+Y):Int) := by
    push_cast
    simp only [encodeWord_cast,Nat.cast_pow,Nat.cast_ofNat]
    exact (Int.add_emod X Y (2^n)).symm
  exact_mod_cast cast

theorem add_complement (U : Bool) (K C : Int) :
    (encodeWord 256 C+(if U then 2^256-1-encodeWord 256 K else encodeWord 256 K)+U.toNat)%2^256=
      encodeWord 256 (signedY U K+C) := by
  cases U
  · simpa [signedY,Int.add_comm] using encode_add 256 C K
  · have kb := encodeWord_bound 256 K
    have c := encodeWord_cast 256 C
    have k := encodeWord_cast 256 K
    have out := encodeWord_cast 256 (-K+C)
    have casts : (((encodeWord 256 C+(2^256-1-encodeWord 256 K)+1)%2^256:Nat):Int)=
        (encodeWord 256 (-K+C):Int) := by
      rw [Int.natCast_emod,Int.natCast_add,Int.natCast_add,
        Int.natCast_sub (by omega),Int.natCast_sub (by norm_num)]
      norm_num only [Nat.reducePow,Int.natCast_pow,Int.natCast_one] at kb c k out ⊢
      omega
    simpa only [Bool.toNat_true,signedY,if_true] using (show
      (encodeWord 256 C+(2^256-1-encodeWord 256 K)+1)%2^256=encodeWord 256 (-K+C) by exact_mod_cast casts)

theorem folded_encoding (U : Bool) (Y : Int) (hy : Centered Y) :
    (EntryHalf5.virtualSource (originalParity Y) (negative Y) U+
      (if U then 2^256-1-encodeWord 256 (Y/2) else encodeWord 256 (Y/2))+U.toNat)%2^256=
      encodeWord 256 (halfResult (signedY U Y)) := by
  rw [EntryHalf5.virtualSource_value,add_complement,EntryHalf5.unary_half_formula U Y hy]
  cases U <;> simp [signedY]

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryPrefix

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run

def copyControl (L : Layout) (J B : Wire) : Program :=
  [.CCX J B (lowY L)]++copyRegister (some J) L.r.tail L.y.tail

def productsSeed (L : Layout) : Program :=
  [.CX L.r0 L.parity,.CCX L.parity L.rmsb L.lower,
    .CCX L.parity (lowY L) L.one,.CCX L.lower (lowY L) L.sign,.CX L.parity L.r0]

def rightShift (L : Layout) : Program :=
  rotateRight L.r++[.CX (L.r.getD 254 0) L.rmsb]

theorem prepare_shape (L : Layout) (J B : Wire) :
    prepare L J B=copyControl L J B++productsSeed L++rightShift L++signComplement (lowY L) L.r := by
  simp only [prepare,copyControl,productsSeed,rightShift,List.append_assoc]

structure PrefixResult (L : Layout) (J B : Wire) (Jv Bv : Bool) (Y : Int) (s t : State) : Prop where
  phase : t.phase=s.phase
  target : regValue L.r t.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y))
  source : regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then encodeWord 256 Y/2 else 0)
  parity : t.basis L.parity=originalParity Y
  a : t.basis L.lower=(originalParity Y && negative Y)
  d : t.basis L.one=(originalParity Y && (Jv && Bv))
  e : t.basis L.sign=((originalParity Y && negative Y) && (Jv && Bv))
  u : t.basis (lowY L)=(Jv && Bv)
  j : t.basis J=Jv
  b : t.basis B=Bv
  carry : ∀q∈L.carry,t.basis q=false
  outside : ∀q,q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign] → t.basis q=s.basis q

theorem rightShift_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=2*encodeWord 255 (Y/2)) :
    let t := run (rightShift L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (Y/2) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let t := run (rotateRight L.r) [] s
  have len := BalancedCleanup.widths L.toLayout hw
  have nd := EntryHalf5.target_nodup L hn
  have rot := rotateRight_spec L.r nd (2*encodeWord 255 (Y/2)) (by omega) s [] hR
  have frame := rotate_frame L.r s []
  have value : regValue L.r t.basis=encodeWord 255 (Y/2) := by
    have h : regValue L.r t.basis=2*encodeWord 255 (Y/2)/2 := rot.2
    omega
  have bound := encodeWord_bound 255 (Y/2)
  have top : t.basis L.rmsb=false := by
    have h := regValue_highBit L.low L.rmsb t.basis
    change t.basis L.rmsb=true ↔ 2^L.low.length≤regValue L.r t.basis at h
    rw [len.1,value] at h
    cases e : t.basis L.rmsb
    · rfl
    · have := h.mp e;omega
  have low : regValue L.low t.basis=encodeWord 255 (Y/2) := by
    rw [BalancedCleanup.Layout.r,regValue_append,len.1] at value
    simpa [regValue,top] using value
  have msbAway : L.rmsb∉L.low :=
    fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  have split : L.low=L.r.take 254++[L.r.getD 254 0] := by
    have idx : 254<L.r.length := by rw [len.2.1];decide
    have h := List.take_succ_eq_append_getElem idx
    have take : L.r.take 255=L.low := by
      change (L.low++[L.rmsb]).take 255=L.low
      rw [←len.1,List.take_left]
    rw [show 254+1=255 from rfl,take] at h
    simpa only [List.getD_eq_getElem _ _ idx] using h
  let out := run [.CX (L.r.getD 254 0) L.rmsb] [] t
  have off (q : Wire) (hq : q≠L.rmsb) : out.basis q=t.basis q := by simp [out,run,writeBit,hq]
  have newLow : regValue L.low out.basis=encodeWord 255 (Y/2) :=
    (regValue_congr _ _ _ (fun q hq => off q (fun e => msbAway (e ▸ hq)))).trans low
  have signApart : L.r.getD 254 0≠L.rmsb := by
    intro eq
    have member : L.r.getD 254 0∈L.low := by rw [split];simp
    exact msbAway (eq ▸ member)
  have signCopy : out.basis L.rmsb=out.basis (L.r.getD 254 0) := by
    have h : out.basis L.rmsb=t.basis (L.r.getD 254 0) := by simp [out,run,writeBit,top]
    exact h.trans (off _ signApart).symm
  have same := signed_extension (L.r.take 254) (L.r.getD 254 0) L.rmsb out.basis signCopy
  rw [←split] at same
  have signed : signedRegValue L.low out.basis=Y/2 := by
    unfold signedRegValue
    rw [len.1,newLow]
    apply decode_encodeWord 255 (by decide)
    have h := constants
    unfold Centered at hy
    norm_num only [Nat.reducePow,Nat.reduceSub] at h ⊢
    omega
  have result : regValue L.r out.basis=encodeWord 256 (Y/2) :=
    word_encoding L.r 256 len.2.1 out.basis (Y/2) (same.trans signed)
  have actual : run (rightShift L) m s=out := by
    rw [rightShift,run_append,(rotate_counts _).2.1,List.take_zero,List.drop_zero]
    simp only [out,t,run]
  rw [actual]
  refine ⟨?_,result,?_⟩
  · simpa only [out,run] using frame.1
  · intro q hq
    have qa : q≠L.rmsb := fun e => hq (by simp [e,BalancedCleanup.Layout.r])
    exact (off q qa).trans (frame.2.1 q hq)

theorem productsSeed_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P H U : Bool) (s : State) (m : List Bool)
    (hp : s.basis L.r0=P) (hh : s.basis L.rmsb=H) (hu : s.basis (lowY L)=U)
    (zp : s.basis L.parity=false) (za : s.basis L.lower=false)
    (zd : s.basis L.one=false) (ze : s.basis L.sign=false) :
    run (productsSeed L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.parity P)
        L.lower (P && H)) L.one (P && U)) L.sign ((P && H) && U)) L.r0 false⟩ := by
  have nd : [L.r0,L.rmsb,L.parity,L.lower,L.one,L.sign,lowY L].Nodup := by
    cases hys : L.ylow with
    | nil => have h := hw.2.1;simp [hys] at h
    | cons a as =>
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [Layout.wires,BalancedCleanup.Layout.wires,lowY,hys,List.getD_cons_zero,
        List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03,n04,n05,n06⟩,⟨⟨n12,n13,n14,n15,n16⟩,⟨⟨n23,n24,n25,n26⟩,⟨⟨n34,n35,n36⟩,⟨⟨n45,n46⟩,n56⟩⟩⟩⟩⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n40 := Ne.symm n04
  have n50 := Ne.symm n05
  have n60 := Ne.symm n06
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n41 := Ne.symm n14
  have n51 := Ne.symm n15
  have n61 := Ne.symm n16
  have n32 := Ne.symm n23
  have n42 := Ne.symm n24
  have n52 := Ne.symm n25
  have n62 := Ne.symm n26
  have n43 := Ne.symm n34
  have n53 := Ne.symm n35
  have n63 := Ne.symm n36
  have n54 := Ne.symm n45
  have n64 := Ne.symm n46
  have n65 := Ne.symm n56
  apply State.extensionality
  · simp only [productsSeed,run]
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qa : q=L.lower
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qd : q=L.one
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qe : q=L.sign
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    by_cases qr : q=L.r0
    · subst q;simp_all [productsSeed,run,writeBit,Function.update]
    simp_all [productsSeed,run,writeBit,Function.update]

theorem copyControl_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires)
    (Jv Bv : Bool) (V : Nat) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=V) (hY : regValue L.y s.basis=0)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let t := run (copyControl L J B) m s
    t.phase=s.phase ∧ regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then V/2 else 0) ∧
    t.basis (lowY L)=(Jv && Bv) ∧ (∀q,q∉L.y → t.basis q=s.basis q) := by
  let U := Jv && Bv
  have yHead := y_cons L hw
  have y0 : lowY L∈L.y := by rw [yHead];simp
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have ry := (List.nodup_append'.mp data).1
  have yn := (List.nodup_append'.mp ry).2.1
  have rdy := (List.nodup_append'.mp ry).2.2
  have yAway : lowY L∉L.y.tail := by rw [yHead] at yn;exact (List.nodup_cons.mp yn).1
  have rAway (q : Wire) (hq : q∈L.r) : q≠lowY L :=
    fun e => List.disjoint_left.mp rdy hq (e.symm ▸ y0)
  have notY (q : Wire) (hq : q∉L.wires) : q∉L.y :=
    fun bad => hq (data_member L q (by simp [bad]))
  have jY := notY J hJ
  have bY := notY B hB
  have jy : J≠lowY L := fun e => jY (e.symm ▸ y0)
  have by0 : B≠lowY L := fun e => bY (e.symm ▸ y0)
  have z := (regValue_zero _ _).mp hY (lowY L) y0
  let a : State := ⟨s.phase,writeBit s.basis (lowY L) U⟩
  have first : run [.CCX J B (lowY L)] [] s=a := by simp [a,run,z,U,hj,hb]
  have aOther (q : Wire) (hq : q≠lowY L) : a.basis q=s.basis q := by simp [a,writeBit,hq]
  have aJ : a.basis J=Jv := (aOther J jy).trans hj
  have sameR : regValue L.r.tail a.basis=V/2 := by
    have same : regValue L.r.tail a.basis=regValue L.r.tail s.basis :=
      regValue_congr _ _ _ (fun q hq => aOther q (rAway q (List.mem_of_mem_tail hq)))
    rw [same]
    rw [r_cons L] at hR
    change (if s.basis L.r0 then 1 else 0)+2*regValue L.r.tail s.basis=V at hR
    cases er : s.basis L.r0 <;> simp only [er,Bool.false_eq_true,if_false,if_true] at hR <;> omega
  have cleanY : regValue L.y.tail a.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (aOther q (fun e => yAway (e ▸ hq))).trans
      ((regValue_zero _ _).mp hY q (List.mem_of_mem_tail hq))
  have lengths : L.r.tail.length=L.y.tail.length := by
    have len := BalancedCleanup.widths L.toLayout hw
    simp [len.2.1,len.2.2.1]
  have cp := copyRegister_correct (some J) L.r.tail L.y.tail lengths (copyND L hn)
    (by
      intro q hq
      have eq : J=q := by simpa using hq
      rw [←eq]
      exact fun h => jY (List.mem_of_mem_tail h)) a m
  have tail : regValue L.y.tail (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis=
      if Jv then V/2 else 0 := by
    rw [cp.2.2,cleanY,sameR]
    simp [copyValue,aJ]
  have head : (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis (lowY L)=U := by
    rw [cp.2.1 _ yAway]
    simp [a,writeBit]
  have actual : run (copyControl L J B) m s=run (copyRegister (some J) L.r.tail L.y.tail) m a := by
    rw [copyControl,run_append,show measurementCount [.CCX J B (lowY L)]=0 from rfl,
      List.take_zero,List.drop_zero,first]
  rw [actual]
  refine ⟨cp.1,?_,head,?_⟩
  · rw [yHead]
    change (if (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis (lowY L) then 1 else 0)+
      2*regValue L.y.tail (run (copyRegister (some J) L.r.tail L.y.tail) m a).basis=_
    rw [head,tail]
    cases Jv <;> cases Bv <;> simp [U]
  · intro q hq
    exact (cp.2.1 q (fun h => hq (List.mem_of_mem_tail h))).trans
      (aOther q (fun e => hq (e.symm ▸ y0)))

structure Prepared (L : Layout) (J B : Wire) (Jv Bv : Bool) (Y : Int) (s t : State) : Prop where
  phase : t.phase=s.phase
  target : regValue L.r t.basis=if (Jv && Bv) then 2^256-1-encodeWord 256 (Y/2) else encodeWord 256 (Y/2)
  source : regValue L.y t.basis=(Jv && Bv).toNat+2*(if Jv then encodeWord 256 Y/2 else 0)
  parity : t.basis L.parity=originalParity Y
  a : t.basis L.lower=(originalParity Y && negative Y)
  d : t.basis L.one=(originalParity Y && (Jv && Bv))
  e : t.basis L.sign=((originalParity Y && negative Y) && (Jv && Bv))
  u : t.basis (lowY L)=(Jv && Bv)
  j : t.basis J=Jv
  b : t.basis B=Bv
  carry : ∀q∈L.carry,t.basis q=false
  outside : ∀q,q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign] → t.basis q=s.basis q

set_option maxHeartbeats 300000 in
theorem prepare_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    Prepared L J B Jv Bv Y s (run (prepare L J B) m s) := by
  let U := Jv && Bv
  let P := originalParity Y
  let H := negative Y
  let a := run (copyControl L J B) [] s
  let b := run (productsSeed L) [] a
  let c := run (rightShift L) [] b
  let d := run (signComplement (lowY L) L.r) [] c
  have len := BalancedCleanup.widths L.toLayout hw
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have ry := (List.nodup_append'.mp data).1
  have dis := (List.nodup_append'.mp ry).2.2
  have r0In : L.r0∈L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry :=
    flagAway L hn q (by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢;tauto)
  have fr (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r :=
    fun h => flag q hq (by simp [h])
  have fy (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.y :=
    fun h => flag q hq (by simp [h])
  have f0 (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q≠L.r0 :=
    fun e => fr q hq (e.symm ▸ r0In)
  have nr (q : Wire) (hq : q∉L.wires) : q∉L.r := fun h => hq (data_member L q (by simp [h]))
  have ny (q : Wire) (hq : q∉L.wires) : q∉L.y := fun h => hq (data_member L q (by simp [h]))
  have cp := copyControl_spec L hw hn J B hJ hB Jv Bv (encodeWord 256 Y) s [] hR hY hj hb
  change a.phase=s.phase ∧ _ at cp
  have R1 : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => cp.2.2.2 q (fun h => List.disjoint_left.mp dis hq h))).trans hR
  have signed : signedRegValue L.r a.basis=Y := by
    unfold signedRegValue
    rw [len.2.1,R1]
    apply decode_encodeWord 256 (by decide)
    have h := constants
    unfold Centered at hy
    norm_num only [Nat.reduceSub] at ⊢
    omega
  have p1 : a.basis L.r0=P := word_parity L.r0 (L.rtail++[L.rmsb]) a.basis Y signed
  have h1 : a.basis L.rmsb=H := word_sign L.low L.rmsb a.basis Y signed
  have z (q : Wire) (hq : q∈[L.parity,L.lower,L.one]) : a.basis q=false := by
    have mem : q∈[L.parity,L.lower,L.one,L.sign] := by simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢;tauto
    have hwork : q∈work L := by
      simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      tauto
    exact (cp.2.2.2 q (fy q mem)).trans (hc q hwork)
  have e0 : a.basis L.sign=false := (cp.2.2.2 _ (fy _ (by simp))).trans hz
  have seed := productsSeed_run L hw hn P H U a [] p1 h1 cp.2.2.1
    (z _ (by simp)) (z _ (by simp)) (z _ (by simp)) e0
  change b=⟨a.phase,_⟩ at seed
  have nd : [L.parity,L.lower,L.one,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03⟩,⟨n12,n13⟩,n23⟩
  have n10 := Ne.symm n01
  have n20 := Ne.symm n02
  have n30 := Ne.symm n03
  have n21 := Ne.symm n12
  have n31 := Ne.symm n13
  have n32 := Ne.symm n23
  have bP : b.basis L.parity=P := by rw [seed];simp [writeBit,Function.update,n01,n02,n03,f0 L.parity (by simp)]
  have bA : b.basis L.lower=(P && H) := by rw [seed];simp [writeBit,Function.update,n12,n13,f0 L.lower (by simp)]
  have bD : b.basis L.one=(P && U) := by rw [seed];simp [writeBit,Function.update,n23,f0 L.one (by simp)]
  have bE : b.basis L.sign=((P && H) && U) := by rw [seed];simp [writeBit,Function.update,f0 L.sign (by simp)]
  have bZero : b.basis L.r0=false := by rw [seed];simp [writeBit]
  have seedOff (q : Wire) (hq : q∉[L.parity,L.lower,L.one,L.sign]) (h0 : q≠L.r0) : b.basis q=a.basis q := by
    simp only [List.mem_cons,List.mem_singleton,not_or] at hq
    rw [seed]
    simp [writeBit,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2,h0]
  have tailValue : regValue L.r.tail b.basis=encodeWord 255 (Y/2) := by
    have same : regValue L.r.tail b.basis=regValue L.r.tail a.basis := by
      apply regValue_congr
      intro q hq
      have inR := List.mem_of_mem_tail hq
      apply seedOff q
      · intro h;exact fr q h inR
      · intro e;have nd := EntryHalf5.target_nodup L hn;rw [r_cons L] at nd
        exact (List.nodup_cons.mp nd).1 (e ▸ hq)
    rw [same]
    have enc := half_encoding Y hy
    rw [r_cons L] at R1
    change (if a.basis L.r0 then 1 else 0)+2*regValue L.r.tail a.basis=encodeWord 256 Y at R1
    rw [p1] at R1
    change encodeWord 256 Y=P.toNat+2*encodeWord 255 (Y/2) at enc
    cases pv : P <;> simp only [pv,Bool.false_eq_true,if_false,if_true,Bool.toNat_false,Bool.toNat_true] at R1 enc <;> omega
  have r2 : regValue L.r b.basis=2*encodeWord 255 (Y/2) := by
    rw [r_cons L]
    change (if b.basis L.r0 then 1 else 0)+2*regValue L.r.tail b.basis=_
    rw [bZero,tailValue];simp
  have rs := rightShift_spec L hw hn Y hy b [] r2
  change c.phase=b.phase ∧ _ at rs
  have comp := signComplement_correct (lowY L) L.r (EntryHalf5.target_nodup L hn)
    (by intro h;have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
        exact List.disjoint_left.mp dis h y0) c []
  have after (q : Wire) (hq : q∉L.r) : d.basis q=b.basis q :=
    (comp.2.1 q hq).trans (rs.2.2 q hq)
  have inY (q : Wire) (hq : q∈L.y) : b.basis q=a.basis q := by
    apply seedOff q
    · intro h;exact fy q h hq
    · intro e;exact List.disjoint_left.mp dis (e.symm ▸ r0In) hq
  have uIn : lowY L∈L.y := by rw [y_cons L hw];simp
  have uNotR : lowY L∉L.r := fun h => List.disjoint_left.mp dis h uIn
  have bU : b.basis (lowY L)=U := (inY _ uIn).trans cp.2.2.1
  have cU : c.basis (lowY L)=U := (rs.2.2 _ uNotR).trans bU
  have outside (q : Wire) (hq : q∉L.r++L.y++[L.parity,L.lower,L.one,L.sign]) : d.basis q=s.basis q := by
    simp only [List.mem_append,not_or] at hq
    exact (after q hq.1.1).trans ((seedOff q hq.2 (fun e => hq.1.1 (e.symm ▸ r0In))).trans (cp.2.2.2 q hq.1.2))
  have actual : run (prepare L J B) m s=d := by
    rw [←run_take (prepare L J B) m s,(prepare_counts L hw J B).2,List.take_zero,prepare_shape]
    simp only [run_append]
    have cc : measurementCount (copyControl L J B)=0 := by
      have c := copyRegister_counts (some J) L.r.tail L.y.tail (by simp [len.2.1,len.2.2.1])
      simp [copyControl,measurementCount_append,measurementCount,c.2]
    have ps : measurementCount (productsSeed L)=0 := rfl
    have rr : measurementCount (rightShift L)=0 := by simp [rightShift,measurementCount_append,(rotate_counts _).2.1,measurementCount]
    simp only [measurementCount_append,cc,ps,rr,Nat.zero_add,List.take_zero,List.drop_zero]
    rfl
  rw [actual]
  refine ⟨comp.1.trans (rs.1.trans ((congrArg State.phase seed).trans cp.1)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,outside⟩
  · rw [comp.2.2,cU,rs.2.1,len.2.1]
  · exact (regValue_congr _ _ _ (fun q hq => (after q (fun r => List.disjoint_left.mp dis r hq)).trans (inY q hq))).trans cp.2.1
  · exact (after _ (fr _ (by simp))).trans bP
  · exact (after _ (fr _ (by simp))).trans bA
  · exact (after _ (fr _ (by simp))).trans bD
  · exact (after _ (fr _ (by simp))).trans bE
  · exact (after _ uNotR).trans bU
  · apply (outside J _).trans hj
    simp only [List.mem_append,not_or]
    refine ⟨⟨nr J hJ,ny J hJ⟩,?_⟩
    intro h
    apply hJ
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  · apply (outside B _).trans hb
    simp only [List.mem_append,not_or]
    refine ⟨⟨nr B hB,ny B hB⟩,?_⟩
    intro h
    apply hB
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  · intro q hq
    have nd := List.nodup_append'.mp data
    have qr : q∉L.r++L.y := fun h => List.disjoint_left.mp nd.2.2 h hq
    have qf : q∉[L.parity,L.lower,L.one,L.sign] := fun h => flag q h (by simp [hq])
    exact (outside q (fun h => (List.mem_append.mp h).elim qr qf)).trans (hc q (by simp [work,hq]))

set_option maxHeartbeats 200000 in
theorem prefix_spec (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    PrefixResult L J B Jv Bv Y s (run (prefixProgram L J B) m s) := by
  let a := run (prepare L J B) [] s
  let t := run (arithmetic L) m a
  have prep := prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have len := BalancedCleanup.widths L.toLayout hw
  have add := Affine.add_correct (sources L) L.r (L.carry.take 255) (lowY L)
    (arithmeticND L hw hn) (sources_away L hw hn)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1]) a m
    (fun q hq => prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  change t.phase=a.phase ∧ (∀q,q∉L.r → t.basis q=a.basis q) ∧
    regValue L.r t.basis=(Affine.value (sources L) a.basis+regValue L.r a.basis+(a.basis (lowY L)).toNat)%2^L.r.length at add
  have sourceValue := sources_value L (originalParity Y) (negative Y) (Jv && Bv) a.basis
    prep.parity prep.a prep.d prep.e
  have result : regValue L.r t.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) := by
    rw [add.2.2,sourceValue,prep.target,prep.u,len.2.1]
    exact folded_encoding (Jv && Bv) Y hy
  have data := (List.nodup_append'.mp (allND L hn)).2.1
  have dis := (List.nodup_append'.mp (List.nodup_append'.mp data).1).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r := by
    intro h
    have member : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp
    exact flagAway L hn q member (by simp [h])
  have control (q : Wire) (hq : q∉L.wires) : q∉L.r :=
    fun h => hq (data_member L q (by simp [h]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have actual : run (prefixProgram L J B) m s=t := by
    rw [prefixProgram,run_append,(prepare_counts L hw J B).2,List.take_zero,List.drop_zero]
  rw [actual]
  refine ⟨add.1.trans prep.phase,result,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => add.2.1 q (fun h => List.disjoint_left.mp dis h hq))).trans prep.source
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.parity
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.a
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.d
  · exact (add.2.1 _ (flag _ (by simp))).trans prep.e
  · exact (add.2.1 _ (fun h => List.disjoint_left.mp dis h y0)).trans prep.u
  · exact (add.2.1 _ (control _ hJ)).trans prep.j
  · exact (add.2.1 _ (control _ hB)).trans prep.b
  · intro q hq
    have apart : q∉L.r := fun h => List.disjoint_left.mp (List.nodup_append'.mp data).2.2 (List.mem_append_left _ h) hq
    exact (add.2.1 q apart).trans (prep.carry q hq)
  · intro q hq
    have apart : q∉L.r := by simp only [List.mem_append,not_or] at hq;exact hq.1.1
    exact (add.2.1 q apart).trans (prep.outside q hq)

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryFrame

set_option linter.unusedSimpArgs false
/-! Final frame composition for the retained-site joint entry. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

/-- The copied low source bit and the copied high source bits reconstruct Y. -/
theorem encoded_parity_decomposition (Y : Int) (hy : Centered Y) :
    (originalParity Y).toNat + 2 * (encodeWord 256 Y / 2) = encodeWord 256 Y := by
  have hc := constants
  have signed := decode_encodeWord 256 (by decide) Y (by
    unfold Centered at hy
    norm_num only [Nat.reduceSub]
    omega)
  have low := signedDecode_mod_two 256 (encodeWord 256 Y) (by decide)
  rw [signed] at low
  have rem : encodeWord 256 Y % 2 = (originalParity Y).toNat := by
    have cast : ((encodeWord 256 Y % 2 : Nat) : Int) = Y % 2 := by
      simpa only [Int.natCast_emod, Nat.cast_ofNat] using low.symm
    cases hp : originalParity Y
    · have hz : Y % 2 = 0 := by simpa only [originalParity, decide_eq_false_iff_not,
        not_not] using hp
      simp only [hp, Bool.toNat_false]
      omega
    · have hz : Y % 2 ≠ 0 := by simpa only [originalParity, decide_eq_true_eq] using hp
      simp only [hp, Bool.toNat_true]
      omega
  have h := Nat.mod_add_div (encodeWord 256 Y) 2
  rwa [rem] at h

/-- This is the source value after deferred bit0 is filled. -/
theorem source_value_after_fill (J : Bool) (Y : Int) (hy : Centered Y) :
    (J && originalParity Y).toNat +
      2 * (if J then encodeWord 256 Y / 2 else 0) =
        encodeWord 256 (if J then Y else 0) := by
  cases J
  · simp [encodeWord]
  · simpa only [Bool.true_and, if_true] using encoded_parity_decomposition Y hy

/-- A numeric pending-source value determines the unchanged high source word. -/
theorem pending_source_high (L : Layout) (hw : L.Widths) (s : BasisState)
    (U : Bool) (high : Nat) (hU : s (L.ylow.getD 0 0) = U)
    (hvalue : regValue L.y s = U.toNat + 2*high) :
    regValue (L.ylow.drop 1 ++ [L.ymsb]) s = high := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    have low : s a = U := by simpa only [hy, List.getD_cons_zero] using hU
    simp only [BalancedCleanup.Layout.y, hy, List.cons_append] at hvalue
    change regValue (as ++ [L.ymsb]) s = high
    change (if s a then 1 else 0) + 2*regValue (as ++ [L.ymsb]) s = _ at hvalue
    rw [low] at hvalue
    cases U <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true,
      if_false, if_true] at hvalue <;> omega

/-- Final source reconstruction needs only its head and high-word values. -/
theorem source_frame_of_parts (L : Layout) (hw : L.Widths) (s : BasisState)
    (J : Bool) (Y : Int) (hy : Centered Y)
    (hlow : s (L.ylow.getD 0 0) = (J && originalParity Y))
    (hhigh : regValue (L.ylow.drop 1 ++ [L.ymsb]) s =
      if J then encodeWord 256 Y / 2 else 0) :
    regValue L.y s = encodeWord 256 (if J then Y else 0) := by
  cases hys : L.ylow with
  | nil => have h := hw.2.1; simp [hys] at h
  | cons a as =>
    have low : s a = (J && originalParity Y) := by
      simpa only [hys, List.getD_cons_zero] using hlow
    have high : regValue (as ++ [L.ymsb]) s =
        if J then encodeWord 256 Y / 2 else 0 := by
      simpa only [hys, List.drop_succ_cons, List.drop_zero] using hhigh
    simp only [BalancedCleanup.Layout.y, hys, List.cons_append]
    change (if s a then 1 else 0) + 2*regValue (as ++ [L.ymsb]) s = _
    rw [low, high]
    simpa only [Bool.toNat, Bool.cond_eq_ite] using source_value_after_fill J Y hy

/-- Read the new sign from the checked centered target value. -/
theorem target_sign_of_value (L : Layout) (hw : L.Widths) (R : Int)
    (hr : Centered R) (s : BasisState) (hR : regValue L.r s = encodeWord 256 R) :
    s L.rmsb = negative R := by
  have hc := constants
  have signed : signedRegValue L.r s = R := by
    unfold signedRegValue
    rw [(BalancedCleanup.widths L.toLayout hw).2.1, hR]
    apply decode_encodeWord 256 (by decide)
    unfold Centered at hr
    norm_num only [Nat.reduceSub]
    omega
  exact word_sign L.low L.rmsb s R signed

/-- The new sign supplies the measured old-sign-product correction. -/
theorem scalar_erase_relation (L : Layout) (hw : L.Widths)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : BasisState)
    (hR : regValue L.r s = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s L.parity = originalParity Y)
    (hA : s L.lower = (originalParity Y && negative Y))
    (hD : s L.one = (originalParity Y && (Jv && Bv))) :
    s L.lower = ((s L.parity && s L.rmsb) ^^ s L.parity ^^ s L.one) := by
  have bounds := signedY_bounds (Jv && Bv) Y hy
  have hc := constants
  have hr := (halfResult_spec (signedY (Jv && Bv) Y)
    (by unfold Centered at bounds; omega)).1
  have sign := target_sign_of_value L hw _ hr s hR
  rw [hA, hP, hD, sign]
  exact oldSign_product (Jv && Bv) Y hy

private theorem joint_11_source_head_member (L : Layout) (hw : L.Widths) :
    L.ylow.getD 0 0 ∈ L.y := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as => simp [BalancedCleanup.Layout.y, hy]

private theorem joint_11_source_head_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.ylow.getD 0 0 ∉ L.r ++ L.carry := by
  have nd : (L.r ++ (L.y ++ L.carry)).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (allND L hn)).2.1
  have rsep := (List.nodup_append'.mp nd).2.2
  have ysep := (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.2
  intro h
  rcases List.mem_append.mp h with hr | hc
  · exact List.disjoint_left.mp rsep hr (List.mem_append_left _ (joint_11_source_head_member L hw))
  · exact List.disjoint_left.mp ysep (joint_11_source_head_member L hw) hc

private theorem joint_11_erased_data_keep (L : Layout) (hn : L.wires.Nodup)
    (J : Wire) (s : BasisState) (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
    (hu : q ≠ L.ylow.getD 0 0) :
    erasedBasis L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J s q = s q := by
  have away (v : Wire) (hv : v ∈ [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q ≠ v := fun e => flagAway L hn v hv (e ▸ hq)
  simp only [erasedBasis, writeBit, Function.update_of_ne hu,
    Function.update_of_ne (away L.one (by simp)),
    Function.update_of_ne (away L.lower (by simp)),
    Function.update_of_ne (away L.sign (by simp))]

/-- Compose the two checked measured cleanup blocks on abstract States. -/
theorem finish_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false) :
    run (eraseScalarsAt L J B ++ clearParity L J) m s =
      ⟨s.phase, writeBit (erasedBasis L.parity L.lower L.one L.sign
        (L.ylow.getD 0 0) J s.basis) L.parity false⟩ := by
  let t : State := ⟨s.phase, erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis⟩
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have ha := scalar_erase_relation L hw Jv Bv Y hy s.basis hR hP hA
    (by simpa only [hP,hU,hJv,hBv] using hD)
  have erase := eraseScalarsAt_run L hw hn J B hJ hB hJB s
    (m.take (measurementCount (eraseScalarsAt L J B))) hE ha hD hU
  have keep (q : Wire) (hq : q ∈ L.r ++ L.carry) : t.basis q = s.basis q := by
    apply joint_11_erased_data_keep L hn J s.basis q
    · rcases List.mem_append.mp hq with hr | hc
      · exact List.mem_append_left _ (List.mem_append_left _ hr)
      · exact List.mem_append_right _ hc
    · exact fun e => joint_11_source_head_away L hw hn (e ▸ hq)
  have tr : regValue L.r t.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (List.mem_append_left _ hq))).trans hR
  have tp : t.basis L.parity = originalParity Y := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne pU,
      Function.update_of_ne pD,Function.update_of_ne pA,Function.update_of_ne pE] using hP
  have tu : t.basis (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [t,erasedBasis,writeBit,Function.update_self,hJv,hP]
  have tj : t.basis J = Jv := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne (Ne.symm uJ),
      Function.update_of_ne (Ne.symm dJ),Function.update_of_ne (Ne.symm aJ),
      Function.update_of_ne (Ne.symm eJ)] using hJv
  have ta : t.basis L.lower = false := by
    simp only [t,erasedBasis,writeBit,Function.update_of_ne aU,
      Function.update_of_ne aD,Function.update_self]
  have tc (q : Wire) (hq : q ∈ L.carry) : t.basis q = false :=
    (keep q (List.mem_append_right _ hq)).trans (hc q hq)
  have parity := clearParity_run L hw hn J hJ Jv Bv Y hy t
    (m.drop (measurementCount (eraseScalarsAt L J B))) tr tp tu tj ta tc
  rw [run_append, erase]
  exact parity

private theorem joint_11_source_high_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q ∈ L.ylow.drop 1 ++ [L.ymsb]) :
    q ∈ L.y ∧ q ≠ L.ylow.getD 0 0 := by
  have nd := (List.nodup_append'.mp (allND L hn)).2.1
  have ny : L.y.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    have tail : q ∈ as ++ [L.ymsb] := by simpa only [hy, List.drop_succ_cons, List.drop_zero] using hq
    have na : a ∉ as ++ [L.ymsb] := by
      have yn : (a :: (as ++ [L.ymsb])).Nodup := by
        simpa only [BalancedCleanup.Layout.y, hy, List.cons_append] using ny
      exact (List.nodup_cons.mp yn).1
    exact ⟨by simp [BalancedCleanup.Layout.y,hy,tail], by
      simpa only [hy,List.getD_cons_zero] using (fun e => na (e ▸ tail) : q ≠ a)⟩

/-- Close the two-word frame after the arithmetic prefix. Only its four live
scalar products are excluded from the prefix's outside-bit frame. -/
theorem finish_pair_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (before s : State) (m : List Bool)
    (phase : s.phase = before.phase)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hYS : regValue L.y s.basis = (Jv && Bv).toNat +
      2*(if Jv then encodeWord 256 Y / 2 else 0))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false)
    (clean : ∀ q ∈ [L.parity,L.lower,L.one,L.sign], before.basis q = false)
    (outside : ∀ q, q ∉ L.r → q ∉ L.y → q ≠ L.parity → q ≠ L.lower →
      q ≠ L.one → q ≠ L.sign → s.basis q = before.basis q) :
    let out := run (eraseScalarsAt L J B ++ clearParity L J) m s
    out.phase = before.phase ∧ PairFrame L.r L.y before.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let bits := writeBit (erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis) L.parity false
  have result := finish_run L hw hn J B hJ hB hJB Jv Bv Y hy s m hR hP hA hD hE hU hJv hBv hc
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have data_keep (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
      (hu : q ≠ L.ylow.getD 0 0) : bits q = s.basis q := by
    have qp : q ≠ L.parity := fun e => flagAway L hn _ (by simp) (e ▸ hq)
    simpa only [bits,writeBit,Function.update_of_ne qp] using joint_11_erased_data_keep L hn J s.basis q hq hu
  have rkeep (q : Wire) (hq : q ∈ L.r) : bits q = s.basis q := by
    apply data_keep q (List.mem_append_left _ (List.mem_append_left _ hq))
    exact fun e => joint_11_source_head_away L hw hn (e ▸ List.mem_append_left _ hq)
  have low : bits (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pU),
      Function.update_self,hJv,hP]
  have high : regValue (L.ylow.drop 1 ++ [L.ymsb]) bits =
      if Jv then encodeWord 256 Y / 2 else 0 := by
    have old := pending_source_high L hw s.basis (Jv && Bv)
      (if Jv then encodeWord 256 Y / 2 else 0) (by rw [hU,hJv,hBv]) hYS
    apply Eq.trans (regValue_congr _ _ _ ?_) old
    intro q hq
    have away := joint_11_source_high_away L hw hn q hq
    exact data_keep q (List.mem_append_left _ (List.mem_append_right _ away.1)) away.2
  have source := source_frame_of_parts L hw bits Jv Y hy low high
  dsimp only
  rw [result]
  refine ⟨phase, (regValue_congr _ _ _ rkeep).trans hR, source, ?_⟩
  intro q hr hys
  change bits q = before.basis q
  by_cases qp : q = L.parity
  · subst q
    simp only [bits,writeBit,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qa : q = L.lower
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pA),
      Function.update_of_ne aU,Function.update_of_ne aD,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qd : q = L.one
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pD),
      Function.update_of_ne dU,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qe : q = L.sign
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pE),
      Function.update_of_ne eU,Function.update_of_ne (Ne.symm dE),
      Function.update_of_ne (Ne.symm aE),Function.update_self]
    exact (clean _ (by simp)).symm
  have qu : q ≠ L.ylow.getD 0 0 := fun e => hys (e ▸ joint_11_source_head_member L hw)
  have same : bits q = s.basis q := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne qp,Function.update_of_ne qu,
      Function.update_of_ne qd,Function.update_of_ne qa,Function.update_of_ne qe]
  exact same.trans (outside q hr hys qp qa qd qe)

/-- Complete-State frame of the retained-site entry for every record tape. -/
theorem program_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y) (hY : regValue L.y s.basis = 0)
    (hclean : ∀ q ∈ BalancedCircuit.work L, s.basis q = false)
    (hSign : s.basis L.sign = false) (hJv : s.basis J = Jv) (hBv : s.basis B = Bv) :
    let out := run (program L J B) m s
    out.phase = s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let t := run (prefixProgram L J B) (m.take (measurementCount (prefixProgram L J B))) s
  have result := prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s
    (m.take (measurementCount (prefixProgram L J B))) hR hY hclean hSign hJv hBv
  change PrefixResult L J B Jv Bv Y s t at result
  have clean (q : Wire) (hq : q ∈ [L.parity,L.lower,L.one,L.sign]) : s.basis q = false := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hSign
  have d : t.basis L.one = (t.basis L.parity && t.basis (L.ylow.getD 0 0)) := by
    simpa only [result.parity,show t.basis (L.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.d
  have e : t.basis L.sign = (t.basis L.lower && t.basis (L.ylow.getD 0 0)) := by
    simpa only [result.a,show t.basis (L.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.e
  have u : t.basis (L.ylow.getD 0 0) = (t.basis J && t.basis B) := by
    rw [result.j,result.b]
    exact result.u
  have outside (q : Wire) (hr : q ∉ L.r) (hy : q ∉ L.y) (qp : q ≠ L.parity)
      (qa : q ≠ L.lower) (qd : q ≠ L.one) (qe : q ≠ L.sign) : t.basis q = s.basis q :=
    result.outside q (by simp [hr,hy,qp,qa,qd,qe])
  have finish := finish_pair_frame L hw hn J B hJ hB hJB Jv Bv Y hy s t
    (m.drop (measurementCount (prefixProgram L J B))) result.phase result.target result.source
    result.parity result.a d e u result.j result.b result.carry clean outside
  dsimp only
  rw [program,List.append_assoc,run_append]
  exact finish

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryLayoutHelpers

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 100000
namespace ECDSAAdd.Entrant.EntryHalf5
open Arithmetic BalancedCircuit BalancedField

def lastCarry (L : Layout) : Wire := L.carry.getD 255 0

theorem carry_split (L : Layout) (hw : L.Widths) :
    L.carry=L.carry.take 255++[lastCarry L] := by
  have hi : 255<L.carry.length := by rw [hw.2.2];decide
  have h := List.take_succ_eq_append_getElem hi
  have e : L.carry.getD 255 0=L.carry[255] := by simp [List.getD,hi]
  simpa only [show 255+1=256 from rfl,←hw.2.2,List.take_length,←e,lastCarry] using h

def scalarPorts (L : Layout) : List Wire :=
  [L.parity,L.lower,L.cout,L.minus,L.plus,lastCarry L,L.sourceGuard,L.one,L.sign]

theorem allWithLastND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (scalarPorts L++(L.r++L.y++L.carry.take 255)).Nodup := by
  have h := allND L hn
  rw [carry_split L hw] at h
  apply List.nodup_iff_count.mpr
  intro q
  have c := List.nodup_iff_count.mp h q
  simp only [scalarPorts,List.count_cons,List.count_append,List.count_nil] at c ⊢
  omega

theorem scalarPortsND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (scalarPorts L).Nodup := (List.nodup_append'.mp (allWithLastND L hw hn)).1

theorem scalarAway (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈scalarPorts L) : q∉L.r++L.y++L.carry.take 255 :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (allWithLastND L hw hn)).2.2 hq h

theorem lastCarry_mem (L : Layout) (hw : L.Widths) : lastCarry L∈L.carry := by
  rw [carry_split L hw];simp

end ECDSAAdd.Entrant.EntryHalf5

end

section
-- Verified component FrontierEntryResources

set_option linter.unusedSimpArgs false

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic Challenge RecordedQuantum Baselines BalancedCircuit

namespace Affine

theorem fan_slots (qs : List Wire) (a : Wire) : gateSlots (fan qs a) = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change 1 + gateSlots (fan qs a) = qs.length + 1
    rw [ih]
    omega

def slotCost : List Bit → Nat
  | [] => 0
  | [b] => b.terms.length+2
  | b::b'::bs => 5*b.terms.length+12+slotCost (b'::bs)

theorem local_slots (b : Bit) (y cin co : Wire) :
    gateSlots (majority b y cin co) = 2*b.terms.length+6 ∧
    gateSlots (erase b y cin co) = 2*b.terms.length+4 ∧
    gateSlots (sum b y cin) = b.terms.length+2 := by
  simp only [majority,erase,sum,view,gateSlots_append,reverse_gateSlots,fan_slots,
    Bit.wires,List.length_cons]
  norm_num [Arithmetic.majority,eraseCarry,gateSlots,instructionSlots]
  omega

theorem add_slots (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (hl : bs.length = ys.length) (hc : carry.length+1 = ys.length) :
    gateSlots (add bs ys carry cin) = slotCost bs := by
  induction bs generalizing ys carry cin with
  | nil => have h : ys = [] := List.eq_nil_of_length_eq_zero hl.symm; simp [add,h,slotCost,gateSlots]
  | cons b bs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      cases bs with
      | nil =>
        have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
        subst ys
        simpa only [add,slotCost] using (local_slots b y cin cin).2.2
      | cons b' bs =>
        cases ys with
        | nil => simp at hl
        | cons y' ys =>
          cases carry with
          | nil => simp at hc
          | cons c cs =>
            have rest := ih (y'::ys) cs c (by simpa using hl) (by simpa using hc)
            simp only [add,gateSlots_append,slotCost] at rest ⊢
            rw [(local_slots b y cin c).1,(local_slots b y cin c).2.1,
              (local_slots b y cin c).2.2,rest]
            omega

def lengthCost : List Nat → Nat
  | [] => 0
  | [k] => k+2
  | k::k'::ks => 5*k+12+lengthCost (k'::ks)

theorem slotCost_lengths (bs : List Bit) :
    slotCost bs = lengthCost (bs.map (fun b => b.terms.length)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons b' bs => simp only [slotCost,List.map_cons,lengthCost,ih]


theorem fan_support_to (qs : List Wire) (a : Wire) (W : Finset Wire)
    (ha : a ∈ W) (hs : ∀ q ∈ qs, q ∈ W) : wires (fan qs a) ⊆ W := by
  intro q hq
  have h := fan_support qs a hq
  simp only [List.mem_toFinset,List.mem_cons] at h
  rcases h with rfl | h
  · exact ha
  · exact hs q h

theorem local_support (b : Bit) (y cin co : Wire) (W : Finset Wire)
    (hs : ∀ q ∈ b.wires, q ∈ W) (hy : y ∈ W) (hc : cin ∈ W) (ho : co ∈ W) :
    wires (majority b y cin co) ⊆ W ∧ wires (erase b y cin co) ⊆ W ∧
      wires (sum b y cin) ⊆ W := by
  have ha := hs b.wire (by simp [Bit.wires])
  have hv := fan_support_to b.terms b.wire W ha (fun q hq => hs q (by simp [Bit.wires,hq]))
  have hm : wires (Arithmetic.majority b.wire y cin co) ⊆ W := by
    simp [Arithmetic.majority,wires,Instr.wires,Finset.union_subset_iff,
      Finset.insert_subset_iff,ha,hy,hc,ho]
  have he : wires (eraseCarry b.wire y cin co) ⊆ W := by
    simp [eraseCarry,wires,Instr.wires,correctionWires,Finset.union_subset_iff,
      Finset.insert_subset_iff,ha,hy,hc,ho]
  have hf := fan_support_to b.wires y W hy hs
  have cx : wires [Instr.CX cin y] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hc,hy]
  simp only [majority,erase,sum,view,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨⟨hv,hm⟩,hv⟩,⟨⟨hv,he⟩,hv⟩,⟨hf,cx⟩⟩

theorem add_support_to (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (W : Finset Wire) (hs : ∀ q ∈ sites bs, q ∈ W)
    (hy : ∀ q ∈ ys, q ∈ W) (hc : ∀ q ∈ carry, q ∈ W) (hi : cin ∈ W) :
    wires (add bs ys carry cin) ⊆ W := by
  induction bs generalizing ys carry cin with
  | nil => simp [add,wires]
  | cons b bs ih =>
    have head (q : Wire) (hq : q ∈ b.wires) : q ∈ W := hs q (head_mem b bs q hq)
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [add,wires]
      | cons y ys =>
        cases ys with
        | nil => exact (local_support b y cin cin W head (hy y (by simp)) hi hi).2.2
        | cons y' ys => simp [add,wires]
    | cons b' bs =>
      cases ys with
      | nil => simp [add,wires]
      | cons y ys =>
        cases ys with
        | nil => simp [add,wires]
        | cons y' ys =>
          cases carry with
          | nil => simp [add,wires]
          | cons c cs =>
            have rest := ih (y'::ys) cs c
              (fun q hq => hs q (tail_mem b (b'::bs) q hq))
              (fun q hq => hy q (by simp [hq]))
              (fun q hq => hc q (by simp [hq])) (hc c (by simp))
            have stepRes := local_support b y cin c W head (hy y (by simp)) hi (hc c (by simp))
            simp only [add,wires_append,Finset.union_subset_iff]
            exact ⟨⟨⟨stepRes.1,rest⟩,stepRes.2.1⟩,stepRes.2.2⟩


theorem fan_physical (qs : List Wire) (a : Wire) (ha : a ∉ qs) : GatePhysical (fan qs a) := by
  intro i hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
  exact fun e => ha (e ▸ hq)

private theorem joint_13_reverse_physical (p : Program) (hp : GatePhysical p) : GatePhysical p.reverse := by
  intro i hi
  exact hp i (List.mem_reverse.mp hi)

theorem local_physical (b : Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀ q ∈ b.wires, q ∉ [y,cin,co]) :
    GatePhysical (majority b y cin co) ∧ GatePhysical (erase b y cin co) ∧
      GatePhysical (sum b y cin) := by
  have hv : GatePhysical (view b) := fan_physical b.terms b.wire hb
  have hr := joint_13_reverse_physical (view b) hv
  have nd : [b.wire,y,cin,co].Nodup := List.nodup_cons.mpr
    ⟨ha b.wire (by simp [Bit.wires]),hn⟩
  have hc : cin ≠ y := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
  have hf := fan_physical b.wires y (fun h => ha y h (by simp))
  have cx : GatePhysical [Instr.CX cin y] := by simpa [GatePhysical,PhysicalInstr,ProperGate] using hc
  simp only [majority,erase,sum,gatePhysical_append]
  exact ⟨⟨⟨hv,majority_physical _ _ _ _ nd⟩,hr⟩,
    ⟨⟨hv,eraseCarry_physical _ _ _ _⟩,hr⟩,⟨hf,cx⟩⟩

theorem add_physical (bs : List Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin :: (ys ++ carry)).Nodup)
    (hs : ∀ q ∈ sites bs, q ∉ cin :: (ys ++ carry))
    (hv : ∀ b ∈ bs, b.Valid) : GatePhysical (add bs ys carry cin) := by
  induction bs generalizing ys carry cin with
  | nil => simp [add,GatePhysical]
  | cons b bs ih =>
    have hb := hv b (by simp)
    have head (q : Wire) (hq : q ∈ b.wires) := hs q (head_mem b bs q hq)
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [add,GatePhysical]
      | cons y ys =>
        cases ys with
        | cons y' ys => simp [add,GatePhysical]
        | nil =>
          have ci : cin ≠ y := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
          have yf : y ∉ b.wires := fun h => head y h (by simp)
          simp only [add,sum,gatePhysical_append]
          exact ⟨fan_physical b.wires y yf,by simpa [GatePhysical,PhysicalInstr,ProperGate] using ci⟩
    | cons b' bs =>
      cases ys with
      | nil => simp [add,GatePhysical]
      | cons y ys =>
        cases ys with
        | nil => simp [add,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [add,GatePhysical]
          | cons c cs =>
            have nd : [y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have away (q : Wire) (hq : q ∈ b.wires) (bad : q ∈ [y,cin,c]) : False := by
              apply head q hq
              simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
              rcases bad with rfl | rfl | rfl <;> simp
            have nr : (c :: ((y'::ys) ++ cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            have sr (q : Wire) (hq : q ∈ sites (b'::bs)) : q ∉ c :: ((y'::ys) ++ cs) := by
              intro bad
              apply hs q (tail_mem b (b'::bs) q hq)
              rcases List.mem_cons.mp bad with rfl | bad
              · simp
              · rcases List.mem_append.mp bad with hy | hc
                · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ hy))
                · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
            have rest := ih (y'::ys) cs c nr sr (fun k hk => hv k (by simp [hk]))
            have stepRes := local_physical b hb y cin c nd away
            simp only [add,gatePhysical_append]
            exact ⟨⟨⟨stepRes.1,rest⟩,stepRes.2.1⟩,stepRes.2.2⟩

end Affine

private def joint_13_termLength (i : Nat) : Nat :=
  if i=3 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=31 ∨ i=255 then 2 else 1

private theorem joint_13_source_lengths (L : Layout) :
    (sources L).map (fun b => b.terms.length) = (List.range 256).map joint_13_termLength := by
  simp only [sources,List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,source,joint_13_termLength]
  split_ifs <;> simp_all
  all_goals omega

private theorem joint_13_source_length_cost :
    Affine.lengthCost ((List.range 256).map joint_13_termLength) = 4369 := by decide +kernel

theorem arithmetic_slots (L : Layout) (hw : L.Widths) : gateSlots (arithmetic L) = 4369 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_slots (sources L) L.r (L.carry.take 255) (lowY L)
    (by rw [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  have cost : Affine.slotCost (sources L) = 4369 := by
    rw [Affine.slotCost_lengths,joint_13_source_lengths]
    exact joint_13_source_length_cost
  exact h.trans cost


def retSites (L : Layout) (J B : Wire) : Finset Wire :=
  (L.r ++ L.y ++ L.carry.take 255 ++ [L.parity,L.lower,L.one,L.sign,J,B]).toFinset

theorem program_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (program L J B) ⊆ retSites L J B := by
  let W := retSites L J B
  have data (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry.take 255) : q ∈ W := by
    simp only [W,retSites,List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl hq
  have scalar (q : Wire) (hq : q ∈ [L.parity,L.lower,L.one,L.sign,J,B]) : q ∈ W := by
    exact List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hd := scalar L.one (by simp)
  have he := scalar L.sign (by simp)
  have hj := scalar J (by simp)
  have hb := scalar B (by simp)
  have r (q : Wire) (hq : q ∈ L.r) : q ∈ W := data q (by simp [hq])
  have y (q : Wire) (hq : q ∈ L.y) : q ∈ W := data q (by simp [hq])
  have c (q : Wire) (hq : q ∈ L.carry.take 255) : q ∈ W := data q (by simp [hq])
  have r0 := r L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L ∈ L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have ul : L.ylow[0]?.getD 0 ∈ W := u
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by rw [len.2.1]; decide
  have ri := r (L.r.getD 254 0) (by rw [List.getD_eq_getElem _ _ idx]; exact List.getElem_mem _)
  have riAlt : L.r[254]?.getD 0 ∈ W := ri
  have cp : wires (copyRegister (some J) L.r.tail L.y.tail) ⊆ W := by
    rw [copyRegister_wires _ _ _ (by simp [len.2.1,len.2.2.1])]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_singleton] at hq
      rcases hq with (rfl | hq) | hq
      · exact hj
      · exact r q (List.mem_of_mem_tail hq)
      · exact y q (List.mem_of_mem_tail hq)
  have rot : wires (rotateRight L.r) ⊆ W := by
    rw [(rotate_wires L.r).1,if_neg (by rw [len.2.1]; omega)]
    exact fun q hq => r q (List.mem_toFinset.mp hq)
  have comp (ctl : Wire) (hctl : ctl ∈ W) : wires (signComplement ctl L.r) ⊆ W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl | h
    · exact hctl
    · exact r q h
  have first : wires [Instr.CCX J B (lowY L)] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hj,hb,u]
  have seeds : wires [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0] ⊆ W := by
    simp [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,r0,rh,hp,ha,hd,he,u]
  have extend : wires [Instr.CX (L.r.getD 254 0) L.rmsb] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,ri,riAlt,rh]
  have prep : wires (prepare L J B) ⊆ W := by
    simpa only [prepare,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) (comp _ u)
  have arith : wires (arithmetic L) ⊆ W := Affine.add_support_to _ _ _ _ W
    (fun q hq => scalar q (by
      have h := sources_sites L q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl <;> simp)) r c u
  have erase : wires (eraseScalarsAt L J B) ⊆ W := by
    simp [eraseScalarsAt,eraseScalars,wires,Instr.wires,correctionWires,
      Finset.union_subset_iff,Finset.insert_subset_iff,hp,ha,hd,he,u,ul,hj,hb,rh,lowY]
  have mag : wires (EntryHalf5.prepareMagnitude L) ⊆ W := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,
      Finset.union_subset_iff]
    exact ⟨by simp [wires,Instr.wires,Finset.insert_subset_iff,rh,ha],comp _ ha⟩
  have carry : wires (EntryHalf5.parityCarry L J) ⊆ W := by
    apply (DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | hq | hq
    · exact hj
    · exact hp
    · exact ha
    · exact r q (List.mem_append_left _ hq)
    · exact c q hq
  have parity : wires (clearParity L J) ⊆ W := by
    simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,
      wires_append,wires_reverse,Finset.union_subset_iff]
    refine ⟨?_,⟨⟨?_,⟨mag,⟨carry,mag⟩⟩⟩,?_⟩⟩
    · simp [wires,Instr.wires,Finset.insert_subset_iff,u,ul,hp,lowY]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
  simpa only [program,prefixProgram,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro prep arith) erase) parity


private theorem joint_13_high_copy_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.r.getD 254 0 ≠ L.rmsb := by
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by rw [len.2.1]; decide
  have split := List.take_succ_eq_append_getElem idx
  have take : L.r.take 255 = L.low := by
    change (L.low ++ [L.rmsb]).take 255 = L.low
    rw [←len.1,List.take_left]
  rw [show 254+1=255 from rfl,take] at split
  have member : L.r.getD 254 0 ∈ L.low := by
    rw [split,List.getD_eq_getElem _ _ idx]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have nd := EntryHalf5.target_nodup L hn
  have apart := (List.nodup_append'.mp nd).2.2
  exact fun e => List.disjoint_left.mp apart (e ▸ member) (by simp)

theorem program_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (program L J B) := by
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have uD : L.ylow[0]?.getD 0 ≠ L.one := Ne.symm dU
  have uE : L.ylow[0]?.getD 0 ≠ L.sign := Ne.symm eU
  have jU : J ≠ L.ylow[0]?.getD 0 := Ne.symm uJ
  have pUnorm : L.parity ≠ L.ylow[0]?.getD 0 := pU
  have r0mem : L.r0 ∈ L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have p0 : L.parity ≠ L.r0 := fun e => flagAway L hn L.parity (by simp)
    (by simp [e,r0mem])
  have uAway : lowY L ∉ L.r := fun h =>
    (List.nodup_cons.mp (arithmeticND L hw hn)).1 (List.mem_append_left _ h)
  have first : GatePhysical [Instr.CCX J B (lowY L)] := by
    simpa [GatePhysical,PhysicalInstr,ProperGate,lowY] using And.intro (Ne.symm uJ) (Ne.symm uB)
  have cp : GatePhysical (copyRegister (some J) L.r.tail L.y.tail) :=
    copyRegister_physical _ _ _ (copyND L hn) (by
      intro q hq hy
      have eq : J = q := by simpa using hq
      subst q
      exact hJ (data_member L J (by simp [List.mem_of_mem_tail hy])))
  have seeds : GatePhysical [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lowY,Ne.symm p0,p0,pA,Ne.symm aH,
      pD,Ne.symm dU,aE,Ne.symm eU,uD,uE]
  have rot := (rotate_physical L.r (EntryHalf5.target_nodup L hn)).1
  have extend : GatePhysical [Instr.CX (L.r.getD 254 0) L.rmsb] := by
    have h : L.r[254]?.getD 0 ≠ L.rmsb := joint_13_high_copy_ne L hw hn
    simpa [GatePhysical,PhysicalInstr,ProperGate] using h
  have comp := signComplement_physical (lowY L) L.r uAway
  have prep : GatePhysical (prepare L J B) := by
    simpa only [prepare,gatePhysical_append] using
      And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) comp
  have arith : GatePhysical (arithmetic L) := Affine.add_physical _ _ _ _
    (arithmeticND L hw hn) (sources_away L hw hn) (sources_valid L hn)
  have erase : GatePhysical (eraseScalarsAt L J B) := by
    simp [eraseScalarsAt,eraseScalars,GatePhysical,PhysicalInstr,ProperGate,pU,Ne.symm uJ,jU,pUnorm]
  have la : L.lower ∉ L.r := fun h => flagAway L hn L.lower (by simp) (by simp [h])
  have mag : GatePhysical (EntryHalf5.prepareMagnitude L) := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm aH,
      signComplement_physical L.lower L.r la⟩
  have magRev : GatePhysical (EntryHalf5.prepareMagnitude L).reverse := by
    intro i hi
    exact mag i (List.mem_reverse.mp hi)
  have len := BalancedCleanup.widths L.toLayout hw
  have carry : GatePhysical (EntryHalf5.parityCarry L J) :=
    DiagonalCarry5.physical _ _ _ _ _ _ (EntryHalf5.carry_nodup L hn J hJ)
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have x : GatePhysical [Instr.X J] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  have parity : GatePhysical (clearParity L J) := by
    simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gatePhysical_append]
    exact ⟨by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm pU,
      ⟨⟨x,⟨mag,⟨carry,magRev⟩⟩⟩,x⟩⟩
  simpa only [program,prefixProgram,gatePhysical_append] using
    And.intro (And.intro (And.intro prep arith) erase) parity


theorem prepare_slots_le (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (prepare L J B) ≤ 1286 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have rot := (rotate_gateSlots_le L.r).1
  rw [len.2.1] at rot
  have value : gateSlots (prepare L J B) = gateSlots (rotateRight L.r)+518 := by
    simp only [prepare,gateSlots_append,copyRegister_gateSlots,signComplement_gateSlots,
      len.2.1,len.2.2.1,List.length_tail,gateSlots_cons,gateSlots_nil,instructionSlots]
    omega
  rw [value]
  omega

theorem clearParity_slots_le (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (clearParity L J) ≤ 2303 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have mag : gateSlots (EntryHalf5.prepareMagnitude L) = 257 := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,signComplement_gateSlots,len.2.1]
  have carry := DiagonalCarry5.slots_le EntryHalf5.parityBits L.low (L.carry.take 255)
    L.lower J L.parity
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
    (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
  have carry_bound : gateSlots (EntryHalf5.parityCarry L J) ≤ 1786 := by
    simpa only [EntryHalf5.parityCarry,EntryHalf5.parityBits,DiagonalCarry5.literal_length] using carry
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,gateSlots_append,
    reverse_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,mag]
  omega

theorem program_slots_le (L : Layout) (hw : L.Widths) (J B : Wire) :
    gateSlots (program L J B) ≤ 8000 := by
  have prep := prepare_slots_le L hw J B
  have arith := arithmetic_slots L hw
  have parity := clearParity_slots_le L hw J
  have erase : gateSlots (eraseScalarsAt L J B) = 11 := rfl
  simp only [program,prefixProgram,gateSlots_append]
  omega

theorem retSites_omits (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (q : Wire)
    (hq : q ∈ [L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L]) :
    q ∉ retSites L J B := by
  have splitND :
      ([L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L] ++
        [L.parity,L.lower,L.one,L.sign]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro r
    have h := List.nodup_iff_count.mp (EntryHalf5.scalarPortsND L hw hn) r
    simp only [EntryHalf5.scalarPorts,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have flagAway := List.disjoint_left.mp (List.nodup_append'.mp splitND).2.2 hq
  have scalar : q ∈ EntryHalf5.scalarPorts L := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [EntryHalf5.scalarPorts]
  have dataAway := EntryHalf5.scalarAway L hw hn q scalar
  have member : q ∈ L.wires := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · simp [Layout.wires,BalancedCleanup.Layout.wires]
    · exact data_member L (EntryHalf5.lastCarry L) (by simp [EntryHalf5.lastCarry_mem L hw])
  have jAway : q ≠ J := fun eq => hJ (eq ▸ member)
  have bAway : q ≠ B := fun eq => hB (eq ▸ member)
  intro bad
  simp only [retSites,List.mem_toFinset,List.mem_append] at bad
  rcases bad with ((r | y) | c) | flags
  · exact dataAway (by simp [r])
  · exact dataAway (by simp [y])
  · exact dataAway (by simp [c])
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at flags
    rcases flags with rfl | rfl | rfl | rfl | j | b
    all_goals first | exact jAway j | exact bAway b | exact flagAway (by simp)

theorem program_omits (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (q : Wire)
    (hq : q ∈ [L.sourceGuard,L.cout,L.minus,L.plus,EntryHalf5.lastCarry L]) :
    q ∉ wires (program L J B) :=
  fun bad => retSites_omits L hw hn J B hJ hB q hq (program_support L hw J B bad)

end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FrontierEntryJointProgram

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField

def joint (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ EntryRetained5.program L J G ++ [.X G]


theorem joint_counts (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (joint L J G) = 771 ∧ measurementCount (joint L J G) = 514 := by
  have h := EntryRetained5.counts L hw J G
  have tx : toffoliCount [Instr.X G] = 0 := rfl
  have mx : measurementCount [Instr.X G] = 0 := rfl
  simpa only [joint, toffoliCount_append, measurementCount_append,
    tx, mx, Nat.zero_add, Nat.add_zero] using h

theorem joint_slots_le (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    Challenge.gateSlots (joint L J G) ≤ 8002 := by
  have h := EntryRetained5.program_slots_le L hw J G
  have x : Challenge.gateSlots [Instr.X G] = 1 := rfl
  simp only [joint, Challenge.gateSlots_append, x]
  omega

end ECDSAAdd.Entrant.FrontierEntry

end

section
-- Verified component FrontierEntryJointFrame

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField

private theorem joint_15_outside_layout (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem joint_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 Y)
    (hY : regValue L.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (joint L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := joint_15_outside_layout L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (EntryRetained5.program L J G)
    (m.take (measurementCount (EntryRetained5.program L J G))) a=t
  have result := EntryRetained5.program_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (EntryRetained5.program L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (joint L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [joint,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]

end ECDSAAdd.Entrant.FrontierEntry

end

section
-- Verified component DirtyTail
set_option linter.unusedVariables false

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5.AffineDirty
open Arithmetic EntryRetained5 EntryRetained5.Affine
attribute [local irreducible] run
private theorem joint_16_append_run (P Q : Program) (m : List Bool) (s : State) :
 run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
 rw [run_append,run_take]
private theorem joint_16_value_write (b : Bit) (q : Wire) (v : Bool) (s : BasisState) (hq:q∉b.wires) :
 b.value (writeBit s q v)=b.value s := by
 apply Bit.value_congr
 intro x hx
 have ne : x≠q := fun e=>hq (e ▸ hx)
 simp [writeBit,ne]

def two (b d : Bit) (y z cin loan : Wire) : Program :=
 [.CX loan z] ++ majority b y cin loan ++ sum d z loan ++ majority b y cin loan ++ sum b y cin

theorem two_run (b d : Bit) (y z cin loan : Wire) (hb:b.Valid) (hd:d.Valid)
 (hn:[y,z,cin,loan].Nodup)
 (ha:∀q∈b.wires++d.wires,q∉[y,z,cin,loan]) (s:State) (m:List Bool) :
 run (two b d y z cin loan) m s=
 ⟨s.phase,writeBit (writeBit s.basis z
   (sumBit (d.value s.basis) (s.basis z) (carryBit (b.value s.basis) (s.basis y) (s.basis cin))))
   y (sumBit (b.value s.basis) (s.basis y) (s.basis cin))⟩ := by
 have yz:y≠z := by intro e; exact (List.nodup_cons.mp hn).1 (by simp [e])
 have yc:y≠cin := by intro e; exact (List.nodup_cons.mp hn).1 (by simp [e])
 have yl:y≠loan := by intro e; exact (List.nodup_cons.mp hn).1 (by simp [e])
 have zc:z≠cin := by intro e; exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [e])
 have zl:z≠loan := by intro e; exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [e])
 have cl:cin≠loan := by intro e; exact (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1 (by simp [e])
 have nd:[y,cin,loan].Nodup := by simp [List.nodup_cons,yc,yl,cl]
 have ab:∀q∈b.wires,q∉[y,cin,loan] := by
  intro q hq bad; exact ha q (List.mem_append_left _ hq) (by simp only [List.mem_cons,List.mem_singleton] at bad ⊢; tauto)
 have ad:∀q∈d.wires,q≠z := by
  intro q hq e; exact ha q (List.mem_append_right _ hq) (by simp [e])
 have ay:∀q∈b.wires,q≠y := by
  intro q hq e; exact ha q (List.mem_append_left _ hq) (by simp [e])
 have bY (v:BasisState) (t:Bool): b.value (writeBit v y t)=b.value v :=
  joint_16_value_write b y t v (fun h=>ha y (List.mem_append_left _ h) (by simp))
 have bZ (v:BasisState) (t:Bool): b.value (writeBit v z t)=b.value v :=
  joint_16_value_write b z t v (fun h=>ha z (List.mem_append_left _ h) (by simp))
 have bL (v:BasisState) (t:Bool): b.value (writeBit v loan t)=b.value v :=
  joint_16_value_write b loan t v (fun h=>ha loan (List.mem_append_left _ h) (by simp))
 have dZ (v:BasisState) (t:Bool): d.value (writeBit v z t)=d.value v :=
  joint_16_value_write d z t v (fun h=>ha z (List.mem_append_right _ h) (by simp))
 have dL (v:BasisState) (t:Bool): d.value (writeBit v loan t)=d.value v :=
  joint_16_value_write d loan t v (fun h=>ha loan (List.mem_append_right _ h) (by simp))
 have maj(v:State) (n:List Bool): run (majority b y cin loan) n v=
   ⟨v.phase,writeBit v.basis loan (v.basis loan ^^ carryBit (b.value v.basis) (v.basis y) (v.basis cin))⟩ :=
   majority_correct b hb y cin loan nd ab v n
 have ds(v:State) (n:List Bool): run (sum d z loan) n v=
   ⟨v.phase,writeBit v.basis z (sumBit (d.value v.basis) (v.basis z) (v.basis loan))⟩ :=
   sum_correct d z loan zl.symm ad v n
 have bs(v:State) (n:List Bool): run (sum b y cin) n v=
   ⟨v.phase,writeBit v.basis y (sumBit (b.value v.basis) (v.basis y) (v.basis cin))⟩ :=
   sum_correct b y cin yc.symm ay v n
 have cx(v:State) (n:List Bool): run [Instr.CX loan z] n v=
  ⟨v.phase,writeBit v.basis z (v.basis loan ^^ v.basis z)⟩ := by simp [run,Bool.xor_comm]
 simp only [two,joint_16_append_run,cx,maj,ds,bs,bZ,bL,dZ,dL]
 apply congrArg (State.mk s.phase)
 funext q
 by_cases qy:q=y
 · subst q
   simp [writeBit,yz,yc,yl,zc,zl,cl,yz.symm,yc.symm,yl.symm,zc.symm,zl.symm,cl.symm,sumBit,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
 by_cases qz:q=z
 · subst q
   simp [writeBit,qy,yz,yc,yl,zc,zl,cl,yz.symm,yc.symm,yl.symm,zc.symm,zl.symm,cl.symm,sumBit,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
 by_cases ql:q=loan
 · subst q
   simp [writeBit,qy,qz,yz,yc,yl,zc,zl,cl,yz.symm,yc.symm,yl.symm,zc.symm,zl.symm,cl.symm,sumBit,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
 simp [writeBit,qy,qz,ql]

theorem two_equals_old (b d : Bit) (y z cin loan last : Wire) (hb:b.Valid) (hd:d.Valid)
 (hn:[loan,y,z,cin,last].Nodup)
 (ha:∀q∈b.wires++d.wires,q∉[loan,y,z,cin,last]) (s:State) (m n:List Bool)
 (clean:s.basis last=false) :
 run (two b d y z cin loan) m s=run (add [b,d] [y,z] [last] cin) n s := by
 have cnt:=List.nodup_iff_count.mp hn
 have nd:[y,z,cin,loan].Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h:=cnt q
  simp only [List.count_cons,List.count_nil] at h ⊢; omega
 have ndold:(cin::([y,z]++[last])).Nodup := by
  apply List.nodup_iff_count.mpr; intro q; have h:=cnt q
  simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢; omega
 have src:∀q∈sites [b,d],q∉cin::([y,z]++[last]) := by
  intro q hq bad
  have member:q∈b.wires++d.wires := by simpa [sites] using hq
  exact ha q member (by simp only [List.mem_cons,List.mem_append,List.mem_singleton] at bad ⊢;tauto)
 have srcnew:∀q∈b.wires++d.wires,q∉[y,z,cin,loan] := by
  intro q hq bad
  exact ha q hq (by simp only [List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
 have old:=add_correct [b,d] [y,z] [last] cin ndold src (by rfl) (by rfl) s n
   (by intro q hq;simpa using (List.mem_singleton.mp hq) ▸ clean)
   (by intro q hq;simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;rcases hq with rfl|rfl;exact hb;exact hd)
 have ne:y≠z := by intro e;exact (List.nodup_cons.mp nd).1 (by simp [e])
 have eq:=two_run b d y z cin loan hb hd nd srcnew s m
 have val:regValue [y,z] (run (two b d y z cin loan) m s).basis=
   (value [b,d] s.basis+regValue [y,z] s.basis+(s.basis cin).toNat)%2^([y,z]:List Wire).length := by
  rw [eq]
  cases bav:b.value s.basis <;> cases dav:d.value s.basis <;>
    cases yy:s.basis y <;> cases zz:s.basis z <;> cases cc:s.basis cin <;>
    simp [value,regValue,writeBit,ne,ne.symm,bav,dav,yy,zz,cc,sumBit,carryBit]
 apply State.extensionality
 · rw [eq];exact old.1.symm
 · funext q
   by_cases hq:q∈[y,z]
   · exact (regValue_eq_iff [y,z] _ _).mp (val.trans old.2.2.symm) q hq
   · have both:q≠y ∧ q≠z := by simpa using hq
     have ny:=both.1
     have nz:=both.2
     rw [eq]
     simpa [writeBit,ny,nz] using (old.2.1 q hq).symm
end ECDSAAdd.Entrant.EntryRetained5.AffineDirty

end

section
-- Verified component DirtyPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.EntryRetained5.AffineDirty
open Arithmetic EntryRetained5 EntryRetained5.Affine
attribute [local irreducible] run
private theorem joint_17_append_run (P Q : Program) (m : List Bool)  (s : State) :
 run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
 rw [run_append,run_take]

def addPrefix : List Bit → List Wire → List Wire → Bit → Bit → Wire → Wire → Wire → Wire → Program
 | [],_,_,a,d,t,z,cin,loan => two a d t z cin loan
 | b::bs,y::ys,k::ks,a,d,t,z,cin,loan =>
   majority b y cin k++addPrefix bs ys ks a d t z k loan++erase b y cin k++sum b y cin
 | _,_,_,_,_,_,_,_,_ => []

theorem prefix_counts (bs:List Bit)  (ys cs:List Wire)  (a d:Bit)  (t z cin loan:Wire) 
 (hy:ys.length=bs.length) (hc:cs.length=bs.length) :
 toffoliCount (addPrefix bs ys cs a d t z cin loan)=bs.length+2 ∧
 measurementCount (addPrefix bs ys cs a d t z cin loan)=bs.length := by
 induction bs generalizing ys cs cin with
 | nil =>
   have aC:=bit_counts a t cin loan
   have dC:=bit_counts d z loan loan
   simp only [addPrefix,two,toffoliCount_append,measurementCount_append,
    aC.1,aC.2.1,aC.2.2.2.2.1,aC.2.2.2.2.2,dC.2.2.2.2.1,dC.2.2.2.2.2,
    toffoliCount,measurementCount]
   decide
 | cons b bs ih =>
   cases ys with
   | nil => simp at hy
   | cons y ys =>
     cases cs with
     | nil => simp at hc
     | cons k ks =>
       have h:=ih ys ks k (by simpa using hy) (by simpa using hc)
       have m:=bit_counts b y cin k
       simp only [addPrefix,toffoliCount_append,measurementCount_append,m.1,m.2.1,m.2.2.1,
         m.2.2.2.1,m.2.2.2.2.1,m.2.2.2.2.2,h.1,h.2,List.length_cons]
       omega

theorem shifted (bs:List Bit)  (ys cs:List Wire)  (a d:Bit)  (t z last cin loan:Wire) 
 (hy:ys.length=bs.length) (hc:cs.length=bs.length)
 (hn:(loan::cin::(ys++[t,z]++cs++[last])).Nodup)
 (hs:∀q∈sites (bs++[a,d]),q∉loan::cin::(ys++[t,z]++cs++[last]))
 (hv:∀b∈bs++[a,d],b.Valid)
 (s:State) (m:List Bool)  (clean:∀q∈cs++[last],s.basis q=false) :
 run (add (bs++[a,d]) (ys++[t,z]) (cs++[last]) cin) (false::m) s=
 run (addPrefix bs ys cs a d t z cin loan) m s := by
 induction bs generalizing ys cs cin s m with
 | nil =>
   have ye:ys=[]:=List.eq_nil_of_length_eq_zero hy
   have ce:cs=[]:=List.eq_nil_of_length_eq_zero hc
   subst ys;subst cs
   have nd:[loan,t,z,cin,last].Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h:=List.nodup_iff_count.mp hn q
    simp only [List.nil_append,List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
   have src:∀q∈a.wires++d.wires,q∉[loan,t,z,cin,last] := by
    intro q hq bad
    exact hs q (by simpa [sites] using hq)
      (by simpa [or_comm,or_left_comm,or_assoc] using bad)
   have eq:=two_equals_old a d t z cin loan last (hv a (by simp)) (hv d (by simp))
     nd src s m (false::m) (clean last (by simp))
   simpa only [List.nil_append,addPrefix] using eq.symm
 | cons b bs ih =>
   cases ys with
   | nil => simp at hy
   | cons y ys =>
     cases cs with
     | nil => simp at hc
     | cons k ks =>
       have hy':ys.length=bs.length:=by simpa using hy
       have hc':ks.length=bs.length:=by simpa using hc
       have cnt:=List.nodup_iff_count.mp hn
       have nd:[y,cin,k].Nodup := by
        apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
        simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
       have nd':(loan::k::(ys++[t,z]++ks++[last])).Nodup := by
        apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
        simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
       have src:∀q∈b.wires,q∉[y,cin,k] := by
        intro q hq bad
        exact hs q (head_mem b (bs++[a,d]) q hq)
          (by simp only [List.mem_cons,List.mem_append,List.mem_singleton] at bad ⊢;tauto)
       have src':∀q∈sites (bs++[a,d]),q∉loan::k::(ys++[t,z]++ks++[last]) := by
        intro q hq bad
        exact hs q (tail_mem b (bs++[a,d]) q hq)
          (by simp only [List.mem_cons,List.mem_append,List.mem_singleton] at bad ⊢;tauto)
       have away(q:Wire)  (hq:q∈ks++[last]):q≠k := by
        have pos:=List.count_pos_iff.mpr hq
        have h:=cnt q
        intro e;subst q
        simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at pos h
        omega
       let mid:=run (majority b y cin k) m s
       have mid_eq:=majority_correct b (hv b (by simp)) y cin k nd src s m
       have same:run (majority b y cin k) (false::m) s=mid := by
        rw [majority_correct b (hv b (by simp)) y cin k nd src s (false::m)]
        exact mid_eq.symm
       have clean':∀q∈ks++[last],mid.basis q=false := by
        intro q hq
        rw [show mid=run (majority b y cin k) m s from rfl,mid_eq]
        simpa [writeBit,away q hq] using clean q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto)
       have ih':=ih ys ks k hy' hc' nd' src'
         (by intro v hv';exact hv v (List.mem_cons_of_mem _ hv')) mid m clean'
       have oldM:measurementCount (add (bs++[a,d]) (ys++[t,z]) (ks++[last]) k)=bs.length+1 := by
        have h:=(add_counts (bs++[a,d]) (ys++[t,z]) (ks++[last]) k
          (by simp [hy']) (by simp [hy',hc'])).2
        simpa [hy'] using h
       have newM:measurementCount (addPrefix bs ys ks a d t z k loan)=bs.length :=
        (prefix_counts bs ys ks a d t z k loan hy' hc').2
       have shape:add ((b::bs)++[a,d]) ((y::ys)++[t,z]) ((k::ks)++[last]) cin=
        majority b y cin k++add (bs++[a,d]) (ys++[t,z]) (ks++[last]) k++erase b y cin k++sum b y cin := by
        cases bs <;> cases ys <;> rfl
       rw [shape]
       simp only [addPrefix,joint_17_append_run,measurementCount_append]
       have majM:measurementCount (majority b y cin k)=0:=(bit_counts b y cin k).2.1
       simp only [majM,Nat.zero_add,List.drop_zero,oldM,newM,List.drop_succ_cons]
       rw [same,ih']
       have eraseM:measurementCount (erase b y cin k)=1 := (bit_counts b y cin k).2.2.2.1
       simp only [eraseM,List.drop_succ_cons]
       rfl

theorem record_independent (bits : List Bit)  (ys carry : List Wire)  (cin : Wire) 
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m n : List Bool)  (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    run (add bits ys carry cin) m s=run (add bits ys carry cin) n s := by
  have a:=add_correct bits ys carry cin hn hs hl hc s m hclean hvalid
  have b:=add_correct bits ys carry cin hn hs hl hc s n hclean hvalid
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq:q∈ys
    · exact (regValue_eq_iff ys _ _).mp (a.2.2.trans b.2.2.symm) q hq
    · exact (a.2.1 q hq).trans (b.2.1 q hq).symm

theorem same_records (bs:List Bit)  (ys cs:List Wire)  (a d:Bit)  (t z last cin loan:Wire) 
 (hy:ys.length=bs.length) (hc:cs.length=bs.length)
 (hn:(loan::cin::(ys++[t,z]++cs++[last])).Nodup)
 (hs:∀q∈sites (bs++[a,d]),q∉loan::cin::(ys++[t,z]++cs++[last]))
 (hv:∀b∈bs++[a,d],b.Valid)
 (s:State) (m:List Bool)  (clean:∀q∈cs++[last],s.basis q=false) :
 run (add (bs++[a,d]) (ys++[t,z]) (cs++[last]) cin) m s=
 run (addPrefix bs ys cs a d t z cin loan) m s := by
 have nd:(cin::((ys++[t,z])++(cs++[last]))).Nodup := by
  simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
 have src:∀q∈sites (bs++[a,d]),q∉cin::((ys++[t,z])++(cs++[last])) := by
  intro q hq bad;exact hs q hq (by simpa only [List.append_assoc] using List.mem_cons_of_mem loan bad)
 have eq:=record_independent (bs++[a,d]) (ys++[t,z]) (cs++[last]) cin nd src
   (by simp [hy]) (by simp [hy,hc]) s m (false::m) clean hv
 exact eq.trans (shifted bs ys cs a d t z last cin loan hy hc hn hs hv s m clean)
end ECDSAAdd.Entrant.EntryRetained5.AffineDirty

end

section
-- Verified component JointArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum EntryRetained5
attribute [local irreducible] run wires
abbrev ports : BalancedCircuit.Layout := OneBankCell5.ports base (base 2409)
def bits : List Affine.Bit := (List.range 254).map (source ports)
def targets : List Wire := wireBlock base 2056 254
def carries : List Wire := wireBlock base 512 253++[base 1540]
def arithmetic : Program := AffineDirty.addPrefix bits targets carries
 (source ports 254) (source ports 255) (base 2310) (base 2311) (lowY ports) (base 0)
theorem sources_split : sources ports=bits++[source ports 254,source ports 255] := by rfl
theorem target_split : ports.r=targets++[base 2310,base 2311] := by
 rw [OneBankCell5.ports_r,balancedSharedPorts_r]
 change wireBlock base 2056 (254+2)=wireBlock base 2056 254++[base 2310,base 2311]
 rw [←wireBlock_append]
 rfl
theorem carry_split : ports.carry.take 255=carries++[base 1541] := by rfl

theorem ports_nodup : ports.wires.Nodup :=
 OneBankCell5.ports_nodup_injective base (base 2409) base_injective (by decide +kernel)
theorem widths : ports.Widths := OneBankCell5.ports_widths base (base 2409)

theorem arithmetic_layout :
 (base 0::lowY ports::(targets++[base 2310,base 2311]++carries++[base 1541])).Nodup ∧
 (∀q∈Affine.sites (bits++[source ports 254,source ports 255]),
   q∉base 0::lowY ports::(targets++[base 2310,base 2311]++carries++[base 1541])) ∧
 (∀b∈bits++[source ports 254,source ports 255],b.Valid) := by
 have ndOld:=arithmeticND ports widths ports_nodup
 have hn:(base 0::lowY ports::(targets++[base 2310,base 2311]++carries++[base 1541])).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · decide +kernel
  · rw [target_split,carry_split] at ndOld
    simpa only [List.append_assoc] using ndOld
 have src:∀q∈Affine.sites (bits++[source ports 254,source ports 255]),
   q∉base 0::lowY ports::(targets++[base 2310,base 2311]++carries++[base 1541]) := by
  intro q hq bad
  have oldsrc:=sources_away ports widths ports_nodup
  have used:q∈Affine.sites (sources ports) := by rwa [sources_split]
  rcases List.mem_cons.mp bad with eq|mem
  · subst q
    have member:=sources_sites ports (base 0) used
    exact (by decide +kernel : base 0∉[ports.parity,ports.lower,ports.one,ports.sign]) member
  · exact oldsrc q used (by rwa [target_split,carry_split,List.append_assoc])
 have hv:∀b∈bits++[source ports 254,source ports 255],b.Valid := by
  intro b hb;exact sources_valid ports ports_nodup b (by rwa [sources_split])
 exact ⟨hn,src,hv⟩

theorem arithmetic_eq (s:State) (m:List Bool) (clean:∀q∈ports.carry,s.basis q=false) :
 run arithmetic m s=run (EntryRetained5.arithmetic ports) m s := by
 obtain ⟨hn,src,hv⟩:=arithmetic_layout
 have cl:∀q∈carries++[base 1541],s.basis q=false := by
  intro q hq;exact clean q (List.mem_of_mem_take (carry_split ▸ hq))
 have eq:=AffineDirty.same_records bits targets carries (source ports 254) (source ports 255)
   (base 2310) (base 2311) (base 1541) (lowY ports) (base 0)
   (by rfl) (by rfl) hn src hv s m cl
 simpa only [EntryRetained5.arithmetic,sources_split,target_split,carry_split,arithmetic] using eq.symm

theorem arithmetic_counts : toffoliCount arithmetic=256 ∧ measurementCount arithmetic=254 := by
 exact AffineDirty.prefix_counts bits targets carries _ _ _ _ _ _ (by rfl) (by rfl)
end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component ParityLoan
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField Challenge Baselines
attribute [local irreducible] run wires

def parityLoan (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (L.carry.getD 254 0) L.sign) (clearParity L J)

theorem parityLoan_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (Jv Bv : Bool) (Y : Int) (hy : Centered Y)
    (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity=originalParity Y)
    (hU : s.basis (L.ylow.getD 0 0)=(Jv && originalParity Y))
    (hS : s.basis J=Jv) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hz : s.basis L.sign=false) :
    run (parityLoan L J) m s=run (clearParity L J) m s := by
  have ha : L.carry.getD 254 0∈L.carry := by
    rw [List.getD_eq_getElem _ _ (by have h:=hw.2.2;omega)]
    exact List.getElem_mem _
  have away:=flagAway L hn L.parity (by simp)
  have ap : L.carry.getD 254 0≠L.parity := by
    intro eq
    have bad : L.parity∈L.carry := eq ▸ ha
    exact away (List.mem_append_right (L.r++L.y) bad)
  have sp : L.sign≠L.parity := by
    have nd:=scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
    tauto
  have eq:=clearParity_run L hw hn J hJ Jv Bv Y hy s m hR hP hU hS hl hc
  apply FieldFrameOB5.rebind_swap_run
  · exact hc _ ha
  · exact hz
  · rw [eq]
    change Function.update s.basis L.parity false (L.carry.getD 254 0)=false
    rw [Function.update_of_ne ap]
    exact hc _ ha
  · rw [eq]
    change Function.update s.basis L.parity false L.sign=false
    rw [Function.update_of_ne sp]
    exact hz

theorem parityLoan_counts (L : Layout) (hw : L.Widths) (J : Wire) :
    toffoliCount (parityLoan L J)=256 ∧ measurementCount (parityLoan L J)=255 := by
  have a:=renameProgram_counts (Equiv.swap (L.carry.getD 254 0) L.sign) (clearParity L J)
  have b:=clearParity_counts L hw J
  exact ⟨a.1.trans b.1,a.2.trans b.2⟩

theorem parityLoan_slots (L : Layout) (hw : L.Widths) (J : Wire) :
    gateSlots (parityLoan L J)≤2303 := by
  rw [parityLoan,rename_gateSlots]
  exact clearParity_slots_le L hw J

theorem parityLoan_physical (L : Layout) (J : Wire)
    (hp : GatePhysical (clearParity L J)) : GatePhysical (parityLoan L J) :=
  gatePhysical_rename _ (Equiv.swap _ _).injective _ hp

theorem parityLoan_support_image (L : Layout) (J : Wire) :
    wires (parityLoan L J)=(wires (clearParity L J)).image (Equiv.swap (L.carry.getD 254 0) L.sign) :=
  renameProgram_support _ _

theorem clearParity_free_sign (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) : L.sign∉wires (clearParity L J) := by
  have away:=flagAway L hn L.sign (by simp)
  have ar : L.sign∉L.r := fun h=>away (by simp only [List.mem_append];exact Or.inl (Or.inl h))
  have ay : L.sign∉L.y := fun h=>away (by simp only [List.mem_append];exact Or.inl (Or.inr h))
  have ac : L.sign∉L.carry := fun h=>away (List.mem_append_right _ h)
  have nd:=scalarND L hn
  have sp : L.sign≠L.parity := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd;tauto
  have sl : L.sign≠L.lower := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd;tauto
  have sj : L.sign≠J := by
    intro eq
    exact hJ (eq ▸ (by simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]))
  have rmsb : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have sr : L.sign≠L.rmsb := fun e=>ar (e ▸ rmsb)
  have y0 : L.ylow.getD 0 0∈L.y := by
    have len:=hw.2.1
    have mem : L.ylow.getD 0 0∈L.ylow := by
      rw [List.getD_eq_getElem _ _ (by omega)];exact List.getElem_mem _
    simpa only [BalancedCleanup.Layout.y,List.mem_append,List.mem_singleton] using
      Or.inl mem
  have sy0 : L.sign≠L.ylow.getD 0 0 := fun e=>ay (e ▸ y0)
  have mag : L.sign∉wires (EntryHalf5.prepareMagnitude L) := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,
      Finset.mem_union,not_or]
    constructor
    · simpa [wires,Instr.wires] using And.intro sr sl
    · intro used
      have h:=signComplement_wires_subset L.lower L.r used
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
      exact h.elim sl ar
  have len:=BalancedCleanup.widths L.toLayout hw
  have ch : L.sign∉wires (EntryHalf5.parityCarry L J) := by
    intro used
    have ss:=DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])
    have h:=List.mem_toFinset.mp (ss used)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h
    · exact sj h
    · exact sp h
    · exact sl h
    · exact ar (List.mem_append_left _ h)
    · exact ac (List.mem_of_mem_take h)
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,
    wires_append,wires_reverse,Finset.mem_union,not_or]
  refine ⟨?_,⟨⟨?_,⟨mag,⟨ch,mag⟩⟩⟩,?_⟩⟩
  · simpa [wires,Instr.wires] using And.intro sy0 sp
  · simpa [wires,Instr.wires] using sj
  · simpa [wires,Instr.wires] using sj

theorem parityLoan_omits_old (L : Layout) (J : Wire)
    (free : L.sign∉wires (clearParity L J)) :
    L.carry.getD 254 0∉wires (parityLoan L J) := by
  rw [parityLoan_support_image]
  intro h
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp h
  have back:=congrArg (Equiv.swap (L.carry.getD 254 0) L.sign) eq
  have same : q=L.sign := by simpa using back
  exact free (same ▸ hq)
theorem parityLoan_retired (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) : L.carry.getD 254 0∉wires (parityLoan L J) :=
  parityLoan_omits_old L J (clearParity_free_sign L hw hn J hJ)
end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component FinishLoan
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] run
private theorem joint_20_source_head_member (L : Layout) (hw : L.Widths) :
    L.ylow.getD 0 0 ∈ L.y := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as => simp [BalancedCleanup.Layout.y, hy]

private theorem joint_20_source_head_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.ylow.getD 0 0 ∉ L.r ++ L.carry := by
  have nd : (L.r ++ (L.y ++ L.carry)).Nodup := by
    simpa only [List.append_assoc] using (List.nodup_append'.mp (allND L hn)).2.1
  have rsep := (List.nodup_append'.mp nd).2.2
  have ysep := (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.2
  intro h
  rcases List.mem_append.mp h with hr | hc
  · exact List.disjoint_left.mp rsep hr (List.mem_append_left _ (joint_20_source_head_member L hw))
  · exact List.disjoint_left.mp ysep (joint_20_source_head_member L hw) hc

private theorem joint_20_erased_data_keep (L : Layout) (hn : L.wires.Nodup)
    (J : Wire) (s : BasisState) (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
    (hu : q ≠ L.ylow.getD 0 0) :
    erasedBasis L.parity L.lower L.one L.sign (L.ylow.getD 0 0) J s q = s q := by
  have away (v : Wire) (hv : v ∈ [L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q ≠ v := fun e => flagAway L hn v hv (e ▸ hq)
  simp only [erasedBasis, writeBit, Function.update_of_ne hu,
    Function.update_of_ne (away L.one (by simp)),
    Function.update_of_ne (away L.lower (by simp)),
    Function.update_of_ne (away L.sign (by simp))]

theorem finishLoan_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false) :
    run (eraseScalarsAt L J B ++ parityLoan L J) m s =
      ⟨s.phase, writeBit (erasedBasis L.parity L.lower L.one L.sign
        (L.ylow.getD 0 0) J s.basis) L.parity false⟩ := by
  let t : State := ⟨s.phase, erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis⟩
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have ha := scalar_erase_relation L hw Jv Bv Y hy s.basis hR hP hA
    (by simpa only [hP,hU,hJv,hBv] using hD)
  have erase := eraseScalarsAt_run L hw hn J B hJ hB hJB s
    (m.take (measurementCount (eraseScalarsAt L J B))) hE ha hD hU
  have keep (q : Wire) (hq : q ∈ L.r ++ L.carry) : t.basis q = s.basis q := by
    apply joint_20_erased_data_keep L hn J s.basis q
    · rcases List.mem_append.mp hq with hr | hc
      · exact List.mem_append_left _ (List.mem_append_left _ hr)
      · exact List.mem_append_right _ hc
    · exact fun e => joint_20_source_head_away L hw hn (e ▸ hq)
  have tr : regValue L.r t.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (List.mem_append_left _ hq))).trans hR
  have tp : t.basis L.parity = originalParity Y := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne pU,
      Function.update_of_ne pD,Function.update_of_ne pA,Function.update_of_ne pE] using hP
  have tu : t.basis (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [t,erasedBasis,writeBit,Function.update_self,hJv,hP]
  have tj : t.basis J = Jv := by
    simpa only [t,erasedBasis,writeBit,Function.update_of_ne (Ne.symm uJ),
      Function.update_of_ne (Ne.symm dJ),Function.update_of_ne (Ne.symm aJ),
      Function.update_of_ne (Ne.symm eJ)] using hJv
  have ta : t.basis L.lower = false := by
    simp only [t,erasedBasis,writeBit,Function.update_of_ne aU,
      Function.update_of_ne aD,Function.update_self]
  have tc (q : Wire) (hq : q ∈ L.carry) : t.basis q = false :=
    (keep q (List.mem_append_right _ hq)).trans (hc q hq)
  have parity := clearParity_run L hw hn J hJ Jv Bv Y hy t
    (m.drop (measurementCount (eraseScalarsAt L J B))) tr tp tu tj ta tc
  have tz : t.basis L.sign=false := by
    simp only [t,erasedBasis,writeBit,Function.update_of_ne eU,
      Function.update_of_ne (Ne.symm dE),Function.update_of_ne (Ne.symm aE),Function.update_self]
  have rebound:=parityLoan_eq L hw hn J hJ Jv Bv Y hy t
    (m.drop (measurementCount (eraseScalarsAt L J B))) tr tp tu tj ta tc tz
  rw [run_append, erase,rebound]
  exact parity

private theorem joint_20_source_high_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q ∈ L.ylow.drop 1 ++ [L.ymsb]) :
    q ∈ L.y ∧ q ≠ L.ylow.getD 0 0 := by
  have nd := (List.nodup_append'.mp (allND L hn)).2.1
  have ny : L.y.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  cases hy : L.ylow with
  | nil => have h := hw.2.1; simp [hy] at h
  | cons a as =>
    have tail : q ∈ as ++ [L.ymsb] := by simpa only [hy, List.drop_succ_cons, List.drop_zero] using hq
    have na : a ∉ as ++ [L.ymsb] := by
      have yn : (a :: (as ++ [L.ymsb])).Nodup := by
        simpa only [BalancedCleanup.Layout.y, hy, List.cons_append] using ny
      exact (List.nodup_cons.mp yn).1
    exact ⟨by simp [BalancedCleanup.Layout.y,hy,tail], by
      simpa only [hy,List.getD_cons_zero] using (fun e => na (e ▸ tail) : q ≠ a)⟩

/-- Close the two-word frame after the arithmetic prefix. Only its four live
scalar products are excluded from the prefix's outside-bit frame. -/
theorem finishLoan_pair_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J ∉ L.wires) (hB : B ∉ L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (before s : State) (m : List Bool)
    (phase : s.phase = before.phase)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hYS : regValue L.y s.basis = (Jv && Bv).toNat +
      2*(if Jv then encodeWord 256 Y / 2 else 0))
    (hP : s.basis L.parity = originalParity Y)
    (hA : s.basis L.lower = (originalParity Y && negative Y))
    (hD : s.basis L.one = (s.basis L.parity && s.basis (L.ylow.getD 0 0)))
    (hE : s.basis L.sign = (s.basis L.lower && s.basis (L.ylow.getD 0 0)))
    (hU : s.basis (L.ylow.getD 0 0) = (s.basis J && s.basis B))
    (hJv : s.basis J = Jv) (hBv : s.basis B = Bv)
    (hc : ∀ q ∈ L.carry, s.basis q = false)
    (clean : ∀ q ∈ [L.parity,L.lower,L.one,L.sign], before.basis q = false)
    (outside : ∀ q, q ∉ L.r → q ∉ L.y → q ≠ L.parity → q ≠ L.lower →
      q ≠ L.one → q ≠ L.sign → s.basis q = before.basis q) :
    let out := run (eraseScalarsAt L J B ++ parityLoan L J) m s
    out.phase = before.phase ∧ PairFrame L.r L.y before.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let bits := writeBit (erasedBasis L.parity L.lower L.one L.sign
    (L.ylow.getD 0 0) J s.basis) L.parity false
  have result := finishLoan_run L hw hn J B hJ hB hJB Jv Bv Y hy s m hR hP hA hD hE hU hJv hBv hc
  have nd := erasePorts_nodup L hw hn J B hJ hB hJB
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
    ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
  have data_keep (q : Wire) (hq : q ∈ L.r ++ L.y ++ L.carry)
      (hu : q ≠ L.ylow.getD 0 0) : bits q = s.basis q := by
    have qp : q ≠ L.parity := fun e => flagAway L hn _ (by simp) (e ▸ hq)
    simpa only [bits,writeBit,Function.update_of_ne qp] using joint_20_erased_data_keep L hn J s.basis q hq hu
  have rkeep (q : Wire) (hq : q ∈ L.r) : bits q = s.basis q := by
    apply data_keep q (List.mem_append_left _ (List.mem_append_left _ hq))
    exact fun e => joint_20_source_head_away L hw hn (e ▸ List.mem_append_left _ hq)
  have low : bits (L.ylow.getD 0 0) = (Jv && originalParity Y) := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pU),
      Function.update_self,hJv,hP]
  have high : regValue (L.ylow.drop 1 ++ [L.ymsb]) bits =
      if Jv then encodeWord 256 Y / 2 else 0 := by
    have old := pending_source_high L hw s.basis (Jv && Bv)
      (if Jv then encodeWord 256 Y / 2 else 0) (by rw [hU,hJv,hBv]) hYS
    apply Eq.trans (regValue_congr _ _ _ ?_) old
    intro q hq
    have away := joint_20_source_high_away L hw hn q hq
    exact data_keep q (List.mem_append_left _ (List.mem_append_right _ away.1)) away.2
  have source := source_frame_of_parts L hw bits Jv Y hy low high
  dsimp only
  rw [result]
  refine ⟨phase, (regValue_congr _ _ _ rkeep).trans hR, source, ?_⟩
  intro q hr hys
  change bits q = before.basis q
  by_cases qp : q = L.parity
  · subst q
    simp only [bits,writeBit,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qa : q = L.lower
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pA),
      Function.update_of_ne aU,Function.update_of_ne aD,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qd : q = L.one
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pD),
      Function.update_of_ne dU,Function.update_self]
    exact (clean _ (by simp)).symm
  by_cases qe : q = L.sign
  · subst q
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne (Ne.symm pE),
      Function.update_of_ne eU,Function.update_of_ne (Ne.symm dE),
      Function.update_of_ne (Ne.symm aE),Function.update_self]
    exact (clean _ (by simp)).symm
  have qu : q ≠ L.ylow.getD 0 0 := fun e => hys (e ▸ joint_20_source_head_member L hw)
  have same : bits q = s.basis q := by
    simp only [bits,erasedBasis,writeBit,Function.update_of_ne qp,Function.update_of_ne qu,
      Function.update_of_ne qd,Function.update_of_ne qa,Function.update_of_ne qe]
  exact same.trans (outside q hr hys qp qa qd qe)


end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component JointProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum EntryRetained5
attribute [local irreducible] run
private theorem joint_21_append_run (P Q : Program) (m : List Bool) (s : State) :
 run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
 rw [run_append,run_take]
def prefixProgram (J B:Wire) : Program := prepare ports J B++arithmetic
def program (J B:Wire) : Program := prefixProgram J B++eraseScalarsAt ports J B++parityLoan ports J

theorem prefix_spec (J B : Wire) (hJ : J∉ports.wires) (hB : B∉ports.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue ports.r s.basis=encodeWord 256 Y) (hY : regValue ports.y s.basis=0)
    (hc : ∀q∈work ports,s.basis q=false) (hz : s.basis ports.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    PrefixResult ports J B Jv Bv Y s (run (prefixProgram J B) m s) := by
  have prep:=prepare_spec ports widths ports_nodup J B hJ hB hJB Jv Bv Y hy s m hR hY hc hz hj hb
  have ar:=arithmetic_eq (run (prepare ports J B) m s) m prep.carry
  have old:=EntryRetained5.prefix_spec ports widths ports_nodup J B hJ hB hJB Jv Bv Y hy s m hR hY hc hz hj hb
  have pm: measurementCount (prepare ports J B)=0:=(prepare_counts ports widths J B).2
  have eq:run (prefixProgram J B) m s=run (EntryRetained5.prefixProgram ports J B) m s := by
    simp only [prefixProgram,EntryRetained5.prefixProgram,joint_21_append_run,pm,List.drop_zero]
    exact ar
  rw [eq]
  exact old
theorem program_frame
    (J B : Wire) (hJ : J ∉ ports.wires) (hB : B ∉ ports.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue ports.r s.basis = encodeWord 256 Y) (hY : regValue ports.y s.basis = 0)
    (hclean : ∀ q ∈ BalancedCircuit.work ports, s.basis q = false)
    (hSign : s.basis ports.sign = false) (hJv : s.basis J = Jv) (hBv : s.basis B = Bv) :
    let out := run (program J B) m s
    out.phase = s.phase ∧ PairFrame ports.r ports.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  let t := run (prefixProgram J B) (m.take (measurementCount (prefixProgram J B))) s
  have result := prefix_spec J B hJ hB hJB Jv Bv Y hy s
    (m.take (measurementCount (prefixProgram J B))) hR hY hclean hSign hJv hBv
  change PrefixResult ports J B Jv Bv Y s t at result
  have clean (q : Wire) (hq : q ∈ [ports.parity,ports.lower,ports.one,ports.sign]) : s.basis q = false := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hclean _ (by simp [BalancedCircuit.work])
    · exact hSign
  have d : t.basis ports.one = (t.basis ports.parity && t.basis (ports.ylow.getD 0 0)) := by
    simpa only [result.parity,show t.basis (ports.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.d
  have e : t.basis ports.sign = (t.basis ports.lower && t.basis (ports.ylow.getD 0 0)) := by
    simpa only [result.a,show t.basis (ports.ylow.getD 0 0) = (Jv && Bv) from result.u] using result.e
  have u : t.basis (ports.ylow.getD 0 0) = (t.basis J && t.basis B) := by
    rw [result.j,result.b]
    exact result.u
  have outside (q : Wire) (hr : q ∉ ports.r) (hy : q ∉ ports.y) (qp : q ≠ ports.parity)
      (qa : q ≠ ports.lower) (qd : q ≠ ports.one) (qe : q ≠ ports.sign) : t.basis q = s.basis q :=
    result.outside q (by simp [hr,hy,qp,qa,qd,qe])
  have finish := finishLoan_pair_frame ports widths ports_nodup J B hJ hB hJB Jv Bv Y hy s t
    (m.drop (measurementCount (prefixProgram J B))) result.phase result.target result.source
    result.parity result.a d e u result.j result.b result.carry clean outside
  dsimp only
  rw [program,List.append_assoc,run_append]
  exact finish

end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component JointFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField
attribute [local irreducible] program prefixProgram arithmetic
def joint (J G:Wire) : Program := [.X G]++program J G++[.X G]
private theorem joint_22_outside_layout (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem joint_frame
    (J G : Wire) (hJ : J ∉ ports.wires) (hG : G ∉ ports.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue ports.r s.basis = encodeWord 256 Y)
    (hY : regValue ports.y s.basis = 0)
    (clean : ∀q∈BalancedCircuit.work ports,s.basis q=false)
    (sign : s.basis ports.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (joint J G) m s
    out.phase=s.phase ∧ PairFrame ports.r ports.y s.basis
      (encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := joint_22_outside_layout ports G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue ports.r a.basis=encodeWord 256 Y :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue ports.y a.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work ports,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : ports.sign∈ports.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : ports.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (program J G)
    (m.take (measurementCount (program J G))) a=t
  have result := program_frame J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (program J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (joint J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [joint,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]


end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component DirtyResources

set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5.AffineDirty
open Arithmetic Challenge RecordedQuantum EntryRetained5 EntryRetained5.Affine
attribute [local irreducible] wires

theorem two_support (a d:Bit) (t z cin loan:Wire) (W:Finset Wire)
 (hs:∀q∈a.wires++d.wires,q∈W) (ht:t∈W) (hz:z∈W) (hc:cin∈W) (hl:loan∈W) :
 wires (two a d t z cin loan)⊆W := by
 have aC:=local_support a t cin loan W (fun q h=>hs q (List.mem_append_left _ h)) ht hc hl
 have dC:=local_support d z loan loan W (fun q h=>hs q (List.mem_append_right _ h)) hz hl hl
 have cx:wires [Instr.CX loan z]⊆W := by simp [wires,Instr.wires,Finset.insert_subset_iff,hl,hz]
 simpa only [two,wires_append,Finset.union_subset_iff] using ⟨⟨⟨⟨cx,aC.1⟩,dC.2.2⟩,aC.1⟩,aC.2.2⟩

theorem prefix_support (bs:List Bit) (ys cs:List Wire) (a d:Bit) (t z cin loan:Wire) (W:Finset Wire)
 (hs:∀q∈sites (bs++[a,d]),q∈W) (ht:∀q∈ys++[t,z]++cs++[cin,loan],q∈W) :
 wires (addPrefix bs ys cs a d t z cin loan)⊆W := by
 induction bs generalizing ys cs cin with
 | nil =>
   apply two_support
   · intro q hq;exact hs q (by simpa [sites] using hq)
   all_goals apply ht; simp
 | cons b bs ih =>
   cases ys with
   | nil => simp [addPrefix,wires]
   | cons y ys =>
     cases cs with
     | nil => simp [addPrefix,wires]
     | cons k ks =>
       have localC:=local_support b y cin k W (fun q h=>hs q (head_mem b (bs++[a,d]) q h))
         (ht y (by simp)) (ht cin (by simp)) (ht k (by simp))
       have rest:=ih ys ks k (fun q h=>hs q (tail_mem b (bs++[a,d]) q h))
         (by intro q h;apply ht; simp only [List.mem_append,List.mem_cons,List.mem_singleton] at h ⊢;tauto)
       simpa only [addPrefix,wires_append,Finset.union_subset_iff] using
         ⟨⟨⟨localC.1,rest⟩,localC.2.1⟩,localC.2.2⟩

theorem two_physical (a d:Bit) (t z cin loan:Wire) (ha:a.Valid) (hd:d.Valid)
 (hn:[t,z,cin,loan].Nodup) (hs:∀q∈a.wires++d.wires,q∉[t,z,cin,loan]) :
 GatePhysical (two a d t z cin loan) := by
 have cnt:=List.nodup_iff_count.mp hn
 have nd:[t,cin,loan].Nodup := by
  apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
  simp only [List.count_cons,List.count_nil] at h ⊢;omega
 have aa:∀q∈a.wires,q∉[t,cin,loan] := by
  intro q h bad;exact hs q (List.mem_append_left _ h) (by simp only [List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
 have aC:=local_physical a ha t cin loan nd aa
 have dz: z∉d.wires := by intro h;exact hs z (List.mem_append_right _ h) (by simp)
 have lz:loan≠z := by
  intro e;exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [e])
 have dcx:GatePhysical [Instr.CX loan z] := by simpa [GatePhysical,PhysicalInstr,ProperGate] using lz
 have dC:GatePhysical (sum d z loan) := by
  exact (gatePhysical_append _ _).mpr ⟨fan_physical d.wires z dz,dcx⟩
 simpa only [two,gatePhysical_append] using ⟨⟨⟨⟨dcx,aC.1⟩,dC⟩,aC.1⟩,aC.2.2⟩

theorem prefix_physical (bs:List Bit) (ys cs:List Wire) (a d:Bit) (t z cin loan:Wire)
 (hn:(loan::cin::(ys++[t,z]++cs)).Nodup)
 (hs:∀q∈sites (bs++[a,d]),q∉loan::cin::(ys++[t,z]++cs))
 (hv:∀b∈bs++[a,d],b.Valid) : GatePhysical (addPrefix bs ys cs a d t z cin loan) := by
 induction bs generalizing ys cs cin with
 | nil =>
   apply two_physical _ _ _ _ _ _ (hv a (by simp)) (hv d (by simp))
   · apply List.nodup_iff_count.mpr;intro q;have h:=List.nodup_iff_count.mp hn q
     simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
   · intro q hq bad
     exact hs q (by simpa [sites] using hq)
       (by simp only [List.mem_append,List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
 | cons b bs ih =>
   cases ys with
   | nil => simp [addPrefix,GatePhysical]
   | cons y ys =>
     cases cs with
     | nil => simp [addPrefix,GatePhysical]
     | cons k ks =>
       have cnt:=List.nodup_iff_count.mp hn
       have nd:[y,cin,k].Nodup := by
        apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
        simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
       have src:∀q∈b.wires,q∉[y,cin,k] := by
        intro q h bad;exact hs q (head_mem b (bs++[a,d]) q h)
          (by simp only [List.mem_append,List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
       have loc:=local_physical b (hv b (by simp)) y cin k nd src
       have nd':(loan::k::(ys++[t,z]++ks)).Nodup := by
        apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
        simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢;omega
       have src':∀q∈sites (bs++[a,d]),q∉loan::k::(ys++[t,z]++ks) := by
        intro q h bad;exact hs q (tail_mem b (bs++[a,d]) q h)
          (by simp only [List.mem_append,List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
       have rest:=ih ys ks k nd' src' (fun v h=>hv v (List.mem_cons_of_mem _ h))
       simpa only [addPrefix,gatePhysical_append] using ⟨⟨⟨loc.1,rest⟩,loc.2.1⟩,loc.2.2⟩

theorem two_slots (a d:Bit) (t z cin loan last:Wire) :
 gateSlots (two a d t z cin loan)=gateSlots (Affine.add [a,d] [t,z] [last] cin)+3 := by
 have an:=local_slots a t cin loan
 have ao:=local_slots a t cin last
 have dn:=local_slots d z loan loan
 have do':=local_slots d z last last
 simp only [two,Affine.add,gateSlots_append,an.1,an.2.1,an.2.2,ao.1,ao.2.1,ao.2.2,dn.2.2,do'.2.2]
 norm_num [gateSlots,instructionSlots]
 omega

theorem prefix_slots (bs:List Bit) (ys cs:List Wire) (a d:Bit) (t z cin loan last:Wire)
 (hy:ys.length=bs.length) (hc:cs.length=bs.length) :
 gateSlots (addPrefix bs ys cs a d t z cin loan)=gateSlots (Affine.add (bs++[a,d]) (ys++[t,z]) (cs++[last]) cin)+3 := by
 induction bs generalizing ys cs cin with
 | nil =>
   have ye:ys=[]:=List.eq_nil_of_length_eq_zero hy
   have ce:cs=[]:=List.eq_nil_of_length_eq_zero hc
   subst ys;subst cs
   simpa only [addPrefix,List.nil_append] using two_slots a d t z cin loan last
 | cons b bs ih =>
   cases ys with
   | nil => simp at hy
   | cons y ys =>
     cases cs with
     | nil => simp at hc
     | cons k ks =>
       have r:=ih ys ks k (by simpa using hy) (by simpa using hc)
       have shape:Affine.add ((b::bs)++[a,d]) ((y::ys)++[t,z]) ((k::ks)++[last]) cin=
        majority b y cin k++Affine.add (bs++[a,d]) (ys++[t,z]) (ks++[last]) k++erase b y cin k++sum b y cin := by
        cases bs <;> cases ys <;> rfl
       simp only [addPrefix,shape,gateSlots_append,r]
       omega
end ECDSAAdd.Entrant.EntryRetained5.AffineDirty

end

section
-- Verified component JointArithmeticResources
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic Challenge BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum EntryRetained5
attribute [local irreducible] wires

def arithmeticSites : Finset Wire :=
 (ports.r++carries++[lowY ports,ports.parity,ports.lower,ports.one,ports.sign,base 0]).toFinset

theorem arithmetic_support : wires arithmetic⊆arithmeticSites := by
 apply AffineDirty.prefix_support bits targets carries (source ports 254) (source ports 255) (base 2310) (base 2311) (lowY ports) (base 0) arithmeticSites
 · intro q hq
   have used:q∈Affine.sites (sources ports) := by rwa [sources_split]
   have member:=sources_sites ports q used
   simp only [arithmeticSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
   tauto
 · intro q hq
   have data:∀q∈targets++[base 2310,base 2311],q∈ports.r := by intro q h; rwa [target_split]
   have dataq : q∈targets++[base 2310,base 2311] → q∈ports.r := data q
   simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq dataq
   simp only [arithmeticSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
   tauto

theorem arithmetic_retired : base 1541∉wires arithmetic := by
 have off:base 1541∉arithmeticSites := by decide +kernel
 exact fun h=>off (arithmetic_support h)

theorem arithmetic_avoids (q:Wire) (off:q∉arithmeticSites) : q∉wires arithmetic :=
 fun h=>off (arithmetic_support h)

theorem arithmetic_physical : GatePhysical arithmetic := by
 obtain ⟨nd,src,hv⟩:=arithmetic_layout
 apply AffineDirty.prefix_physical bits targets carries (source ports 254) (source ports 255) (base 2310) (base 2311) (lowY ports) (base 0)
 · apply List.nodup_iff_count.mpr;intro q
   have h:=List.nodup_iff_count.mp nd q
   simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
   omega
 · intro q hq bad
   exact src q hq (by simp only [List.mem_append,List.mem_cons,List.mem_singleton] at bad ⊢;tauto)
 · exact hv

theorem arithmetic_slots : gateSlots arithmetic=gateSlots (EntryRetained5.arithmetic ports)+3 := by
 have h:=AffineDirty.prefix_slots bits targets carries (source ports 254) (source ports 255)
   (base 2310) (base 2311) (lowY ports) (base 0) (base 1541) (by rfl) (by rfl)
 simpa only [arithmetic,EntryRetained5.arithmetic,sources_split,target_split,carry_split] using h
end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component OutsideSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic Challenge RecordedQuantum BalancedCircuit
attribute [local irreducible] wires
theorem outside_support (L : Layout) (hw : L.Widths) (J B : Wire) (W:Finset Wire)
 (data:∀q∈L.r++L.y,q∈W) (scalar:∀q∈[L.parity,L.lower,L.one,L.sign,J,B],q∈W) :
 wires (prepare L J B)⊆W ∧ wires (eraseScalarsAt L J B)⊆W := by
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hd := scalar L.one (by simp)
  have he := scalar L.sign (by simp)
  have hj := scalar J (by simp)
  have hb := scalar B (by simp)
  have r (q : Wire) (hq : q ∈ L.r) : q ∈ W := data q (by simp [hq])
  have y (q : Wire) (hq : q ∈ L.y) : q ∈ W := data q (by simp [hq])
  have r0 := r L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L ∈ L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have ul : L.ylow[0]?.getD 0 ∈ W := u
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254 < L.r.length := by rw [len.2.1]; decide
  have ri := r (L.r.getD 254 0) (by rw [List.getD_eq_getElem _ _ idx]; exact List.getElem_mem _)
  have riAlt : L.r[254]?.getD 0 ∈ W := ri
  have cp : wires (copyRegister (some J) L.r.tail L.y.tail) ⊆ W := by
    rw [copyRegister_wires _ _ _ (by simp [len.2.1,len.2.2.1])]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_singleton] at hq
      rcases hq with (rfl | hq) | hq
      · exact hj
      · exact r q (List.mem_of_mem_tail hq)
      · exact y q (List.mem_of_mem_tail hq)
  have rot : wires (rotateRight L.r) ⊆ W := by
    rw [(rotate_wires L.r).1,if_neg (by rw [len.2.1]; omega)]
    exact fun q hq => r q (List.mem_toFinset.mp hq)
  have comp (ctl : Wire) (hctl : ctl ∈ W) : wires (signComplement ctl L.r) ⊆ W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl | h
    · exact hctl
    · exact r q h
  have first : wires [Instr.CCX J B (lowY L)] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hj,hb,u]
  have seeds : wires [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0] ⊆ W := by
    simp [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,r0,rh,hp,ha,hd,he,u]
  have extend : wires [Instr.CX (L.r.getD 254 0) L.rmsb] ⊆ W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,ri,riAlt,rh]
  have prep : wires (prepare L J B) ⊆ W := by
    simpa only [prepare,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) (comp _ u)
  have erase : wires (eraseScalarsAt L J B) ⊆ W := by
    simp [eraseScalarsAt,eraseScalars,wires,Instr.wires,correctionWires,
      Finset.union_subset_iff,Finset.insert_subset_iff,hp,ha,hd,he,u,ul,hj,hb,rh,lowY]
  exact ⟨prep,erase⟩
end ECDSAAdd.Entrant.EntryRetained5

end

section
-- Verified component JointResources
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic Challenge BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum EntryRetained5 Baselines
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots arithmetic

def sites (J B:Wire) : Finset Wire :=
 (ports.r++ports.y++carries++[ports.parity,ports.lower,ports.one,ports.sign,J,B,base 0]).toFinset

theorem old_sites_to_new (J B q:Wire) (hq:q∈retSites ports J B) (neq:q≠base 1541) :q∈sites J B := by
 simp only [retSites,carry_split,sites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
 tauto

theorem parity_support (J B:Wire) (hJ:J∉ports.wires) : wires (parityLoan ports J)⊆sites J B := by
 have old:=EntryRetained5.program_support ports widths J B
 have oldp: wires (clearParity ports J)⊆retSites ports J B := by
  simp only [EntryRetained5.program,EntryRetained5.prefixProgram,wires_append,Finset.union_subset_iff] at old
  exact old.2
 have sf:=clearParity_free_sign ports widths ports_nodup J hJ
 intro q used
 rw [parityLoan_support_image] at used
 obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp used
 have same:ports.carry.getD 254 0=base 1541 :=rfl
 by_cases ret:a=base 1541
 · subst a
   rw [same,Equiv.swap_apply_left]
   simp [sites]
 · have ns:a≠ports.sign :=fun e=>sf (e ▸ ha)
   rw [same,Equiv.swap_apply_of_ne_of_ne ret ns]
   exact old_sites_to_new J B a (oldp ha) ret

theorem program_support (J B:Wire) (hJ:J∉ports.wires) : wires (program J B)⊆sites J B := by
 have outer:=outside_support ports widths J B (sites J B)
  (by intro q hq;simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;tauto)
  (by intro q hq;simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢;tauto)
 have ar: wires arithmetic⊆sites J B := arithmetic_support.trans (by
  intro q hq
  have y0:lowY ports∈ports.y := by rw [y_cons ports widths];simp
  simp only [arithmeticSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hq with (h|h)|rfl|rfl|rfl|rfl|rfl|rfl
  · tauto
  · tauto
  · tauto
  all_goals tauto)
 have pa:=parity_support J B hJ
 simpa only [program,prefixProgram,wires_append,Finset.union_subset_iff] using
  ⟨⟨⟨outer.1,ar⟩,outer.2⟩,pa⟩

theorem joint_support (J G:Wire) (hJ:J∉ports.wires) : wires (joint J G)⊆sites J G := by
 have pg:=program_support J G hJ
 have x: wires [Instr.X G]⊆sites J G := by simp [wires,Instr.wires,sites]
 simpa only [joint,wires_append,Finset.union_subset_iff] using ⟨⟨x,pg⟩,x⟩

theorem program_counts (J B:Wire) : toffoliCount (program J B)=772 ∧ measurementCount (program J B)=513 := by
 have old:=EntryRetained5.counts ports widths J B
 have ar:=arithmetic_counts
 have ao:=EntryRetained5.arithmetic_counts ports widths
 have pn:=parityLoan_counts ports widths J
 have po:=clearParity_counts ports widths J
 simp only [program,prefixProgram,EntryRetained5.program,EntryRetained5.prefixProgram,
  toffoliCount_append,measurementCount_append] at old ⊢
 omega

theorem joint_counts (J G:Wire) : toffoliCount (joint J G)=772 ∧ measurementCount (joint J G)=513 := by
 have h:=program_counts J G
 simpa [joint,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount] using h

theorem program_physical (J B:Wire) (hJ:J∉ports.wires) (hB:B∉ports.wires) (hJB:[J,B].Nodup) :
 GatePhysical (program J B) := by
 have old:=EntryRetained5.program_physical ports widths ports_nodup J B hJ hB hJB
 simp only [EntryRetained5.program,EntryRetained5.prefixProgram,gatePhysical_append] at old
 have ar:=arithmetic_physical
 have pa:GatePhysical (parityLoan ports J):=parityLoan_physical ports J (by tauto)
 simp only [program,prefixProgram,gatePhysical_append]
 tauto

theorem joint_physical (J G:Wire) (hJ:J∉ports.wires) (hG:G∉ports.wires) (hJG:[J,G].Nodup) :
 GatePhysical (joint J G) := by
 have p:=program_physical J G hJ hG hJG
 have x:GatePhysical [Instr.X G] :=by simp [GatePhysical,PhysicalInstr,ProperGate]
 simpa only [joint,gatePhysical_append] using ⟨⟨x,p⟩,x⟩

theorem program_slots (J B:Wire) : gateSlots (program J B)≤8003 := by
 have old:=EntryRetained5.program_slots_le ports widths J B
 have a:=arithmetic_slots
 have p: gateSlots (parityLoan ports J)=gateSlots (clearParity ports J) :=by rw [parityLoan,rename_gateSlots]
 simp only [program,prefixProgram,EntryRetained5.program,EntryRetained5.prefixProgram,gateSlots_append] at old ⊢
 omega

theorem joint_slots (J G:Wire) : gateSlots (joint J G)≤8005 := by
 have h:=program_slots J G
 simp only [joint,gateSlots_append]
 have x:gateSlots [Instr.X G]=1 :=by simp [gateSlots,instructionSlots]
 rw [x]
 omega
end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component FirstBodyFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed CompressedFieldSupport Secp256k1
attribute [local irreducible] run mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate
attribute [local irreducible] joint program arithmetic
def remainingLetters : List MixedTranscriptLetter := (List.range' 2 3).map tapeLetter
def firstBody : Program := joint (base 1028) (base 1)++
 SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters
def baseFirstPacket : Program := History5.decode base 0++firstBody++History5.encode base 0
def firstPacket : Program := renameProgram (shifted (Placement5.pi 0)) baseFirstPacket
private theorem joint_27_work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have w := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have d := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h w
    omega

private theorem joint_27_joint_pair
    (J G : Wire) (hJ : J∉ports.wires) (hG : G∉ports.wires) (hJG : [J,G].Nodup)
    (hj : J∉ports.r ∧ J∉ports.y) (hg : G∉ports.r ∧ G∉ports.y)
    (origin : BasisState) (hc : ∀q∈BalancedCircuit.work ports,origin q=false)
    (hs : origin ports.sign=false) (Z : Fp) :
    Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) (joint J G)
      (PairFrame ports.r ports.y origin
        (encodeWord 256 (halfResult (signedY (origin J && !origin G) (centerFp Z))))
        (encodeWord 256 (if origin J then centerFp Z else 0))) := by
  intro s m h
  have sign_away : ports.sign∉ports.r ∧ ports.sign∉ports.y := by
    have f := BalancedCircuit.flagAway ports ports_nodup ports.sign (by simp)
    exact ⟨fun a=>f (by simp only [List.mem_append];tauto),
      fun a=>f (by simp only [List.mem_append];tauto)⟩
  have clean : ∀q∈BalancedCircuit.work ports,s.basis q=false := by
    intro q hq
    have away := joint_27_work_away ports ports_nodup q hq
    exact (h.2.2 q away.1 away.2).trans (hc q hq)
  have out := joint_frame J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m h.1 h.2.1 clean
    ((h.2.2 _ sign_away.1 sign_away.2).trans hs)
    (h.2.2 _ hj.1 hj.2) (h.2.2 _ hg.1 hg.2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

private theorem joint_27_unary_half (b : Bool) (Z : Fp) :
    halfResult (signedY b (centerFp Z))=centerFp ((if b then -Z else Z)/2) := by
  have h:=signedY_bounds b (centerFp Z) (centerFp_bounds Z)
  have q0 : 0≤BalancedField.q := (BalancedField.constants).1.le
  have bounds : -(2*BalancedField.q)≤signedY b (centerFp Z) ∧
      signedY b (centerFp Z)≤2*BalancedField.q := by
    unfold Centered at h
    omega
  have hh:=halfResult_center _ bounds
  cases b <;> simpa only [signedY,Bool.false_eq_true,if_false,if_true,Int.cast_neg,centerFp_cast] using hh

private theorem joint_27_source_word (b : Bool) (Z : Fp) :
    encodeWord 256 (if b then centerFp Z else 0)=centerWord (if b then Z else 0) := by
  cases b
  · simp only [Bool.false_eq_true,if_false,HalfField.centerWord_zero]
    rfl
  · rfl

private theorem joint_27_enable_frame {k : Nat} {P Q : Program} (h : SW.Sel (base 2400) k P Q)
    (origin : BasisState) (hb : origin (base 2400)=true)
    (away : base 2400∉ports.r ∧ base 2400∉ports.y) (I J X Y : Nat)
    (hq : Triple (PairFrame ports.r ports.y origin I J) Q (PairFrame ports.r ports.y origin X Y)) :
    Triple (PairFrame ports.r ports.y origin I J) P (PairFrame ports.r ports.y origin X Y) := by
  intro s m hs
  rw [(h.eq m s ((hs.2.2 _ away.1 away.2).trans hb)).1]
  exact hq s m hs

private theorem joint_27_letters_layout (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (ls : List MixedTranscriptLetter)
    (hl : ∀l∈ls,∃i,i<510 ∧ l=tapeLetter i) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls := by
  intro l h
  obtain ⟨i,hi,rfl⟩:=hl l h
  simpa only [tapeLetter] using mixedTape_getD_layout base _ _ _ ctx.hf i (by omega)

private theorem joint_27_payload_cons (origin:BasisState) (hb:origin (base 2400)=true)
    (ls:List MixedTranscriptLetter) (Q:Fp×Fp) :
    directionalPayload false (mixedTranscriptControls origin (base 2400) (tapeLetter 1::ls)) Q=
    directionalPayload false (mixedTranscriptControls origin (base 2400) ls)
      (skywalkPayloadCell (origin (base 1)) (origin (base 1029)) Q) := by
  simp only [mixedTranscriptControls,List.map_cons,directionalPayload,Bool.false_eq_true,
    if_false,skywalkPayloadReplay,tapeLetter,mixedTape_base_getD 1 (by decide),mixedTranscriptBit,hb,if_true]

private theorem joint_27_first_payload_split (origin : BasisState) (hb : origin (base 2400)=true) (Z : Fp) :
    Replay5.firstPayload true origin (Z,0)=
      directionalPayload false (mixedTranscriptControls origin (base 2400) remainingLetters)
        (skywalkPayloadCell (origin (base 1)) (origin (base 1029))
          (if origin (base 1028) then (0,Z) else (Z,0))) := by
  have rest : Replay5.restLetters=tapeLetter 1::remainingLetters := by rfl
  rw [Replay5.firstPayload,if_pos rfl,rest,joint_27_payload_cons origin hb]
  apply congrArg (fun Q=>directionalPayload false (mixedTranscriptControls origin (base 2400) remainingLetters) Q)
  simp only [mixedTranscriptBit,hb,if_true]

/-- Joint initial copy/half, then the unchanged S1 swap and cells2..4. -/
theorem firstBody_frame (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) :
    Triple (PairFrame ports.r ports.y origin (centerWord Z) 0) firstBody
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 1 (by decide)) ctx.ho
  rw [mixedTape_base_getD 1 (by decide)] at layout
  have newLayout := OneBankCell5.ports_transcript base (base 2400) (base 1) (base 1029)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hn := newLayout.kernel
  have hw := newLayout.widths
  have hJ : base 1028∉ports.wires := by decide
  have hG : base 1∉ports.wires := by decide
  have outside (q : Wire) (hq : q∉ports.wires) : q∉ports.r ∧ q∉ports.y := by
    constructor <;> intro h <;> apply hq
    · exact EntryRetained5.data_member ports q (by simp [h])
    · exact EntryRetained5.data_member ports q (by simp [h])
  have away : base 2400∉ports.r ∧ base 2400∉ports.y := newLayout.outside _ (by simp)
  have clean := OneBankCell5.clean_of_env_work base (base 2409) origin ctx.env ctx.parity
  have hjoint := joint_27_joint_pair _ _ hJ hG (by decide) (outside _ hJ) (outside _ hG)
    origin clean ctx.hg0 Z
  let J:=origin (base 1028)
  let G:=origin (base 1)
  let S:=origin (base 1029)
  let A:Fp := (if J && !G then -Z else Z)/2
  let B:Fp := if J then Z else 0
  have jf : Triple (PairFrame ports.r ports.y origin (centerWord Z) 0)
      (joint (base 1028) (base 1)) (PairFrame ports.r ports.y origin (centerWord A) (centerWord B)) := by
    rw [joint_27_unary_half,joint_27_source_word] at hjoint
    exact hjoint
  have swap := OneFlagCell.selectSwap_frame base (base 2400) (base 1029) (base 2409)
    (mixedTranscriptUnitTrace.getD 1 (false,false)).2 OneFlagReplay.base_sign_nd (by decide)
    (newLayout.outside _ (by simp)) (newLayout.outside _ (by simp))
    (newLayout.outside _ (by simp [OneBankCell5.ports_sign])) origin ctx.hg0 A B
  have sel := ((SW.Sel.refl (base 2400) OneFlagSW.swapBody OneFlagSW.selSwap_away).window
    (base 1029) (base 2409) (mixedTranscriptUnitTrace.getD 1 (false,false)).2 (by decide))
  have sf := joint_27_enable_frame sel origin hb away (centerWord A) (centerWord B)
    (centerWord (if S then B else A)) (centerWord (if S then A else B)) (by
      simpa only [OneFlagCell.selectSwap,OneFlagSW.swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,
        mixedTranscriptBit,hb,if_true,S] using swap)
  have lsf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) remainingLetters :=
    joint_27_letters_layout origin ctx _ (by
      intro l hl
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
      exact ⟨i,by have := List.mem_range'_1.mp hi;omega,rfl⟩)
  have rf := OneFlagReplay.raw_frame true remainingLetters lsf origin ctx (if S then B else A) (if S then A else B)
  have rs := OneFlagSW.selRaw_sel true remainingLetters (by
    intro l hl
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
    exact OneFlagSW.selLetter_nodup i (by have := List.mem_range'_1.mp hi;omega))
  have tail := joint_27_enable_frame rs origin hb away _ _ _ _ rf
  have all := (jf.seq sf).seq tail
  have cell : (if S then B else A,if S then A else B)=
      skywalkPayloadCell G S (if J then (0,Z) else (Z,0)) := by
    cases eJ:J <;> cases eG:G <;> cases eS:S <;>
      simp [A,B,skywalkPayloadCell,eJ,eG,eS]
  rw [joint_27_first_payload_split origin hb Z]
  simpa only [firstBody,List.append_assoc,cell,J,G,S] using all


end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component FirstSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed
attribute [local irreducible] wires
private theorem joint_28_ports_field_sites :
    (ports.r++ports.y++ports.carry++[ports.parity,ports.lower,ports.one,ports.sign]).toFinset ⊆
      OneFlagReplay.fieldSites := by
  intro q hq
  simp only [ports,OneBankCell5.ports,OneBankCell5.ids,Q6EndpointCell.ids,OneFlagReplay.fieldSites,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    wireBlock,List.map_append,List.map_cons,List.map_nil,List.mem_toFinset,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  tauto

private theorem joint_28_sel_support (source flag : Wire) (P : Program) (W : Finset Wire)
    (hs : source∈W) (hf : flag∈W) (hp : wires P⊆W) :
    wires (SW.selW source flag P)⊆W := by
  have head : wires [Instr.CX source flag]⊆W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hs,hf]
  have tail : wires [Instr.measureX flag [] [Correction.Z source]]⊆W := by
    simp [wires,Instr.wires,correctionWires,Finset.insert_subset_iff,hs,hf]
  simpa only [SW.selW,wires_append,Finset.union_subset_iff] using ⟨⟨head,hp⟩,tail⟩


theorem firstBody_support : wires firstBody⊆OneFlagReplay.readSites 0 := by
 let W:=OneFlagReplay.readSites 0
 have hi:OneFlagReplay.fieldSites⊆W := fun _ h=>Finset.mem_union_left _ (Finset.mem_union_left _ h)
 have data (q:Wire) (hq:q∈ports.r++ports.y++ports.carry++[ports.parity,ports.lower,ports.one,ports.sign]) : q∈W :=
  hi (joint_28_ports_field_sites (List.mem_toFinset.mpr hq))
 have g0:base 0∈W := Finset.mem_union_right _ (by simpa using (Replay5.history_controls 0 0 (by decide)).1)
 have js:base 1028∈W := Finset.mem_union_right _ (by simpa using (Replay5.history_controls 0 0 (by decide)).2)
 have gg:base 1∈W := Finset.mem_union_right _ (by simpa using (Replay5.history_controls 0 1 (by decide)).1)
 have ss:base 1029∈W := Finset.mem_union_right _ (by simpa using (Replay5.history_controls 0 1 (by decide)).2)
 have flag:base 2409∈W := data _ (by simp [ports,OneBankCell5.ports])
 have jointS:wires (joint (base 1028) (base 1))⊆W :=
  (joint_support _ _ (by decide +kernel)).trans (by
   intro q hq
   have cc:q∈carries→q∈ports.carry := by
    intro h;exact List.mem_of_mem_take (carry_split ▸ List.mem_append_left _ h)
   have dd:q∈ports.r++ports.y++ports.carry++[ports.parity,ports.lower,ports.one,ports.sign]→q∈W :=data q
   simp only [sites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
   simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at dd
   rcases hq with ((h|h)|h)|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   · exact data q (by simp [h])
   · exact data q (by simp [h])
   · exact data q (by simp [cc h])
   all_goals first |assumption |apply data; simp)
 have swap:wires OneFlagSW.swapBody⊆W := by
  intro q hq
  have h:=swapRegisters_wires (base 2409)
    (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y (by simp [balancedSharedPorts_r,balancedSharedPorts_y,wireBlock_length]) hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  rcases h with rfl|hr|hy
  · exact flag
  · exact data q (by simpa only [OneBankCell5.ports_r] using (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))))
  · exact data q (by simpa only [OneBankCell5.ports_y] using (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hy))))
 have selSwap:=joint_28_sel_support (base 1029) (base 2409) OneFlagSW.swapBody W ss flag swap
 have raw:wires (OneFlagSW.rawReplayS true remainingLetters)⊆W := by
  have old:=OneFlagReplay.raw_support true remainingLetters W hi
    (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp)))
    (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp)))
    (by intro l hl;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
        exact ⟨Finset.mem_union_right _ (by simpa only [Nat.zero_add,tapeLetter,mixedTape_base_getD i (by have := List.mem_range'_1.mp hi;omega)] using (Replay5.history_controls 0 i (by have := List.mem_range'_1.mp hi;omega)).1),
          Finset.mem_union_right _ (by simpa only [Nat.zero_add,tapeLetter,mixedTape_base_getD i (by have := List.mem_range'_1.mp hi;omega)] using (Replay5.history_controls 0 i (by have := List.mem_range'_1.mp hi;omega)).2)⟩)
  exact (OneFlagSW.selRaw_sel true remainingLetters (by
    intro l hl;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hl
    exact OneFlagSW.selLetter_nodup i (by have := List.mem_range'_1.mp hi;omega))).sub.wires_sub.trans old
 simpa only [firstBody,wires_append,Finset.union_subset_iff] using ⟨⟨jointS,selSwap⟩,raw⟩

theorem firstBody_read_support :
 wires firstBody⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
 firstBody_support.trans (OneFlagReplay.readSites_sub 0)
end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component FirstPacketFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed CompressedFieldSupport Secp256k1
attribute [local irreducible] run firstBody joint program arithmetic
theorem firstPacket_frame (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    (run firstPacket m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (Replay5.firstPayload true origin (Z,0)).1 (Replay5.firstPayload true origin (Z,0)).2
        (run firstPacket m s) := by
  have body : Triple
      (PairFrame ports.r ports.y origin (centerWord Z) (centerWord (0:Fp))) firstBody
      (PairFrame ports.r ports.y origin
        (centerWord (Replay5.firstPayload true origin (Z,0)).1)
        (centerWord (Replay5.firstPayload true origin (Z,0)).2)) := by
    simpa only [HalfField.centerWord_zero] using firstBody_frame origin ctx hb Z
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin Z 0 _ _ _ firstBody_read_support body s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) baseFirstPacket
    (fun q hq=>Placement5.pi_outside 0 q (by decide) hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal Z 0 s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run firstPacket m s=run baseFirstPacket m s := eq
  rw [same]
  exact fresh

end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component Replay

/-! The new first packet with the old, unchanged forward replay suffix. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires History5.allEncode run measurementCount OneFlagSW.groupsS OneFlagSW.endPacketS

def logicalReplay : Program :=
  firstPacket ++ OneFlagSW.groupsS true 1 101 ++ OneFlagSW.endPacketS true

def replay : Program := renameProgram (OB5.sig 511) logicalReplay

/-- The old packet uses its own record tape; the unchanged suffix keeps the new tape. -/
def oldRecords (m : List Bool) : List Bool :=
  List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false ++
    m.drop (measurementCount firstPacket)

theorem oldRecords_take (m : List Bool) :
    (oldRecords m).take (measurementCount (OneFlagSW.firstPacketS true))=
      List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false := by
  rw [oldRecords,List.take_append_of_le_length (by
    simpa only [List.length_replicate] using
      (Nat.le_refl (measurementCount (OneFlagSW.firstPacketS true))))]
  simpa only [List.length_replicate] using
    List.take_length (l:=List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false)

theorem oldRecords_drop (m : List Bool) :
    (oldRecords m).drop (measurementCount (OneFlagSW.firstPacketS true))=
      m.drop (measurementCount firstPacket) := by
  have nil : (List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false).drop
      (measurementCount (OneFlagSW.firstPacketS true))=[] := by
    simpa only [List.length_replicate] using
      List.drop_length (l:=List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false)
  rw [oldRecords,List.drop_append,List.length_replicate,nil,Nat.sub_self,List.drop_zero,List.nil_append]

private theorem joint_30_encoded_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (ht : History5.EncodedFieldFrame5 base (base 2409) origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩:=hs
  obtain ⟨b,hb,fb,eb⟩:=ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem encoded_enable (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (X Y : Fp) (s : State)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    s.basis (base 2400)=true := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  have away := layout.outside (base 2400) (by simp)
  obtain ⟨raw,_,frame,encoded⟩:=input
  have unused : base 2400∉wires (History5.allEncode base 102) := by
    intro used
    have support : wires (History5.allEncode base 102)⊆(skywalkPoolWires base).toFinset := HalfField5.encoder_pool_support
    have pool : base 2400∈skywalkPoolWires base := List.mem_toFinset.mp (support used)
    exact ctx.hp (base 2400) (by simp) pool
  rw [encoded,run_preserves_outside _ [] raw _ unused]
  exact (frame.2.2 _ away.1 away.2).trans hb

/-- Both packet record tapes are arbitrary and independent. -/
theorem firstPacket_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (mNew mOld : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run firstPacket mNew s=run (OneFlagSW.firstPacketS true) mOld s := by
  have fresh := firstPacket_frame origin ctx hb Z s mNew input
  have old := OneFlagReplay.firstPacket_frame true origin ctx Z 0 s mOld input (by simp)
  have eq := (OneFlagSW.selFirstPacket_sel true).eq mOld s (encoded_enable origin ctx hb Z 0 s input)
  rw [←eq.1] at old
  exact joint_30_encoded_unique origin _ _ _ _ fresh.2 old.2 (fresh.1.trans old.1.symm)

/-- Only the old first-packet tape is padded. The groups and end packet are unchanged. -/
theorem logical_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run logicalReplay m s=run (OneFlagSW.logicalReplayS true) (oldRecords m) s := by
  have first := firstPacket_compare origin ctx hb Z s (m.take (measurementCount firstPacket))
    (List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false) input
  have freshShape : logicalReplay=firstPacket++(OneFlagSW.groupsS true 1 101++OneFlagSW.endPacketS true) := by
    simp only [logicalReplay,List.append_assoc]
  have oldShape : OneFlagSW.logicalReplayS true=OneFlagSW.firstPacketS true++(OneFlagSW.groupsS true 1 101++OneFlagSW.endPacketS true) := by
    simp only [OneFlagSW.logicalReplayS,if_true,List.append_assoc]
  rw [freshShape,oldShape]
  simp only [run_append,oldRecords_take,oldRecords_drop]
  rw [first]

/-- The same record builder works after the final sig511 field placement. -/
theorem replay_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run replay m s=run (OneFlagSW.replayS true) (oldRecords m) s := by
  have localEq := logical_compare origin ctx hb Z (pullState (OB5.sig 511) s) m input
  have fresh := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) logicalReplay m s
  have old := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (OneFlagSW.logicalReplayS true) (oldRecords m) s
  have eq := congrArg (pullState (OB5.sig 511)) (fresh.trans (localEq.trans old.symm))
  simpa only [OB5.pull_invol 511 (by decide),replay,OneFlagSW.replayS] using eq

end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component KernelProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
def field5S : Program := JointEntryQ7.replay ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def rawKernel : Program := Q5FusionPhase.kernel hostField5S
def baseKernel : Program := Q5FusionPhase.relocated hostField5S
def kernel6S : Program := Q6FusionPhase.relocated hostField5S
def kernel5S : Program := Q7FusionPhase.relocated hostField5S
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component FieldTransferPrefix
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS
  OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S OneFlagEntryRaw.field5 OneFlagEntryRaw.hostField5
  OneFlagEntryRaw.kernel5 OneFlagSW.replayS JointEntryQ7.replay JointEntryQ7.logicalReplay
  OneFlagSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

theorem replay_records_drop (m : List Bool) :
    (JointEntryQ7.oldRecords m).drop (measurementCount (OneFlagSW.replayS true))=
      m.drop (measurementCount JointEntryQ7.replay) := by
  let a:=measurementCount (OneFlagSW.firstPacketS true)
  let b:=measurementCount JointEntryQ7.firstPacket
  let c:=measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (OneFlagSW.endPacketS true)
  have old : measurementCount (OneFlagSW.replayS true)=a+c := by
    unfold OneFlagSW.replayS
    rw [(renameProgram_counts _ _).2]
    simp only [OneFlagSW.logicalReplayS,if_true,measurementCount_append,a,c,Nat.add_assoc]
  have fresh : measurementCount JointEntryQ7.replay=b+c := by
    unfold JointEntryQ7.replay
    rw [(renameProgram_counts _ _).2]
    simp only [JointEntryQ7.logicalReplay,measurementCount_append,b,c,Nat.add_assoc]
  have drop (a b c : Nat) : (List.replicate a false ++ m.drop b).drop (a+c)=m.drop (b+c) := by
    have nil : (List.replicate a false).drop (a+c)=[] :=
      List.drop_eq_nil_iff.mpr (by simp only [List.length_replicate];omega)
    rw [List.drop_append,List.length_replicate,nil]
    simp only [Nat.add_sub_cancel_left,List.nil_append,List.drop_drop]
  rw [old,fresh]
  exact drop a b c

theorem field_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run field5S m s=run OneFlagEntryRaw.field5S (JointEntryQ7.oldRecords m) s := by
  have eq:=JointEntryQ7.replay_compare origin ctx hb Z s m input
  simp only [field5S,OneFlagEntryRaw.field5S,run_append,run_take]
  rw [eq,replay_records_drop]

theorem hosted_compare (P Q : Program) (s : State) (m n : List Bool)
    (pf : base 511∉wires P) (qf : base 511∉wires Q)
    (sg : s.basis (base 2409)=false) (hg : s.basis (base 511)=true)
    (se : s.basis (base 2410)=false) (he : s.basis (base 1542)=false)
    (eq : run P m s=run Q n s) :
    run ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)])) m s=
      run ([.X (base 511)]++(renameProgram HostOB5.hostSwap Q++[.X (base 511)])) n s := by
  let X:Program := [.X (base 511)]
  let u:=run X [] s
  have dis (R : Program) (hr : base 511∉wires R) : Disjoint (wires X) (wires R) := by
    apply Finset.disjoint_left.mpr
    intro q hq used
    have e:q=base 511 := by simpa only [X,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton] using hq
    exact hr (e ▸ used)
  have cp:=run_disjoint_commute X P (dis P pf) [] m s
  have cq:=run_disjoint_commute X Q (dis Q qf) [] n s
  have equal : run P m u=run Q n u := cp.symm.trans ((congrArg (run X []) eq).trans cq)
  have pull : pullState HostOB5.hostSwap u=u := by
    apply HostOB5.host_pull
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2409)=!s.basis (base 511)
      rw [sg,hg];rfl
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2410)=s.basis (base 1542)
      rw [se,he]
  have rp:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective P m u
  have rq:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective Q n u
  rw [pull] at rp rq
  have ren : run (renameProgram HostOB5.hostSwap P) m u=run (renameProgram HostOB5.hostSwap Q) n u := by
    have e:=congrArg (pullState HostOB5.hostSwap) (rp.trans (equal.trans rq.symm))
    simpa only [pullState,HostOB5.hostSwap_invol] using e
  have records (r : List Bool) (t : State) : run X r t=run X [] t := by simp only[X,run]
  simpa only [X,u,run_append,measurementCount,List.take_zero,List.drop_zero,run_take,run] using
    congrArg (run X []) ren

end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component FieldReady
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S
 OneFlagEntryRaw.field5

theorem field_from_ready
 (hostFree : base 511∉wires field5S) (origin : BasisState) (ctx : OneFlagReplay.Context origin)
 (enabled : origin (base 2400)=true) (Z : Fp) (a3 v3 : State) (m : List Bool)
 (frame : FieldFrameOB5.EncodedFieldFrame origin Z 0 v3)
 (paired : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (selectors : a3.basis (base 2409)=false ∧ a3.basis (base 2410)=false)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false) :
 run hostField5S m v3=run OneFlagEntryRaw.hostField5S (JointEntryQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have unhosted : run field5S m v3=run OneFlagEntryRaw.field5S (JointEntryQ7.oldRecords m) v3 :=
  field_compare origin ctx enabled Z v3 m frame
 have outside (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 :=
  OwnPlusHost.not_block i 2056 256 (by omega)
 have keep (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
  (paired _ (outside i hi)).symm
 have oldSubset : wires OneFlagEntryRaw.field5S⊆wires OneFlagEntryRaw.field5 :=
  OneFlagEntryRaw.selField5.sub.wires_sub
 have oldAway : base 511∉wires OneFlagEntryRaw.field5 := OneFlagEntryRaw.field_free.1
 have oldFree : base 511∉wires OneFlagEntryRaw.field5S := fun used=>oldAway (oldSubset used)
 have compared:=hosted_compare field5S OneFlagEntryRaw.field5S v3 m (JointEntryQ7.oldRecords m)
  hostFree oldFree ((keep 2409 (by omega)).trans selectors.1)
  ((keep 511 (by omega)).trans hosts.1) ((keep 2410 (by omega)).trans selectors.2)
  ((keep 1542 (by omega)).trans hosts.2) unhosted
 have on:=JointEntryQ7.encoded_enable origin ctx enabled Z 0 (pullState (OB5.sig 511) v3) frame
 have sigb : OB5.sig 511 (base 2400)=base 2400 := by decide
 refine ⟨?_,?_⟩
 · simpa only [hostField5S,OneFlagEntryRaw.hostField5S] using compared
 · simpa only [pullState,sigb] using on
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component RetargetFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
namespace ECDSAAdd.Entrant.JointEntryPrepared
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires

theorem retarget (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
 (hr : origin (base 2312)=false) (hy : origin (base 1026)=false) (Y : Fp) (a3 v3 : State)
 (phase : a3.phase=v3.phase)
 (same : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2))
 (canonical : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 a3) :
 FieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 v3 := by
 have logicalSame : ∀q,q∉wireBlock base 2056 256 →
   (pullState (OB5.sig 511) v3).basis q=(pullState (OB5.sig 511) a3).basis q := by
  intro q hq
  exact (same _ (EntryFuse.sig_num_away q hq)).symm
 have logicalValue : regValue (wireBlock base 2056 256) (pullState (OB5.sig 511) v3).basis=centerWord (Y/2) := by
  apply (regValue_congr _ _ _ ?_).trans target
  intro q hq
  change v3.basis (OB5.sig 511 q)=v3.basis q
  rw [EntryFuse.sig_num_fix q hq]
 exact EntryFuse.encoded_retarget5 hn origin hr hy Y
  (pullState (OB5.sig 511) a3) (pullState (OB5.sig 511) v3) phase.symm logicalSame logicalValue canonical
end ECDSAAdd.Entrant.JointEntryPrepared

end

section
-- Verified component FieldFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S

theorem field_from_facts (hostFree : base 511∉wires field5S)
 (hn : (skywalkSharedWires base).Nodup)
 (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 (x : Nat) (Y : Fp) (s origin a3 v3 : State) (m : List Bool)
 (facts : PreparationFacts x Y s origin) (legal : History5.RawLegal base 102 origin.basis)
 (canonical : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false)
 (phase : a3.phase=v3.phase)
 (same : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2))
 (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
 (hb : s.basis (base 2400)=true) :
 run hostField5S m v3=run OneFlagEntryRaw.hostField5S (JointEntryQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
  intro q hq bad
  exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
 have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
 have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
 have enabled : origin.basis (base 2400)=true := (facts.controls _ (by simp)).trans hb
 have frame:=JointEntryPrepared.retarget hn origin.basis facts.targetHigh facts.sourceHigh Y a3 v3 phase same target canonical
 let ctx : OneFlagReplay.Context origin.basis := ⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩
 have selectors:=EntryFuse.encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 canonical
 exact field_from_ready hostFree origin.basis ctx enabled (Y/2) a3 v3 m frame same selectors hosts
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component PreparedPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryPrepared
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires SkywalkTrace.trace SkywalkTrace.next Nat.iterate
 NativeFirstDirect.forward stackForwardT skywalkArithmeticClear compactForward5

theorem canonical_prefix
 (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
 (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m1 m2 m3 : List Bool)
 (hin : SkywalkArithmeticInput base x Y.val s.basis) (a1 a2 a3 : State)
 (ha1 : run (NativeFirstDirect.forward base) m1 s=a1)
 (ha2 : run stackForwardT m2 a1=a2) (ha3 : run (skywalkArithmeticClear base) m3 a2=a3) :
 ∃origin : State, PreparationFacts x Y s origin ∧ History5.RawLegal base 102 origin.basis ∧
  FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 ∧
  a3.basis (base 511)=true ∧ a3.basis (base 1542)=false := by
 have first:=NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
 rw [ha1] at first
 change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
 generalize ht2 : run (compactForward5 base 1 511) m2 a1 = t2
 generalize ht3 : run (skywalkArithmeticClear base) m3 t2 = t3
 obtain ⟨hp0,hpo,hpp,cop⟩:=OB5.prime_facts x hx0 hx
 have pool:=skywalkShared_integer_nodup base hn
 have firstW:=(W.compactSkywalkStage_one base _ a1.basis).mpr first
 have gap : p+2^32≤2^256 := by norm_num [p]
 have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 := by
  simpa only [ht2] using Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp gap hx cop a1 m2 m2 first
 have e2 : a2=pullState (OB5.sig 511) t2 := by
  rw [←ha2,stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
  have fwd:=StackOB5.forward_run x hx0 hx a1 m2 firstW
  rw [wEq] at fwd
  exact fwd
 have e3 : a3=pullState (OB5.sig 511) t3 := by
  rw [←ha3,e2,KernelOB5.clear_placed,ht3]
 obtain ⟨origin,facts,legal,_,encEq,entry⟩:=Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
  m1 m2 m3 hin a1 t2 t3 ha1 ht2 ht3 first
 have canonical : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
  change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
  rw [e3,OB5.pull_invol 511 (by decide)]
  exact entry
 have hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false :=
  EntryFuse.encoded_host_bits5 x hx0 hx origin t3 a3 facts.trace encEq e3
 exact ⟨origin,facts,legal,canonical,hosts⟩
end ECDSAAdd.Entrant.JointEntryPrepared

end

section
-- Verified component PairedPrefix
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
namespace ECDSAAdd.Entrant.JointEntryPrepared
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires NativeFirstDirect.forward stackForwardT skywalkArithmeticClear

theorem paired_prefix (s t a1 a2 a3 v1 v2 v3 : State) (m1 m2 m3 : List Bool)
 (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
 (ha1 : run (NativeFirstDirect.forward base) m1 s=a1)
 (ha2 : run stackForwardT m2 a1=a2) (ha3 : run (skywalkArithmeticClear base) m3 a2=a3)
 (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
 (h2 : run stackForwardT m2 v1=v2) (h3 : run (skywalkArithmeticClear base) m3 v2=v3) :
 a3.phase=v3.phase ∧ (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
 (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) := by
 have h:=EntryFuse.pool_three (NativeFirstDirect.forward base) stackForwardT (skywalkArithmeticClear base)
  EntryFuse.first_pool5 EntryFuse.forward_pool5 EntryFuse.clear_pool5 s t m1 m2 m3 phase.symm
  (fun q hq=>(same q hq).symm) v1 v2 v3 h1 h2 h3
 dsimp only at h
 simpa only[ha1,ha2,ha3] using h
end ECDSAAdd.Entrant.JointEntryPrepared

end

section
-- Verified component StateCompare
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS
  OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S OneFlagEntryRaw.field5 OneFlagEntryRaw.hostField5
  OneFlagEntryRaw.kernel5 OneFlagSW.replayS JointEntryQ7.replay JointEntryQ7.logicalReplay
  OneFlagSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

theorem field_state_compare
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) (v1 v2 v3 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run stackForwardT m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3) :
    run hostField5S m4 v3=run OneFlagEntryRaw.hostField5S (JointEntryQ7.oldRecords m4) v3 ∧
      v3.basis (base 2400)=true := by
  generalize ha1 : run (NativeFirstDirect.forward base) m1 s = a1
  generalize ha2 : run stackForwardT m2 a1 = a2
  generalize ha3 : run (skywalkArithmeticClear base) m3 a2 = a3
  have paired:=JointEntryPrepared.paired_prefix s t a1 a2 a3 v1 v2 v3 m1 m2 m3
    phase same ha1 ha2 ha3 h1 h2 h3
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) :=
    (regValue_congr _ _ _ paired.2.2).trans value
  obtain ⟨origin,facts,legal,canonical,hosts⟩:=JointEntryPrepared.canonical_prefix hn hlo ho
    x Y hx0 hx s m1 m2 m3 hin a1 a2 a3 ha1 ha2 ha3
  exact field_from_facts field5S_hosts_free.1 hn ho hf x Y s origin a3 v3 m4 facts legal canonical hosts
    paired.1 paired.2.1 target hg0 hs0 hb

end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component EnabledKernel
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS
  OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S OneFlagEntryRaw.field5 OneFlagEntryRaw.hostField5
  OneFlagEntryRaw.kernel5 OneFlagSW.replayS JointEntryQ7.replay JointEntryQ7.logicalReplay
  OneFlagSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

theorem enabled_kernel_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5S) m t) := by
  let P : State→State→Prop := fun initial out=>initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all:=skywalkRunSeven (NativeFirstDirect.forward base) stackForwardT (skywalkArithmeticClear base)
    hostField5S (skywalkArithmeticClear base) stackReverseT (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 ph sm val
      have pair:=field_state_compare field5S_hosts_free hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 hin hg0 hs0
        ph sm val hb v1 v2 v3 h1 h2 h3
      have selected:=(OneFlagEntryRaw.selHostField5.eq (JointEntryQ7.oldRecords m4) v3 pair.2).1
      have old4 : run OneFlagEntryRaw.hostField5 (JointEntryQ7.oldRecords m4) v3=v4 := by
        have e:=pair.1.symm.trans h4
        rw [selected] at e
        simpa only [OneFlagEntryRaw.hostField5,OneFlagEntryRaw.field5,EntryFuse.hostField5,EntryFuse.field5] using e
      exact OneFlagEntryRaw.kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3
        (JointEntryQ7.oldRecords m4) m5 m6 m7 hin hg0 hs0 ph sm val
        v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 old4 h5 h6 h7) t m
  simpa only [Q5FusionPhase.kernel,firstPhase,lastPhase,List.append_assoc] using all phase same value

end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component EnabledBase
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS
  OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S OneFlagEntryRaw.field5 OneFlagEntryRaw.hostField5
  OneFlagEntryRaw.kernel5 OneFlagSW.replayS JointEntryQ7.replay JointEntryQ7.logicalReplay
  OneFlagSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free

theorem enabled_base_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run baseKernel m t) := by
  have old:=enabled_kernel_correct field5S_hosts_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value hb
  have eq:=Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5S true
    hin same hostField5S_1026_free old
  rw [baseKernel,eq]
  exact old


end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component BaseCorrect
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS OneFlagSW.endPacketS
  OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S OneFlagEntryRaw.field5 OneFlagEntryRaw.hostField5
  OneFlagEntryRaw.kernel5 OneFlagSW.replayS JointEntryQ7.replay JointEntryQ7.logicalReplay
  OneFlagSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free baseKernel_control_free

theorem base_kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out:=run baseKernel m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := EntryFuse.forceControl5 s
  let b := EntryFuse.forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [EntryFuse.forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := EntryFuse.forceControl5_true s
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [EntryFuse.forceControl5_true,EntryFuse.forceControl5_true]
    · rw [EntryFuse.forceControl5_keep t q e,EntryFuse.forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact EntryFuse.forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong:=enabled_base_correct field5S_hosts_free hostField5S_1026_free hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half ab
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree:=pool_run_agrees baseKernel (wires baseKernel) (Finset.Subset.refl _) m t b rfl
    (fun q hq=>(EntryFuse.forceControl5_keep t q (fun e=>baseKernel_control_free (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run baseKernel m t).basis q=(run baseKernel m b).basis q := by
    by_cases used:q∈wires baseKernel
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (EntryFuse.forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e=>numAway (e ▸ hq))
  · intro q hq
    by_cases e:q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ baseKernel_control_free).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (EntryFuse.forceControl5_keep s q e))

end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component FieldTransfer

end

section
-- Verified component KernelCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
variable (hostField5S_1541_free : base 1541∉wires hostField5S)
variable (hostField5S_1542_free : base 1542∉wires hostField5S)
attribute [local irreducible] run wires kernel5S kernel6S baseKernel hostField5S

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free
theorem kernel6S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel6S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=base_kernel5S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q6FusionPhase.kernel hostField5S=baseKernel :=
    by simpa only [baseKernel] using Q6FusionGeometry.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1541_free frame
  simpa only [kernel6S,eq,shape] using old

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include hostField5S_1542_free
theorem kernel5S_correct_of_static
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=kernel6S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q7FusionPhase.kernel hostField5S=kernel6S :=
    by simpa only [kernel6S] using Q7FusionPhase.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1542_free frame
  simpa only [kernel5S,eq,shape] using old

end StaticPremises
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component FirstResources

set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed
attribute [local irreducible] wires toffoliCount measurementCount

private theorem joint_44_rest_nodup (l : MixedTranscriptLetter) (hl : l∈remainingLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  apply OneFlagSW.selRest_nodup
  change l∈tapeLetter 1::remainingLetters
  exact List.mem_cons_of_mem _ hl

theorem firstBody_control_free : base 2400∉wires firstBody := by
  have raw : base 2400∉wires (joint (base 1028) (base 1)) := by
    have off : base 2400∉sites (base 1028) (base 1) := by decide +kernel
    exact fun h=>off (joint_support _ _ (by decide +kernel) h)
  have sw := (((SW.Sel.refl (base 2400) OneFlagSW.swapBody OneFlagSW.selSwap_away).window
    (base 1029) (base 2409) false (by decide +kernel))).away
  have tail := (OneFlagSW.selRaw_sel true remainingLetters joint_44_rest_nodup).away
  simpa only [firstBody,wires_append,Finset.mem_union,not_or] using And.intro (And.intro raw sw) tail

theorem firstPacket_control_free : base 2400∉wires firstPacket := by
  have codec := OneFlagSW.selHist_away 0 (by omega)
  have raw : base 2400∉wires baseFirstPacket := by
    simpa only [baseFirstPacket,wires_append,Finset.mem_union,not_or] using
      And.intro (And.intro codec.2 firstBody_control_free) codec.1
  exact OwnPlusHost.rename_avoid (shifted (Placement5.pi 0)) _ _ (SW.selShift_fix 0 (by omega)) raw

private theorem joint_44_swap_nd : (base 2410::(ports.r++ports.y)).Nodup := by
  have hn := MappedCompressed.LaneA.laneLogical_config.1
  have ho : base 2410∉skywalkSharedWires base :=
    MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp)
  have own : base 2410∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2410) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2410)) nd (base 2410)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2410) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2410∈(balancedSharedPorts base (base 2410)).r := by
      simpa only [ports,OneBankCell5.ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2410∈(balancedSharedPorts base (base 2410)).y := by
      simpa only [ports,OneBankCell5.ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

private theorem joint_44_selSwap_counts :
    toffoliCount (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)=256 ∧
      measurementCount (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)=1 := by
  have hw:=OneBankCell5.ports_widths base (base 2409)
  have width:=BalancedCleanup.widths ports.toLayout hw
  have c:=swapRegisters_resources (base 2409) ports.r ports.y
    (width.2.1.trans width.2.2.1.symm) OneFlagReplay.base_sign_nd
  change toffoliCount (SW.selW (base 1029) (base 2409) (swapRegisters (base 2409) ports.r ports.y))=256 ∧
    measurementCount (SW.selW (base 1029) (base 2409) (swapRegisters (base 2409) ports.r ports.y))=1
  simp only [SW.selW,
    toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    c.1,c.2.1,width.2.1]
  norm_num

theorem firstPacket_counts : toffoliCount firstPacket=4876 ∧ measurementCount firstPacket=3589 := by
  have old:=OneFlagReplay.raw_counts true remainingLetters
    joint_44_swap_nd
  have len : remainingLetters.length=3 := by simp [remainingLetters]
  rw [len] at old
  have selected:=OneFlagSW.selRaw_sel true remainingLetters joint_44_rest_nodup
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have jointC:=joint_counts (base 1028) (base 1)
  have sw:=joint_44_selSwap_counts
  have ec:=History5.encode_counts base 0
  have dc:=History5.decode_counts base 0
  have placed:=renameProgram_counts (shifted (Placement5.pi 0)) baseFirstPacket
  simp only [firstPacket]
  rw [placed.1,placed.2]
  simp only [baseFirstPacket,firstBody,
    toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem firstPacket_counts_diff :
    toffoliCount firstPacket+504=toffoliCount (OneFlagSW.firstPacketS true) ∧
      measurementCount firstPacket+510=measurementCount (OneFlagSW.firstPacketS true) := by
  have old:=OneFlagReplay.firstPacket_counts true MappedCompressed.LaneA.laneLogical_config.1
    (MappedCompressed.LaneA.laneLogical_config.2.1 _ (by simp))
  have selected:=OneFlagSW.selFirstPacket_sel true
  have selectedT:=selected.tc
  have selectedM:=selected.mc
  have fresh:=firstPacket_counts
  simp only [if_true] at old
  constructor <;> omega

end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component KernelFootprint
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointEntryKernelFootprint
open Arithmetic MappedCompressed
attribute [local irreducible] wires CoherentTail.addPrefix Q6Structural.rawAdd Q6EndpointStructural.forwardE Q6EndpointCell.halfE

def coreSites (L : BalancedCircuit.Layout) : Finset Wire :=
 (L.r++L.y++L.carry.take 254++[L.parity,L.lower,L.one,L.sign]).toFinset

theorem prefix_sites (x y c : List Wire) (a t z cin : Wire)
 (hy:y.length=x.length) (hc:c.length=x.length) :
 wires (CoherentTail.addPrefix x y c a t z cin)=(x++y++c++[a,t,z,cin]).toFinset := by
 induction x generalizing y c cin with
 | nil=>
   have ey:y=[]:=List.eq_nil_of_length_eq_zero hy
   have ec:c=[]:=List.eq_nil_of_length_eq_zero hc
   subst y; subst c
   ext q
   simp [CoherentTail.addPrefix,CoherentTail.program,wires,Instr.wires]
   tauto
 | cons b xs ih=>
   cases y with
   | nil=>simp at hy
   | cons d ys=>
     cases c with
     | nil=>simp at hc
     | cons k ks=>
       have hy':ys.length=xs.length:=by simpa using hy
       have hc':ks.length=xs.length:=by simpa using hc
       rw [CoherentTail.addPrefix,wires_append,wires_append,wires_append,ih _ _ _ hy' hc']
       ext q
       simp [majority,eraseCarry,wires,Instr.wires,correctionWires]
       tauto

theorem core_subset_forwardE (L : BalancedCircuit.Layout) (hw : L.Widths) :
 coreSites L⊆wires (Q6EndpointStructural.forwardE L) := by
 have len:=hw.2.2
 have yw:=hw.2.1
 have rw:=hw.1
 have ct:(Q6Structural.carryLayout L).carry.take 255=L.carry.take 254++[L.lower] := by
   simp [Q6Structural.carryLayout,Q6Structural.q6Carry,List.take_append,List.length_take,len]
 have plen:((Q6Structural.carryLayout L).carry.take 255).length=L.ylow.length :=by
   rw[ct]
   simp[yw,len]
 have ylen:L.low.length=L.ylow.length:=by simp[BalancedCleanup.Layout.low,rw,yw]
 have pref:=prefix_sites L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign ylen plen
 have rawsub:wires (CoherentTail.addPrefix L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign)⊆wires (Q6Structural.rawAdd L) :=by
   simp only[Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,FieldRename.mapCircuit] at *
   intro q hq
   simp only[wires_append]
   exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
 have allsub:wires (GuardCompression.seed L)∪wires (Q6Structural.rawAdd L)⊆wires (Q6EndpointStructural.forwardE L) :=by
   intro q hq
   simp only[Q6EndpointStructural.forwardE,Q6StructuralCell.forwardPrefix,wires_append,Finset.mem_union] at hq ⊢
   tauto
 intro q hq
 apply allsub
 by_cases parity:q=L.parity
 · subst q
   exact Finset.mem_union_left _ (by simp[GuardCompression.seed,wires,Instr.wires])
 · apply Finset.mem_union_right
   apply rawsub
   rw[pref,ct]
   simp only[coreSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
     BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low] at hq ⊢
   tauto

theorem core_subset_forward (L : BalancedCircuit.Layout) (hw : L.Widths) :
 coreSites L⊆wires (Q6StructuralCell.forward L) := by
 have len:=hw.2.2
 have yw:=hw.2.1
 have rw:=hw.1
 have ct:(Q6Structural.carryLayout L).carry.take 255=L.carry.take 254++[L.lower] := by
   simp [Q6Structural.carryLayout,Q6Structural.q6Carry,List.take_append,List.length_take,len]
 have plen:((Q6Structural.carryLayout L).carry.take 255).length=L.ylow.length :=by
   rw[ct]
   simp[yw,len]
 have ylen:L.low.length=L.ylow.length:=by simp[BalancedCleanup.Layout.low,rw,yw]
 have pref:=prefix_sites L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign ylen plen
 have rawsub:wires (CoherentTail.addPrefix L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign)⊆wires (Q6Structural.rawAdd L) :=by
   simp only[Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,FieldRename.mapCircuit] at *
   intro q hq
   simp only[wires_append]
   exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
 have allsub:wires (GuardCompression.seed L)∪wires (Q6Structural.rawAdd L)⊆wires (Q6StructuralCell.forward L) :=by
   intro q hq
   simp only[Q6StructuralCell.forward,Q6StructuralCell.forwardPrefix,wires_append,Finset.mem_union] at hq ⊢
   tauto
 intro q hq
 apply allsub
 by_cases parity:q=L.parity
 · subst q
   exact Finset.mem_union_left _ (by simp[GuardCompression.seed,wires,Instr.wires])
 · apply Finset.mem_union_right
   apply rawsub
   rw[pref,ct]
   simp only[coreSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
     BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low] at hq ⊢
   tauto

theorem actual_core_subset_halfE :
 coreSites (Q6EndpointCell.ports base (base 2409))⊆wires (Q6EndpointCell.halfE true base (base 2409)) := by
 have core:=core_subset_forwardE (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths _ _)
 intro q hq
 have h:=core hq
 rw [Q6EndpointCell.halfE_true,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem actual_core_subset_half :
 coreSites (Q6EndpointCell.ports base (base 2409))⊆wires (Q6EndpointCell.half true base (base 2409)) := by
 have core:=core_subset_forward (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths _ _)
 intro q hq
 have h:=core hq
 simp only [Q6EndpointCell.half,OwnQ6Core5.half,OwnQ6Core5.kernel,if_true,wires_append,Finset.mem_union]
 exact Or.inl (Or.inr h)

theorem sites_split (J G : Wire) :
 JointEntryQ7.sites J G=coreSites (Q6EndpointCell.ports base (base 2409))∪{J,G,base 0} := by
 have eq : JointEntryQ7.ports=Q6EndpointCell.ports base (base 2409):=rfl
 have ct : JointEntryQ7.ports.carry.take 254=JointEntryQ7.carries:=rfl
 ext q
 rw [←eq]
 simp only [JointEntryQ7.sites,coreSites,ct,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
 tauto
end ECDSAAdd.Entrant.JointEntryKernelFootprint

end

section
-- Verified component KernelSupport
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 MappedCompressed BalancedField History5 JointEntryQ7
attribute [local irreducible] wires JointEntryQ7.joint JointEntryQ7.firstBody JointEntryQ7.firstPacket JointEntryQ7.logicalReplay JointEntryQ7.replay OneFlagSW.swapBody OneFlagSW.rawReplayS OneFlagSW.firstBodyS OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S field5S hostField5S

private theorem joint_46_cell_half_sub :
 wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
 intro q h
 simp only [OneFlagSW.cellS,if_true,SW.selW,wires_append,Finset.mem_union]
 tauto

private theorem joint_46_oldBody_shape :
 OneFlagSW.firstBodyS true=OneFlagSW.firstSwapS++
 (OneFlagSW.cellS true (base 1) (base 1029)++OneFlagSW.rawReplayS true remainingLetters) := by
 have rest : Replay5.restLetters=tapeLetter 1::remainingLetters:=rfl
 simp only [OneFlagSW.firstBodyS,if_true,rest]
 rw [OneFlagSW.rawReplayS]
 rfl

private theorem joint_46_half_body_sub : wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.firstBodyS true) := by
 intro q h
 have hc:=joint_46_cell_half_sub h
 rw [joint_46_oldBody_shape,wires_append,wires_append]
 exact Finset.mem_union_right _ (Finset.mem_union_left _ hc)

private theorem joint_46_extra_codec : {base 1028,base 1,base 0}⊆wires (History5.decode base 0) := by decide +kernel

private theorem joint_46_union_into_packet (D B E : Program) (C F : Finset Wire)
 (hc : C⊆wires B) (hf : F⊆wires D) : C∪F⊆wires (D++B++E) := by
 rw [wires_append,wires_append]
 exact Finset.union_subset (hc.trans ((Finset.subset_union_right).trans Finset.subset_union_left))
   (hf.trans (Finset.subset_union_left.trans Finset.subset_union_left))

private theorem joint_46_joint_base_sub : wires (joint (base 1028) (base 1))⊆wires (OneFlagSW.baseFirstPacketS true) := by
 have sub : wires (joint (base 1028) (base 1))⊆
   JointEntryKernelFootprint.coreSites (Q6EndpointCell.ports base (base 2409))∪{base 1028,base 1,base 0} := by
   simpa only [JointEntryKernelFootprint.sites_split] using joint_support (base 1028) (base 1) (by decide +kernel)
 have target := joint_46_union_into_packet (History5.decode base 0) (OneFlagSW.firstBodyS true) (History5.encode base 0)
   _ _ (JointEntryKernelFootprint.actual_core_subset_half.trans joint_46_half_body_sub) joint_46_extra_codec
 exact sub.trans target

private theorem joint_46_tail_body_sub :
 wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters)⊆
 wires (OneFlagSW.firstBodyS true) := by
 have cell : wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
   simp only [OneFlagSW.cellS,if_true,wires_append]
   exact Finset.subset_union_right
 intro q used
 rw [joint_46_oldBody_shape]
 simp only [wires_append,Finset.mem_union] at used ⊢
 rcases used with h|h
 · exact Or.inr (Or.inl (cell h))
 · exact Or.inr (Or.inr h)

private theorem joint_46_first_base_sub : wires baseFirstPacket⊆wires (OneFlagSW.baseFirstPacketS true) := by
 intro q used
 simp only [baseFirstPacket,wires_append,Finset.mem_union] at used
 rcases used with (hd|hb)|he
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [firstBody,wires_append,Finset.mem_union] at hb
   rcases hb with (hj|hs)|hr
   · exact joint_46_joint_base_sub hj
   · have htail:=joint_46_tail_body_sub (by rw [wires_append]; exact Finset.mem_union_left _ hs)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
   · have htail:=joint_46_tail_body_sub (by rw [wires_append]; exact Finset.mem_union_right _ hr)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto

private theorem joint_46_first_sub : wires firstPacket⊆wires (OneFlagSW.firstPacketS true) := by
 simpa only [firstPacket,OneFlagSW.firstPacketS,renameProgram_support] using Finset.image_subset_image joint_46_first_base_sub

private theorem joint_46_replay_sub : wires replay⊆wires (OneFlagSW.replayS true) := by
 have log : wires logicalReplay⊆wires (OneFlagSW.logicalReplayS true) := by
   intro q used
   simp only [logicalReplay,OneFlagSW.logicalReplayS,if_true,wires_append,Finset.mem_union] at used ⊢
   rcases used with (h|h)|h
   · exact Or.inl (Or.inl (joint_46_first_sub h))
   · exact Or.inl (Or.inr h)
   · exact Or.inr h
 simpa only [replay,OneFlagSW.replayS,renameProgram_support] using Finset.image_subset_image log

theorem field_subset_old : wires field5S⊆wires OneFlagEntryRaw.field5S := by
 simp only [field5S,OneFlagEntryRaw.field5S,wires_append]
 exact Finset.union_subset_union joint_46_replay_sub (Finset.Subset.refl _)

theorem hosted_subset_old : wires hostField5S⊆wires OneFlagEntryRaw.hostField5S := by
 have ren:=Finset.image_subset_image (f:=HostOB5.hostSwap) field_subset_old
 simp only [hostField5S,OneFlagEntryRaw.hostField5S,wires_append,renameProgram_support]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union ren (Finset.Subset.refl _))

theorem field5S_support : wires field5S⊆OB5Support.segSites :=
 field_subset_old.trans (OneFlagEntryRaw.selField5.sub.wires_sub.trans OneFlagEntryRaw.field_support)

theorem field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S := by
 have off : base 511∉OB5Support.segSites ∧ base 1542∉OB5Support.segSites := OB5Support.seg_host_free
 exact ⟨fun h=>off.1 (field5S_support h),fun h=>off.2 (field5S_support h)⟩

theorem field5S_control_free : base 2400∉wires field5S := fun h=>OneFlagEntryRaw.selField5.away (field_subset_old h)
theorem hostField5S_1026_free : base 1026∉wires hostField5S :=fun h=>OneFlagEntryQ5.hostField5S_free (hosted_subset_old h)
theorem hostField5S_1541_free : base 1541∉wires hostField5S :=fun h=>OneFlagEntryQ6.hostField5S_free1541 (hosted_subset_old h)
theorem hostField5S_1542_free : base 1542∉wires hostField5S :=fun h=>OwnOneFlagEntryQ7.hostField5S_free1542 (hosted_subset_old h)

theorem hostField5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) : base i∉wires hostField5S := by
 intro used
 apply OneFlagEntryOmissions.kernel_free7 i hi
 have sub : wires OneFlagEntryRaw.hostField5S⊆wires OwnOneFlagEntryQ7.kernel5S := by
   intro q hq
   simp only [OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hq)
 exact sub (hosted_subset_old used)
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component KernelGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic MappedCompressed Q5Global718
attribute [local irreducible] wires run
 OneFlagEntryRaw.kernel5 OneFlagEntryRaw.kernel5S OneFlagEntryRaw.hostField5S
 hostField5S baseKernel rawKernel kernel6S kernel5S

theorem hostField5S_control_free : base 2400∉wires hostField5S :=
 fun used=>OneFlagEntryRaw.selHostField5.away (hosted_subset_old used)

theorem baseKernel_control_free : base 2400∉wires baseKernel := by
 have f:=OwnQ5SW.renamed_first_away
 have l:=OwnQ5SW.renamed_last_away
 simpa only [baseKernel,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
  And.intro f (And.intro hostField5S_control_free l)

private theorem joint_47_replace_middle (a b p q : Program) (h : wires p⊆wires q) :
 wires (a++(p++b))⊆wires (a++(q++b)) := by
 simp only [wires_append]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))

theorem kernel_subset_old : wires kernel5S⊆wires OwnOneFlagEntryQ7.kernel5S := by
 simpa only [kernel5S,OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated] using
  joint_47_replace_middle (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6First)
   (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6Last) hostField5S OneFlagEntryRaw.hostField5S hosted_subset_old

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 kernel_subset_old.trans OwnOneFlagEntryQ7.kernel5S_support

theorem kernel5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires kernel5S := fun used=>OneFlagEntryOmissions.kernel_free7 i hi (kernel_subset_old used)
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component KernelClosed
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
 exact kernel5S_correct_of_static field5S_hosts_free hostField5S_1026_free baseKernel_control_free
  hostField5S_1541_free hostField5S_1542_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component FirstCosts

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryQ7
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines

private theorem joint_49_remaining_mem (l : MixedTranscriptLetter) (hl : l ∈ remainingLetters) :
    l ∈ Replay5.restLetters := by
  change l ∈ tapeLetter 1 :: remainingLetters
  exact List.mem_cons_of_mem _ hl

private theorem joint_49_selected_physical (source flag : Wire) (P : Program)
    (away : source ≠ flag) (physical : GatePhysical P) :
    GatePhysical (SW.selW source flag P) := by
  have head : GatePhysical [Instr.CX source flag] := by
    simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using away
  have tail : GatePhysical [Instr.measureX flag [] [Correction.Z source]] := by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  simpa only [SW.selW,gatePhysical_append] using And.intro (And.intro head physical) tail

theorem firstPacket_physical : GatePhysical firstPacket := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have pair := OneFlagReplay.base_sign_nd
  have swap : GatePhysical OneFlagSW.swapBody := by
    simpa only [OneFlagSW.swapBody] using swapRegisters_physical _ _ _ pair
  have selected := OneFlagSW.selRaw_sel true remainingLetters
    (fun l hl => OneFlagSW.selRest_nodup l (joint_49_remaining_mem l hl))
  have layout : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) remainingLetters := by
    intro l hl
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hl
    have bound:=List.mem_range'_1.mp hk
    simpa only [remainingLetters,tapeLetter] using mixedTape_getD_layout base _ _ _ cfg.2.2 k (by omega)
  have rest := OneFlagReplay.raw_physical true remainingLetters cfg.1 cfg.2.1 layout
  have body : GatePhysical firstBody := by
    simpa only [firstBody,gatePhysical_append] using
      And.intro (And.intro (joint_physical (base 1028) (base 1) (by decide +kernel) (by decide +kernel) (by decide +kernel))
        (joint_49_selected_physical (base 1029) (base 2409) OneFlagSW.swapBody (by decide +kernel) swap))
        (selected.sub.physical rest)
  have e := History5.encode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base cfg.1) 0 (by decide)
  have packet : GatePhysical baseFirstPacket := by
    simpa only [baseFirstPacket,gatePhysical_append] using And.intro (And.intro d body) e
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ packet

private theorem joint_49_selected_swap_slots :
 gateSlots (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)≤771 :=by
 have h: gateSlots OneFlagSW.swapBody=768 :=by decide +kernel
 simp only [SW.selW,gateSlots_append]
 have a:gateSlots [Instr.CX (base 1029) (base 2409)]=1 :=by rfl
 have b:gateSlots [Instr.measureX (base 2409) [] [Correction.Z (base 1029)]]=2 :=by rfl
 rw [a,b,h]

 theorem firstPacket_slots_le : gateSlots firstPacket ≤ gateSlots (OneFlagSW.firstPacketS true)+9000 := by
  have core := joint_slots (base 1028) (base 1)
  have sw := joint_49_selected_swap_slots
  have letters : Replay5.restLetters = tapeLetter 1 :: remainingLetters := rfl
  simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    OneFlagSW.firstPacketS,OneFlagSW.baseFirstPacketS,OneFlagSW.firstBodyS,if_true,letters,
    OneFlagSW.rawReplayS,gateSlots_append]
  omega
end ECDSAAdd.Entrant.JointEntryQ7

end

section
-- Verified component KernelCosts
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Challenge Baselines
attribute [local irreducible] wires toffoliCount measurementCount gateSlots
 Q7FusionPhase.q6First Q7FusionPhase.q6Last
 OneFlagEntryRaw.field5S OneFlagEntryRaw.hostField5S
 JointEntryQ7.firstPacket OneFlagSW.firstPacketS OneFlagSW.groupsS OneFlagSW.endPacketS

theorem kernel5S_counts_diff :
    toffoliCount kernel5S + 504 = toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
    measurementCount kernel5S + 510 = measurementCount OwnOneFlagEntryQ7.kernel5S := by
  have first := JointEntryQ7.firstPacket_counts_diff
  simp only [kernel5S,OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointEntryQ7.replay,JointEntryQ7.logicalReplay,
    OneFlagEntryRaw.hostField5S,OneFlagEntryRaw.field5S,OneFlagSW.replayS,OneFlagSW.logicalReplayS,
    if_true,toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem kernel5S_slots_le : gateSlots kernel5S ≤ gateSlots OwnOneFlagEntryQ7.kernel5S+9000 := by
  have first := JointEntryQ7.firstPacket_slots_le
  simp only [kernel5S,OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointEntryQ7.replay,JointEntryQ7.logicalReplay,
    OneFlagEntryRaw.hostField5S,OneFlagEntryRaw.field5S,OneFlagSW.replayS,OneFlagSW.logicalReplayS,
    if_true,gateSlots_append,rename_gateSlots]
  omega

theorem replay_physical : GatePhysical JointEntryQ7.replay := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have oldGroups := OneFlagReplay.groups_physical true 1 101 (by decide)
    cfg.1 cfg.2.1 (Replay5.letters_layouts cfg.2.2)
  have groups := (OneFlagSW.selGroups_sel true 1 101 (by decide)).sub.physical oldGroups
  have last := (OneFlagSW.selEnd_sel true).sub.physical (OneFlagReplay.endPacket_physical true)
  have logical : GatePhysical JointEntryQ7.logicalReplay := by
    simpa only [JointEntryQ7.logicalReplay,gatePhysical_append] using
      And.intro (And.intro JointEntryQ7.firstPacket_physical groups) last
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ logical

theorem field5S_physical : GatePhysical field5S := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have old := (OneFlagEntryRaw.selField5.sub.physical
    (OneFlagEntryResources.field_sub.physical (OneFlagSegment.physical true cfg.1 cfg.2.1 cfg.2.2)))
  simp only [OneFlagEntryRaw.field5S,gatePhysical_append] at old
  simpa only [field5S,gatePhysical_append] using And.intro replay_physical old.2

theorem hostField5S_physical : GatePhysical hostField5S := by
  simpa only [hostField5S] using Q5FusionFields.host_physical field5S field5S_physical

theorem kernel5S_physical : GatePhysical kernel5S := by
  have old := OwnOneFlagEntryQ7.kernel5S_physical
  simp only [OwnOneFlagEntryQ7.kernel5S,Q7FusionPhase.relocated,gatePhysical_append] at old
  simpa only [kernel5S,Q7FusionPhase.relocated,gatePhysical_append] using
    And.intro old.1 (And.intro hostField5S_physical old.2.2)
end ECDSAAdd.Entrant.JointEntryKernelQ7

end

section
-- Verified component Division

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointEntryDivisionQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem joint_51_mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires JointEntryKernelQ7.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f JointEntryKernelQ7.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [joint_51_mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [joint_51_mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [joint_51_mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := JointEntryKernelQ7.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective JointEntryKernelQ7.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (joint_51_mapped_regS f _ (run JointEntryKernelQ7.kernel5S m b).basis
      (run (renameProgram f JointEntryKernelQ7.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain JointEntryKernelQ7.kernel5S sites m t q image).trans (same q hq)



open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) JointEntryKernelQ7.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ JointEntryKernelQ7.kernel5S_support

theorem arithEntryS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithEntryS L) := by
  apply gatePhysical_rename_support (wireFn2 L) JointEntryKernelQ7.kernel5S
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (JointEntryKernelQ7.kernel5S_support ha)) b
      (ArithmeticOB5.logical_sub_old (JointEntryKernelQ7.kernel5S_support hb)) eq
  · exact JointEntryKernelQ7.kernel5S_physical

private theorem joint_51_divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem joint_51_numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem joint_51_control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    joint_51_divisor_sitesS joint_51_numerator_sitesS joint_51_control_siteS (JointEntryKernelQ7.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm


open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep

theorem fusedDivisionF_support (L : ControlledPointLayout) (hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    wires (fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    arithEntryS_support L hw⟩

theorem fusedDivisionF_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (fusedDivisionF L k) := by
  simp only [fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,arithEntryS_physical L hw hn⟩

theorem fusedDivisionF_counts_diff (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    toffoliCount (fusedDivisionF L k)+504=toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k) ∧
      measurementCount (fusedDivisionF L k)+510=measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k) := by
  have c:=JointEntryKernelQ7.kernel5S_counts_diff
  have a:=renameProgram_counts (wireFn2 L) JointEntryKernelQ7.kernel5S
  have b:=renameProgram_counts (wireFn2 L) OwnOneFlagEntryQ7.kernel5S
  simp only [fusedDivisionF,OwnOneFlagEntryQ7.fusedDivisionF,arithEntryS,OwnOneFlagEntryQ7.arithEntryS,
    toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  constructor <;> omega

theorem fusedDivisionF_slots_le (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    gateSlots (fusedDivisionF L k)≤gateSlots (OwnOneFlagEntryQ7.fusedDivisionF L k)+9000 := by
  simp only [fusedDivisionF,OwnOneFlagEntryQ7.fusedDivisionF,arithEntryS,OwnOneFlagEntryQ7.arithEntryS,
    gateSlots_append,rename_gateSlots]
  have h:=JointEntryKernelQ7.kernel5S_slots_le
  omega

private theorem joint_51_placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i k : Nat) (hi : base i∈OB5Support.logicalSites)
    (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires JointEntryKernelQ7.kernel5S) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  rw [arithEntryS,renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩:=Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (JointEntryKernelQ7.kernel5S_support used)) (base i)
    (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

private theorem joint_51_logical_mem (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem joint_51_arithEntryS_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact joint_51_placed_free L hw hn 2312 1800 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 766 766 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 765 765 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 767 767 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 1026 770 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 1541 1285 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))
  · exact joint_51_placed_free L hw hn 1542 1286 (joint_51_logical_mem _ (by simp)) rfl
      (JointEntryKernelQ7.kernel5S_free _ (by simp))

theorem fusedDivisionF_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285,1286]) (c : Fp) :
    L.core.poolWire k∉wires (fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old:=ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),joint_51_arithEntryS_free L hw hn k hk⟩

end ECDSAAdd.Entrant.JointEntryDivisionQ7

end

section
-- Verified component Actual
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointEntryActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots
 fastConstAdd fastConstNeg fastConstRefl

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.generic L (JointEntryDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.gen L (JointEntryDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy

theorem generic_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (generic L cx cy)+504=toffoliCount (OwnOneFlagActual.generic L cx cy) ∧
 measurementCount (generic L cx cy)+510=measurementCount (OwnOneFlagActual.generic L cx cy) := by
 have d:=JointEntryDivisionQ7.fusedDivisionF_counts_diff L hw hn (-cy)
 simp only [generic,OwnOneFlagActual.generic,OneFlagProducer.generic,All12Generic.generic,
  toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (gen L cx cy)+504=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
 measurementCount (gen L cx cy)+510=measurementCount (OwnOneFlagActual.gen L cx cy) := by
 have d:=generic_counts_diff L hw hn cx cy
 simp only [generic,OwnOneFlagActual.generic,OneFlagProducer.generic] at d
 simp only [gen,OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,All12Generic.mid,
  toffoliCount_append,measurementCount_append,renameProgram_counts]
 constructor <;> omega

theorem generic_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
 All12Generic.generic_sites L hw _ _ _ (JointEntryDivisionQ7.fusedDivisionF_support L hw hn)
  (OwnDiagAll12PlacedQ7.support L hw hn) (OwnOneFlagActual.exit_support L hw) cx cy

theorem sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
 rw [gen,All12Generic.gen_shape]
 exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 GatePhysical (gen L cx cy) :=
 All12Generic.gen_physical L hw hn _ _ _ (JointEntryDivisionQ7.fusedDivisionF_physical L hw hn)
  (OwnDiagAll12PlacedQ7.physical L hw hn) (OwnOneFlagExitQ7.arithExit_physical L hw hn) cx cy

theorem gen_slots_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤gateSlots (OwnOneFlagActual.gen L cx cy)+9000 := by
 have d:=JointEntryDivisionQ7.fusedDivisionF_slots_le L hw hn (-cy)
 simp only [gen,OwnOneFlagActual.gen,OneFlagProducer.gen,All12Generic.gen,All12Generic.mid,
  All12Generic.generic,gateSlots_append,rename_gateSlots]
 omega

theorem slots (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤49209000 := by
 have h:=gen_slots_diff L hw hn cx cy
 have old:=OwnOneFlagActual.slots L hw cx cy
 omega

theorem generic_free (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (k:Nat) (hk:k∈[1800,766,765,767,770,1285,1286]) (cx cy:Fp) :
 L.core.poolWire k∉wires (generic L cx cy) := by
 have bounds : 515≤k ∧ k<2613 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
 exact All12Generic.generic_free L hw hn _ _ _ k bounds
  (JointEntryDivisionQ7.fusedDivisionF_free L hw hn k hk)
  (OwnDiagAll12PlacedQ7.square_free L hw hn k hk)
  (OneFlagExitOmissions.exit_avoids L hw hn k hk) cx cy

theorem ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (logicalND : (skywalkSharedWires base).Nodup) (hlo:History5.HistoryAbove base)
 (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 {cx cy:Fp} (hc:curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
 All12Generic.genFFused_ok L hw hn _ _ _ (OwnOneFlagExitQ7.arithExit_correct L hw hn)
  (JointEntryDivisionQ7.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
  (OneFlagProducer.square_step L hw hn) hc

theorem qubits (C:Point) (cx cy:Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1592 := by
 rw [gen,All12Generic.gen_shape]
 apply GenericQ7Geometry.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy)
 · intro k hk
   exact generic_free layout layout_widths layout_nodup k (List.mem_append_left [1285,1286] hk) cx cy
 · exact generic_free layout layout_widths layout_nodup 1285 (by simp) cx cy
 · exact generic_free layout layout_widths layout_nodup 1286 (by simp) cx cy
end ECDSAAdd.Entrant.JointEntryActual

end
end FrontierJointEntry

section FrontierJointTerminal

section
-- Verified combined component CombinedReplay

/-! The new first packet with the old, unchanged forward replay suffix. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalQ7
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
attribute [local irreducible] wires History5.allEncode run measurementCount OneFlagSW.groupsS TerminalGraphSW.endPacketS

abbrev firstPacket := JointEntryQ7.firstPacket

def logicalReplay : Program :=
  firstPacket ++ TerminalGraphSW.groupsS true 1 101 ++ TerminalGraphSW.endPacketS true

def replay : Program := renameProgram (OB5.sig 511) logicalReplay

/-- The old packet uses its own record tape; the unchanged suffix keeps the new tape. -/
def oldRecords (m : List Bool) : List Bool :=
  List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false ++
    m.drop (measurementCount firstPacket)

theorem oldRecords_take (m : List Bool) :
    (oldRecords m).take (measurementCount (TerminalGraphSW.firstPacketS true))=
      List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false := by
  rw [oldRecords,List.take_append_of_le_length (by
    simpa only [List.length_replicate] using
      (Nat.le_refl (measurementCount (TerminalGraphSW.firstPacketS true))))]
  simpa only [List.length_replicate] using
    List.take_length (l:=List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false)

theorem oldRecords_drop (m : List Bool) :
    (oldRecords m).drop (measurementCount (TerminalGraphSW.firstPacketS true))=
      m.drop (measurementCount firstPacket) := by
  have nil : (List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false).drop
      (measurementCount (TerminalGraphSW.firstPacketS true))=[] := by
    simpa only [List.length_replicate] using
      List.drop_length (l:=List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false)
  rw [oldRecords,List.drop_append,List.length_replicate,nil,Nat.sub_self,List.drop_zero,List.nil_append]

private theorem encoded_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (ht : History5.EncodedFieldFrame5 base (base 2409) origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩:=hs
  obtain ⟨b,hb,fb,eb⟩:=ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem encoded_enable (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (X Y : Fp) (s : State)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    s.basis (base 2400)=true := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  have away := layout.outside (base 2400) (by simp)
  obtain ⟨raw,_,frame,encoded⟩:=input
  have unused : base 2400∉wires (History5.allEncode base 102) := by
    intro used
    have support : wires (History5.allEncode base 102)⊆(skywalkPoolWires base).toFinset := HalfField5.encoder_pool_support
    have pool : base 2400∈skywalkPoolWires base := List.mem_toFinset.mp (support used)
    exact ctx.hp (base 2400) (by simp) pool
  rw [encoded,run_preserves_outside _ [] raw _ unused]
  exact (frame.2.2 _ away.1 away.2).trans hb

/-- Both packet record tapes are arbitrary and independent. -/
theorem firstPacket_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (mNew mOld : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run firstPacket mNew s=run (TerminalGraphSW.firstPacketS true) mOld s := by
  have fresh := JointEntryQ7.firstPacket_frame origin ctx hb Z s mNew input
  have old := OneFlagReplay.firstPacket_frame true origin ctx Z 0 s mOld input (by simp)
  have eq := (OneFlagSW.selFirstPacket_sel true).eq mOld s (encoded_enable origin ctx hb Z 0 s input)
  rw [←eq.1] at old
  exact encoded_unique origin _ _ _ _ fresh.2 old.2 (fresh.1.trans old.1.symm)

/-- Only the old first-packet tape is padded. The groups and end packet are unchanged. -/
theorem logical_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Z 0 s) :
    run logicalReplay m s=run (TerminalGraphSW.logicalReplayS true) (oldRecords m) s := by
  have first := firstPacket_compare origin ctx hb Z s (m.take (measurementCount firstPacket))
    (List.replicate (measurementCount (TerminalGraphSW.firstPacketS true)) false) input
  have freshShape : logicalReplay=firstPacket++(TerminalGraphSW.groupsS true 1 101++TerminalGraphSW.endPacketS true) := by
    simp only [logicalReplay,List.append_assoc]
  have oldShape : TerminalGraphSW.logicalReplayS true=TerminalGraphSW.firstPacketS true++(TerminalGraphSW.groupsS true 1 101++TerminalGraphSW.endPacketS true) := by
    simp only [TerminalGraphSW.logicalReplayS,if_true,List.append_assoc]
  rw [freshShape,oldShape]
  simp only [run_append,oldRecords_take,oldRecords_drop]
  rw [first]

/-- The same record builder works after the final sig511 field placement. -/
theorem replay_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run replay m s=run (TerminalGraphSW.replayS true) (oldRecords m) s := by
  have localEq := logical_compare origin ctx hb Z (pullState (OB5.sig 511) s) m input
  have fresh := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) logicalReplay m s
  have old := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (TerminalGraphSW.logicalReplayS true) (oldRecords m) s
  have eq := congrArg (pullState (OB5.sig 511)) (fresh.trans (localEq.trans old.symm))
  simpa only [OB5.pull_invol 511 (by decide),replay,TerminalGraphSW.replayS] using eq

end ECDSAAdd.Entrant.JointTerminalQ7

end

section
-- Verified combined component CombinedKernelProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
def field5S : Program := JointTerminalQ7.replay ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def rawKernel : Program := Q5FusionPhase.kernel hostField5S
def baseKernel : Program := Q5FusionPhase.relocated hostField5S
def kernel6S : Program := Q6FusionPhase.relocated hostField5S
def kernel5S : Program := Q7FusionPhase.relocated hostField5S
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedRecordCounts
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket



theorem old_replay_count_shape :
 measurementCount (TerminalGraphSW.replayS true)=measurementCount (OneFlagSW.firstPacketS true)+
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) := by
 unfold TerminalGraphSW.replayS
 rw [(renameProgram_counts (OB5.sig 511) (TerminalGraphSW.logicalReplayS true)).2]
 simp only [TerminalGraphSW.logicalReplayS,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,if_true,measurementCount_append,Nat.add_assoc]



theorem new_replay_count_shape :
 measurementCount JointTerminalQ7.replay=measurementCount JointEntryQ7.firstPacket+
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) := by
 unfold JointTerminalQ7.replay
 rw [(renameProgram_counts (OB5.sig 511) JointTerminalQ7.logicalReplay).2]
 simp only [JointTerminalQ7.logicalReplay,JointTerminalQ7.firstPacket,TerminalGraphSW.groupsS,measurementCount_append,Nat.add_assoc]



private theorem drop_pad (a b c : Nat) (m : List Bool) :
 (List.replicate a false ++m.drop b).drop (a+c)=m.drop (b+c) := by
 have nil : (List.replicate a false).drop (a+c)=[] :=
  List.drop_eq_nil_iff.mpr (by simp only [List.length_replicate];omega)
 rw [List.drop_append,List.length_replicate,nil]
 simp only [Nat.add_sub_cancel_left,List.nil_append,List.drop_drop]

theorem replay_records_drop (m : List Bool) :
    (JointTerminalQ7.oldRecords m).drop (measurementCount (TerminalGraphSW.replayS true))=
      m.drop (measurementCount JointTerminalQ7.replay) := by
 conv_lhs => rw [old_replay_count_shape]
 conv_rhs => rw [new_replay_count_shape]
 simpa only [JointTerminalQ7.oldRecords,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS] using
  drop_pad (measurementCount (OneFlagSW.firstPacketS true)) (measurementCount JointEntryQ7.firstPacket)
   (measurementCount (OneFlagSW.groupsS true 1 101)+measurementCount (TerminalGraphSW.endPacketS true)) m

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldTransferPrefix
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

theorem field_compare (origin : BasisState) (ctx : OneFlagReplay.Context origin)
    (hb : origin (base 2400)=true) (Z : Fp) (s : State) (m : List Bool)
    (input : FieldFrameOB5.EncodedFieldFrame origin Z 0 s) :
    run field5S m s=run TerminalGraphEntryRaw.field5S (JointTerminalQ7.oldRecords m) s := by
  have eq:=JointTerminalQ7.replay_compare origin ctx hb Z s m input
  simp only [field5S,TerminalGraphEntryRaw.field5S,run_append,run_take]
  rw [eq,replay_records_drop]

theorem hosted_compare (P Q : Program) (s : State) (m n : List Bool)
    (pf : base 511∉wires P) (qf : base 511∉wires Q)
    (sg : s.basis (base 2409)=false) (hg : s.basis (base 511)=true)
    (se : s.basis (base 2410)=false) (he : s.basis (base 1542)=false)
    (eq : run P m s=run Q n s) :
    run ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)])) m s=
      run ([.X (base 511)]++(renameProgram HostOB5.hostSwap Q++[.X (base 511)])) n s := by
  let X:Program := [.X (base 511)]
  let u:=run X [] s
  have dis (R : Program) (hr : base 511∉wires R) : Disjoint (wires X) (wires R) := by
    apply Finset.disjoint_left.mpr
    intro q hq used
    have e:q=base 511 := by simpa only [X,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton] using hq
    exact hr (e ▸ used)
  have cp:=run_disjoint_commute X P (dis P pf) [] m s
  have cq:=run_disjoint_commute X Q (dis Q qf) [] n s
  have equal : run P m u=run Q n u := cp.symm.trans ((congrArg (run X []) eq).trans cq)
  have pull : pullState HostOB5.hostSwap u=u := by
    apply HostOB5.host_pull
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2409)=!s.basis (base 511)
      rw [sg,hg];rfl
    · simp [u,X,run,writeBit,Function.update,base]
      change s.basis (base 2410)=s.basis (base 1542)
      rw [se,he]
  have rp:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective P m u
  have rq:=ECDSAAdd.run_rename HostOB5.hostSwap HostOB5.hostSwap_injective Q n u
  rw [pull] at rp rq
  have ren : run (renameProgram HostOB5.hostSwap P) m u=run (renameProgram HostOB5.hostSwap Q) n u := by
    have e:=congrArg (pullState HostOB5.hostSwap) (rp.trans (equal.trans rq.symm))
    simpa only [pullState,HostOB5.hostSwap_invol] using e
  have records (r : List Bool) (t : State) : run X r t=run X [] t := by simp only[X,run]
  simpa only [X,u,run_append,measurementCount,List.take_zero,List.drop_zero,run_take,run] using
    congrArg (run X []) ren

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldReady
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S
 TerminalGraphEntryRaw.field5

theorem field_from_ready
 (hostFree : base 511∉wires field5S) (origin : BasisState) (ctx : OneFlagReplay.Context origin)
 (enabled : origin (base 2400)=true) (Z : Fp) (a3 v3 : State) (m : List Bool)
 (frame : FieldFrameOB5.EncodedFieldFrame origin Z 0 v3)
 (paired : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (selectors : a3.basis (base 2409)=false ∧ a3.basis (base 2410)=false)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false) :
 run hostField5S m v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have unhosted : run field5S m v3=run TerminalGraphEntryRaw.field5S (JointTerminalQ7.oldRecords m) v3 :=
  field_compare origin ctx enabled Z v3 m frame
 have outside (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 :=
  OwnPlusHost.not_block i 2056 256 (by omega)
 have keep (i : Nat) (hi : i<2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
  (paired _ (outside i hi)).symm
 have oldSubset : wires TerminalGraphEntryRaw.field5S⊆wires TerminalGraphEntryRaw.field5 :=
  TerminalGraphEntryRaw.selField5.sub.wires_sub
 have oldAway : base 511∉wires TerminalGraphEntryRaw.field5 := TerminalGraphEntryRaw.field_free.1
 have oldFree : base 511∉wires TerminalGraphEntryRaw.field5S := fun used=>oldAway (oldSubset used)
 have compared:=hosted_compare field5S TerminalGraphEntryRaw.field5S v3 m (JointTerminalQ7.oldRecords m)
  hostFree oldFree ((keep 2409 (by omega)).trans selectors.1)
  ((keep 511 (by omega)).trans hosts.1) ((keep 2410 (by omega)).trans selectors.2)
  ((keep 1542 (by omega)).trans hosts.2) unhosted
 have on:=JointTerminalQ7.encoded_enable origin ctx enabled Z 0 (pullState (OB5.sig 511) v3) frame
 have sigb : OB5.sig 511 (base 2400)=base 2400 := by decide
 refine ⟨?_,?_⟩
 · simpa only [hostField5S,TerminalGraphEntryRaw.hostField5S] using compared
 · simpa only [pullState,sigb] using on
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedFieldFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5 Q5Global718
attribute [local irreducible] run wires field5S hostField5S TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S

theorem field_from_facts (hostFree : base 511∉wires field5S)
 (hn : (skywalkSharedWires base).Nodup)
 (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 (x : Nat) (Y : Fp) (s origin a3 v3 : State) (m : List Bool)
 (facts : PreparationFacts x Y s origin) (legal : History5.RawLegal base 102 origin.basis)
 (canonical : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3)
 (hosts : a3.basis (base 511)=true ∧ a3.basis (base 1542)=false)
 (phase : a3.phase=v3.phase)
 (same : ∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q)
 (target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2))
 (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
 (hb : s.basis (base 2400)=true) :
 run hostField5S m v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m) v3 ∧
 v3.basis (base 2400)=true := by
 have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
  intro q hq bad
  exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
 have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
 have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
 have enabled : origin.basis (base 2400)=true := (facts.controls _ (by simp)).trans hb
 have frame:=JointEntryPrepared.retarget hn origin.basis facts.targetHigh facts.sourceHigh Y a3 v3 phase same target canonical
 let ctx : OneFlagReplay.Context origin.basis := ⟨hn,ho,hp,hf,hg,hs,facts.env,legal,facts.targetHigh⟩
 have selectors:=EntryFuse.encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 canonical
 exact field_from_ready hostFree origin.basis ctx enabled (Y/2) a3 v3 m frame same selectors hosts
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedStateCompare
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

theorem field_state_compare
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) (v1 v2 v3 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run stackForwardT m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3) :
    run hostField5S m4 v3=run TerminalGraphEntryRaw.hostField5S (JointTerminalQ7.oldRecords m4) v3 ∧
      v3.basis (base 2400)=true := by
  generalize ha1 : run (NativeFirstDirect.forward base) m1 s = a1
  generalize ha2 : run stackForwardT m2 a1 = a2
  generalize ha3 : run (skywalkArithmeticClear base) m3 a2 = a3
  have paired:=JointEntryPrepared.paired_prefix s t a1 a2 a3 v1 v2 v3 m1 m2 m3
    phase same ha1 ha2 ha3 h1 h2 h3
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) :=
    (regValue_congr _ _ _ paired.2.2).trans value
  obtain ⟨origin,facts,legal,canonical,hosts⟩:=JointEntryPrepared.canonical_prefix hn hlo ho
    x Y hx0 hx s m1 m2 m3 hin a1 a2 a3 ha1 ha2 ha3
  exact field_from_facts field5S_hosts_free.1 hn ho hf x Y s origin a3 v3 m4 facts legal canonical hosts
    paired.1 paired.2.1 target hg0 hs0 hb

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedEnabledKernel
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free

theorem enabled_kernel_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5S) m t) := by
  let P : State→State→Prop := fun initial out=>initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all:=skywalkRunSeven (NativeFirstDirect.forward base) stackForwardT (skywalkArithmeticClear base)
    hostField5S (skywalkArithmeticClear base) stackReverseT (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 ph sm val
      have pair:=field_state_compare field5S_hosts_free hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 hin hg0 hs0
        ph sm val hb v1 v2 v3 h1 h2 h3
      have selected:=(TerminalGraphEntryRaw.selHostField5.eq (JointTerminalQ7.oldRecords m4) v3 pair.2).1
      have old4 : run TerminalGraphEntryRaw.hostField5 (JointTerminalQ7.oldRecords m4) v3=v4 := by
        have e:=pair.1.symm.trans h4
        rw [selected] at e
        simpa only [TerminalGraphEntryRaw.hostField5,TerminalGraphEntryRaw.field5,EntryFuse.hostField5,EntryFuse.field5] using e
      exact TerminalGraphEntryRaw.kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3
        (JointTerminalQ7.oldRecords m4) m5 m6 m7 hin hg0 hs0 ph sm val
        v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 old4 h5 h6 h7) t m
  simpa only [Q5FusionPhase.kernel,firstPhase,lastPhase,List.append_assoc] using all phase same value

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedEnabledBase
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free

theorem enabled_base_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase) (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (hb : s.basis (base 2400)=true) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run baseKernel m t) := by
  have old:=enabled_kernel_correct field5S_hosts_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value hb
  have eq:=Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5S true
    hin same hostField5S_1026_free old
  rw [baseKernel,eq]
  exact old


end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedBaseCorrect
/-! Transfer the prepared fused numerator through the new entry replay. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedFieldSupport
  OffsetBorrowedCanonical BalancedField History5 Q5Global718
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
attribute [local irreducible] SkywalkTrace.trace SkywalkTrace.next Nat.iterate
  mixedTranscriptUnitTrace skywalkTapeControls skywalkSharedTape
attribute [local irreducible] run wires measurementCount field5S hostField5S baseKernel
  Q5FusionPhase.kernel Q5FusionPhase.relocated firstPhase lastPhase OneFlagSW.groupsS TerminalGraphSW.endPacketS
  TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S TerminalGraphEntryRaw.field5 TerminalGraphEntryRaw.hostField5
  TerminalGraphEntryRaw.kernel5 TerminalGraphSW.replayS JointTerminalQ7.replay JointTerminalQ7.logicalReplay
  TerminalGraphSW.logicalReplayS OneFlagSW.firstPacketS JointEntryQ7.firstPacket

include field5S_hosts_free hostField5S_1026_free baseKernel_control_free

theorem base_kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out:=run baseKernel m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := EntryFuse.forceControl5 s
  let b := EntryFuse.forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact EntryFuse.forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [EntryFuse.forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (EntryFuse.forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := EntryFuse.forceControl5_true s
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [EntryFuse.forceControl5_true,EntryFuse.forceControl5_true]
    · rw [EntryFuse.forceControl5_keep t q e,EntryFuse.forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact EntryFuse.forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong:=enabled_base_correct field5S_hosts_free hostField5S_1026_free hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half ab
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree:=pool_run_agrees baseKernel (wires baseKernel) (Finset.Subset.refl _) m t b rfl
    (fun q hq=>(EntryFuse.forceControl5_keep t q (fun e=>baseKernel_control_free (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run baseKernel m t).basis q=(run baseKernel m b).basis q := by
    by_cases used:q∈wires baseKernel
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (EntryFuse.forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e=>numAway (e ▸ hq))
  · intro q hq
    by_cases e:q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ baseKernel_control_free).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (EntryFuse.forceControl5_keep s q e))

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
section StaticPremises
variable (field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S)
variable (hostField5S_1026_free : base 1026∉wires hostField5S)
variable (baseKernel_control_free : base 2400∉wires baseKernel)
variable (hostField5S_1541_free : base 1541∉wires hostField5S)
variable (hostField5S_1542_free : base 1542∉wires hostField5S)
attribute [local irreducible] run wires kernel5S kernel6S baseKernel hostField5S

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free
theorem kernel6S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel6S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=base_kernel5S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q6FusionPhase.kernel hostField5S=baseKernel :=
    by simpa only [baseKernel] using Q6FusionGeometry.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1541_free frame
  simpa only [kernel6S,eq,shape] using old

/- Relocate the integer phases only after the field stage has restored both loan sites. -/
include hostField5S_1542_free
theorem kernel5S_correct_of_static
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=kernel6S_correct field5S_hosts_free hostField5S_1026_free baseKernel_control_free hostField5S_1541_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have shape : Q7FusionPhase.kernel hostField5S=kernel6S :=
    by simpa only [kernel6S] using Q7FusionPhase.old_shape hostField5S
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [shape] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S hin same
    hostField5S_1542_free frame
  simpa only [kernel5S,eq,shape] using old

end StaticPremises
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelSupport
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed BalancedField History5 JointEntryQ7
attribute [local irreducible] wires JointEntryQ7.joint JointEntryQ7.firstBody JointEntryQ7.firstPacket JointTerminalQ7.logicalReplay JointTerminalQ7.replay OneFlagSW.swapBody OneFlagSW.rawReplayS OneFlagSW.firstBodyS TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S field5S hostField5S

private theorem cell_half_sub :
 wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
 intro q h
 simp only [OneFlagSW.cellS,if_true,SW.selW,wires_append,Finset.mem_union]
 tauto

private theorem oldBody_shape :
 OneFlagSW.firstBodyS true=OneFlagSW.firstSwapS++
 (OneFlagSW.cellS true (base 1) (base 1029)++OneFlagSW.rawReplayS true remainingLetters) := by
 have rest : Replay5.restLetters=tapeLetter 1::remainingLetters:=rfl
 simp only [OneFlagSW.firstBodyS,if_true,rest]
 rw [OneFlagSW.rawReplayS]
 rfl

private theorem half_body_sub : wires (Q6EndpointCell.half true base (base 2409))⊆wires (OneFlagSW.firstBodyS true) := by
 intro q h
 have hc:=cell_half_sub h
 rw [oldBody_shape,wires_append,wires_append]
 exact Finset.mem_union_right _ (Finset.mem_union_left _ hc)

private theorem extra_codec : {base 1028,base 1,base 0}⊆wires (History5.decode base 0) := by decide +kernel

private theorem union_into_packet (D B E : Program) (C F : Finset Wire)
 (hc : C⊆wires B) (hf : F⊆wires D) : C∪F⊆wires (D++B++E) := by
 rw [wires_append,wires_append]
 exact Finset.union_subset (hc.trans ((Finset.subset_union_right).trans Finset.subset_union_left))
   (hf.trans (Finset.subset_union_left.trans Finset.subset_union_left))

private theorem joint_base_sub : wires (joint (base 1028) (base 1))⊆wires (OneFlagSW.baseFirstPacketS true) := by
 have sub : wires (joint (base 1028) (base 1))⊆
   JointEntryKernelFootprint.coreSites (Q6EndpointCell.ports base (base 2409))∪{base 1028,base 1,base 0} := by
   simpa only [JointEntryKernelFootprint.sites_split] using joint_support (base 1028) (base 1) (by decide +kernel)
 have target := union_into_packet (History5.decode base 0) (OneFlagSW.firstBodyS true) (History5.encode base 0)
   _ _ (JointEntryKernelFootprint.actual_core_subset_half.trans half_body_sub) extra_codec
 exact sub.trans target

private theorem tail_body_sub :
 wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody++OneFlagSW.rawReplayS true remainingLetters)⊆
 wires (OneFlagSW.firstBodyS true) := by
 have cell : wires (SW.selW (base 1029) (base 2409) OneFlagSW.swapBody)⊆wires (OneFlagSW.cellS true (base 1) (base 1029)) := by
   simp only [OneFlagSW.cellS,if_true,wires_append]
   exact Finset.subset_union_right
 intro q used
 rw [oldBody_shape]
 simp only [wires_append,Finset.mem_union] at used ⊢
 rcases used with h|h
 · exact Or.inr (Or.inl (cell h))
 · exact Or.inr (Or.inr h)

private theorem first_base_sub : wires baseFirstPacket⊆wires (OneFlagSW.baseFirstPacketS true) := by
 intro q used
 simp only [baseFirstPacket,wires_append,Finset.mem_union] at used
 rcases used with (hd|hb)|he
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [firstBody,wires_append,Finset.mem_union] at hb
   rcases hb with (hj|hs)|hr
   · exact joint_base_sub hj
   · have htail:=tail_body_sub (by rw [wires_append]; exact Finset.mem_union_left _ hs)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
   · have htail:=tail_body_sub (by rw [wires_append]; exact Finset.mem_union_right _ hr)
     simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto
 · simp only [OneFlagSW.baseFirstPacketS,wires_append,Finset.mem_union];tauto

private theorem first_sub : wires firstPacket⊆wires (TerminalGraphSW.firstPacketS true) := by
 simpa only [firstPacket,TerminalGraphSW.firstPacketS,OneFlagSW.firstPacketS,renameProgram_support] using Finset.image_subset_image first_base_sub

private theorem replay_sub : wires JointTerminalQ7.replay⊆wires (TerminalGraphSW.replayS true) := by
 have log : wires JointTerminalQ7.logicalReplay⊆wires (TerminalGraphSW.logicalReplayS true) := by
   intro q used
   simp only [JointTerminalQ7.logicalReplay,TerminalGraphSW.logicalReplayS,if_true,wires_append,Finset.mem_union] at used ⊢
   rcases used with (h|h)|h
   · exact Or.inl (Or.inl (first_sub h))
   · exact Or.inl (Or.inr h)
   · exact Or.inr h
 simpa only [JointTerminalQ7.replay,TerminalGraphSW.replayS,renameProgram_support] using Finset.image_subset_image log

theorem field_subset_old : wires field5S⊆wires TerminalGraphEntryRaw.field5S := by
 simp only [field5S,TerminalGraphEntryRaw.field5S,wires_append]
 exact Finset.union_subset_union replay_sub (Finset.Subset.refl _)

theorem hosted_subset_old : wires hostField5S⊆wires TerminalGraphEntryRaw.hostField5S := by
 have ren:=Finset.image_subset_image (f:=HostOB5.hostSwap) field_subset_old
 simp only [hostField5S,TerminalGraphEntryRaw.hostField5S,wires_append,renameProgram_support]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union ren (Finset.Subset.refl _))

theorem field5S_support : wires field5S⊆OB5Support.segSites :=
 field_subset_old.trans (TerminalGraphEntryRaw.selField5.sub.wires_sub.trans TerminalGraphEntryRaw.field_support)

theorem field5S_hosts_free : base 511∉wires field5S ∧ base 1542∉wires field5S := by
 have off : base 511∉OB5Support.segSites ∧ base 1542∉OB5Support.segSites := OB5Support.seg_host_free
 exact ⟨fun h=>off.1 (field5S_support h),fun h=>off.2 (field5S_support h)⟩

theorem field5S_control_free : base 2400∉wires field5S := fun h=>TerminalGraphEntryRaw.selField5.away (field_subset_old h)
theorem hostField5S_1026_free : base 1026∉wires hostField5S :=fun h=>TerminalGraphEntryQ5.hostField5S_free (hosted_subset_old h)
theorem hostField5S_1541_free : base 1541∉wires hostField5S :=fun h=>TerminalGraphEntryQ6.hostField5S_free1541 (hosted_subset_old h)
theorem hostField5S_1542_free : base 1542∉wires hostField5S :=fun h=>OwnTerminalGraphEntryQ7.hostField5S_free1542 (hosted_subset_old h)

theorem hostField5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) : base i∉wires hostField5S := by
 intro used
 apply TerminalGraphEntryOmissions.kernel_free7 i hi
 have sub : wires TerminalGraphEntryRaw.hostField5S⊆wires OwnTerminalGraphEntryQ7.kernel5S := by
   intro q hq
   simp only [OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hq)
 exact sub (hosted_subset_old used)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic MappedCompressed Q5Global718
attribute [local irreducible] wires run
 TerminalGraphEntryRaw.kernel5 TerminalGraphEntryRaw.kernel5S TerminalGraphEntryRaw.hostField5S
 hostField5S baseKernel rawKernel kernel6S kernel5S

theorem hostField5S_control_free : base 2400∉wires hostField5S :=
 fun used=>TerminalGraphEntryRaw.selHostField5.away (hosted_subset_old used)

theorem baseKernel_control_free : base 2400∉wires baseKernel := by
 have f:=OwnQ5SW.renamed_first_away
 have l:=OwnQ5SW.renamed_last_away
 simpa only [baseKernel,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
  And.intro f (And.intro hostField5S_control_free l)

private theorem replace_middle (a b p q : Program) (h : wires p⊆wires q) :
 wires (a++(p++b))⊆wires (a++(q++b)) := by
 simp only [wires_append]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))

theorem kernel_subset_old : wires kernel5S⊆wires OwnTerminalGraphEntryQ7.kernel5S := by
 simpa only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated] using
  replace_middle (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6First)
   (renameProgram Q7IntegerHost.swap Q7FusionPhase.q6Last) hostField5S TerminalGraphEntryRaw.hostField5S hosted_subset_old

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 kernel_subset_old.trans OwnTerminalGraphEntryQ7.kernel5S_support

theorem kernel5S_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires kernel5S := fun used=>TerminalGraphEntryOmissions.kernel_free7 i hi (kernel_subset_old used)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelClosed
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
 exact kernel5S_correct_of_static field5S_hosts_free hostField5S_1026_free baseKernel_control_free
  hostField5S_1541_free hostField5S_1542_free hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedKernelCosts
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalKernelQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Challenge Baselines
attribute [local irreducible] wires toffoliCount measurementCount gateSlots
 Q7FusionPhase.q6First Q7FusionPhase.q6Last
 TerminalGraphEntryRaw.field5S TerminalGraphEntryRaw.hostField5S
 JointEntryQ7.firstPacket OneFlagSW.firstPacketS OneFlagSW.groupsS TerminalGraphSW.endPacketS

theorem kernel5S_counts_diff :
    toffoliCount kernel5S + 504 = toffoliCount OwnTerminalGraphEntryQ7.kernel5S ∧
    measurementCount kernel5S + 510 = measurementCount OwnTerminalGraphEntryQ7.kernel5S := by
  have first := JointEntryQ7.firstPacket_counts_diff
  simp only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointTerminalQ7.replay,JointTerminalQ7.logicalReplay,
    TerminalGraphEntryRaw.hostField5S,TerminalGraphEntryRaw.field5S,TerminalGraphSW.replayS,TerminalGraphSW.logicalReplayS,
    if_true,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem kernel5S_slots_le : gateSlots kernel5S ≤ gateSlots OwnTerminalGraphEntryQ7.kernel5S+9000 := by
  have first := JointEntryQ7.firstPacket_slots_le
  simp only [kernel5S,OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,
    hostField5S,field5S,JointTerminalQ7.replay,JointTerminalQ7.logicalReplay,
    TerminalGraphEntryRaw.hostField5S,TerminalGraphEntryRaw.field5S,TerminalGraphSW.replayS,TerminalGraphSW.logicalReplayS,
    if_true,JointTerminalQ7.firstPacket,TerminalGraphSW.firstPacketS,TerminalGraphSW.groupsS,gateSlots_append,rename_gateSlots]
  omega

theorem replay_physical : GatePhysical JointTerminalQ7.replay := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have oldGroups := OneFlagReplay.groups_physical true 1 101 (by decide)
    cfg.1 cfg.2.1 (Replay5.letters_layouts cfg.2.2)
  have groups := (OneFlagSW.selGroups_sel true 1 101 (by decide)).sub.physical oldGroups
  have last := (TerminalGraphSW.selEnd_sel TerminalGraphSupport.half_subset true).sub.physical (TerminalGraphReplay.endPacket_physical true)
  have logical : GatePhysical JointTerminalQ7.logicalReplay := by
    simpa only [JointTerminalQ7.logicalReplay,gatePhysical_append] using
      And.intro (And.intro JointEntryQ7.firstPacket_physical groups) last
  exact gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ logical

theorem field5S_physical : GatePhysical field5S := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have old := (TerminalGraphEntryRaw.selField5.sub.physical
    (TerminalGraphEntryResources.field_sub.physical (TerminalGraphSegment.physical true cfg.1 cfg.2.1 cfg.2.2)))
  simp only [TerminalGraphEntryRaw.field5S,gatePhysical_append] at old
  simpa only [field5S,gatePhysical_append] using And.intro replay_physical old.2

theorem hostField5S_physical : GatePhysical hostField5S := by
  simpa only [hostField5S] using Q5FusionFields.host_physical field5S field5S_physical

theorem kernel5S_physical : GatePhysical kernel5S := by
  have old := OwnTerminalGraphEntryQ7.kernel5S_physical
  simp only [OwnTerminalGraphEntryQ7.kernel5S,Q7FusionPhase.relocated,gatePhysical_append] at old
  simpa only [kernel5S,Q7FusionPhase.relocated,gatePhysical_append] using
    And.intro old.1 (And.intro hostField5S_physical old.2.2)
end ECDSAAdd.Entrant.JointTerminalKernelQ7

end

section
-- Verified combined component CombinedDivision

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointTerminalDivisionQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires JointTerminalKernelQ7.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f JointTerminalKernelQ7.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := JointTerminalKernelQ7.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective JointTerminalKernelQ7.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run JointTerminalKernelQ7.kernel5S m b).basis
      (run (renameProgram f JointTerminalKernelQ7.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain JointTerminalKernelQ7.kernel5S sites m t q image).trans (same q hq)



open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) JointTerminalKernelQ7.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ JointTerminalKernelQ7.kernel5S_support

theorem arithEntryS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithEntryS L) := by
  apply gatePhysical_rename_support (wireFn2 L) JointTerminalKernelQ7.kernel5S
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support ha)) b
      (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support hb)) eq
  · exact JointTerminalKernelQ7.kernel5S_physical

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (JointTerminalKernelQ7.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm


open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep

theorem fusedDivisionF_support (L : ControlledPointLayout) (hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    wires (fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    arithEntryS_support L hw⟩

theorem fusedDivisionF_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (fusedDivisionF L k) := by
  simp only [fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,arithEntryS_physical L hw hn⟩

theorem fusedDivisionF_counts_diff (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    toffoliCount (fusedDivisionF L k)+504=toffoliCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k) ∧
      measurementCount (fusedDivisionF L k)+510=measurementCount (OwnTerminalGraphEntryQ7.fusedDivisionF L k) := by
  have c:=JointTerminalKernelQ7.kernel5S_counts_diff
  have a:=renameProgram_counts (wireFn2 L) JointTerminalKernelQ7.kernel5S
  have b:=renameProgram_counts (wireFn2 L) OwnTerminalGraphEntryQ7.kernel5S
  simp only [fusedDivisionF,OwnTerminalGraphEntryQ7.fusedDivisionF,arithEntryS,OwnTerminalGraphEntryQ7.arithEntryS,
    toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  constructor <;> omega

theorem fusedDivisionF_slots_le (L : ControlledPointLayout) (_hw : L.Widths)
    (_hn : L.wires.Nodup) (k : Fp) :
    gateSlots (fusedDivisionF L k)≤gateSlots (OwnTerminalGraphEntryQ7.fusedDivisionF L k)+9000 := by
  simp only [fusedDivisionF,OwnTerminalGraphEntryQ7.fusedDivisionF,arithEntryS,OwnTerminalGraphEntryQ7.arithEntryS,
    gateSlots_append,rename_gateSlots]
  have h:=JointTerminalKernelQ7.kernel5S_slots_le
  omega

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i k : Nat) (hi : base i∈OB5Support.logicalSites)
    (hm : wireFn2 L (base i)=L.core.poolWire k)
    (free : base i∉wires JointTerminalKernelQ7.kernel5S) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  rw [arithEntryS,renameProgram_support]
  intro h
  obtain ⟨old,used,eq⟩:=Finset.mem_image.mp h
  have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
  have back:=(placement2 L hw hn).injectiveOnSlots old
    (ArithmeticOB5.logical_sub_old (JointTerminalKernelQ7.kernel5S_support used)) (base i)
    (ArithmeticOB5.logical_sub_old hi) mapped
  exact free (back ▸ used)

private theorem logical_mem (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
    base i∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

private theorem arithEntryS_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
    L.core.poolWire k∉wires (arithEntryS L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact placed_free L hw hn 2312 1800 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 766 766 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 765 765 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 767 767 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1026 770 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1541 1285 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))
  · exact placed_free L hw hn 1542 1286 (logical_mem _ (by simp)) rfl
      (JointTerminalKernelQ7.kernel5S_free _ (by simp))

theorem fusedDivisionF_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285,1286]) (c : Fp) :
    L.core.poolWire k∉wires (fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old:=ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),arithEntryS_free L hw hn k hk⟩

end ECDSAAdd.Entrant.JointTerminalDivisionQ7

end

section
-- Verified combined component CombinedActual
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.JointTerminalActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots
 fastConstAdd fastConstNeg fastConstRefl

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.generic L (JointTerminalDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
 All12Generic.gen L (JointTerminalDivisionQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L)
  (OwnOneFlagExitQ7.arithExit L) cx cy

theorem generic_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (generic L cx cy)+504=toffoliCount (OwnTerminalGraphActual.generic L cx cy) ∧
 measurementCount (generic L cx cy)+510=measurementCount (OwnTerminalGraphActual.generic L cx cy) := by
 have d:=JointTerminalDivisionQ7.fusedDivisionF_counts_diff L hw hn (-cy)
 simp only [generic,OwnTerminalGraphActual.generic,TerminalGraphProducer.generic,All12Generic.generic,
  toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_counts_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 toffoliCount (gen L cx cy)+504=toffoliCount (OwnTerminalGraphActual.gen L cx cy) ∧
 measurementCount (gen L cx cy)+510=measurementCount (OwnTerminalGraphActual.gen L cx cy) := by
 have d:=generic_counts_diff L hw hn cx cy
 simp only [generic,OwnTerminalGraphActual.generic,TerminalGraphProducer.generic] at d
 simp only [gen,OwnTerminalGraphActual.gen,TerminalGraphProducer.gen,All12Generic.gen,All12Generic.mid,
  toffoliCount_append,measurementCount_append,renameProgram_counts]
 constructor <;> omega

theorem generic_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
 All12Generic.generic_sites L hw _ _ _ (JointTerminalDivisionQ7.fusedDivisionF_support L hw hn)
  (OwnDiagAll12PlacedQ7.support L hw hn) (OwnTerminalGraphActual.exit_support L hw) cx cy

theorem sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
 rw [gen,All12Generic.gen_shape]
 exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 GatePhysical (gen L cx cy) :=
 All12Generic.gen_physical L hw hn _ _ _ (JointTerminalDivisionQ7.fusedDivisionF_physical L hw hn)
  (OwnDiagAll12PlacedQ7.physical L hw hn) (OwnOneFlagExitQ7.arithExit_physical L hw hn) cx cy

theorem gen_slots_diff (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤gateSlots (OwnTerminalGraphActual.gen L cx cy)+9000 := by
 have d:=JointTerminalDivisionQ7.fusedDivisionF_slots_le L hw hn (-cy)
 simp only [gen,OwnTerminalGraphActual.gen,TerminalGraphProducer.gen,All12Generic.gen,All12Generic.mid,
  All12Generic.generic,gateSlots_append,rename_gateSlots]
 omega

theorem slots (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy:Fp) :
 gateSlots (gen L cx cy)≤49233000 := by
 have h:=gen_slots_diff L hw hn cx cy
 have old:=OwnTerminalGraphActual.slots L hw cx cy
 omega

theorem generic_free (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (k:Nat) (hk:k∈[1800,766,765,767,770,1285,1286]) (cx cy:Fp) :
 L.core.poolWire k∉wires (generic L cx cy) := by
 have bounds : 515≤k ∧ k<2613 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
 exact All12Generic.generic_free L hw hn _ _ _ k bounds
  (JointTerminalDivisionQ7.fusedDivisionF_free L hw hn k hk)
  (OwnDiagAll12PlacedQ7.square_free L hw hn k hk)
  (OneFlagExitOmissions.exit_avoids L hw hn k hk) cx cy

theorem ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (logicalND : (skywalkSharedWires base).Nodup) (hlo:History5.HistoryAbove base)
 (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
 (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
 {cx cy:Fp} (hc:curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
 All12Generic.genFFused_ok L hw hn _ _ _ (OwnOneFlagExitQ7.arithExit_correct L hw hn)
  (JointTerminalDivisionQ7.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
  (TerminalGraphProducer.square_step L hw hn) hc

theorem qubits (C:Point) (cx cy:Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1592 := by
 rw [gen,All12Generic.gen_shape]
 apply GenericQ7Geometry.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy)
 · intro k hk
   exact generic_free layout layout_widths layout_nodup k (List.mem_append_left [1285,1286] hk) cx cy
 · exact generic_free layout layout_widths layout_nodup 1285 (by simp) cx cy
 · exact generic_free layout layout_widths layout_nodup 1286 (by simp) cx cy
end ECDSAAdd.Entrant.JointTerminalActual

end
end FrontierJointTerminal

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      OwnDHWrapper.wrapper layout C cy (JointTerminalActual.gen layout cx cy)
def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2153104,1499809,1592,50000004⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have cfg:=MappedCompressed.LaneA.laneLogical_config
    have above:History5.HistoryAbove MappedCompressed.base:=by intro j hj;simp [MappedCompressed.base]
    have hG:=JointTerminalActual.sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (OwnDHWrapper.full_spec layout layout_widths layout_nodup R hc b _
        (JointTerminalActual.ok layout layout_widths layout_nodup cfg.1 above cfg.2.1 cfg.2.2 hc) hG)
      ((OwnDHWrapper.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2153104 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h:=(OwnDHWrapper.wrapper_counts layout layout_widths (JointTerminalActual.gen layout cx cy) hc).1
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf:=(genF_counts layout layout_widths cx cy).1
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
    have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).1
    have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).1
    have joint:=(JointTerminalActual.gen_counts_diff layout layout_widths layout_nodup cx cy).1
    have terminal:=(OwnTerminalGraphActual.counts_diff layout layout_widths cx cy).1
    change toffoliCount (OwnDHWrapper.wrapper layout (.some hc) cy (JointTerminalActual.gen layout cx cy))≤2153104
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1499809 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h:=(OwnDHWrapper.wrapper_counts layout layout_widths (JointTerminalActual.gen layout cx cy) hc).2
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf:=(genF_counts layout layout_widths cx cy).2
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
    have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).2
    have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).2
    have joint:=(JointTerminalActual.gen_counts_diff layout layout_widths layout_nodup cx cy).2
    have terminal:=(OwnTerminalGraphActual.counts_diff layout layout_widths cx cy).2
    change measurementCount (OwnDHWrapper.wrapper layout (.some hc) cy (JointTerminalActual.gen layout cx cy))≤1499809
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1592 := by
  cases C with
  | zero => change qubits []≤1592;rw [qubits_empty];decide
  | @some cx cy hc =>
    have old := JointTerminalActual.qubits (.some hc) cx cy
    have sub := OwnDHWrapper.wrapper_subset layout (.some hc) cy (JointTerminalActual.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) sub)).trans old

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact OwnDHWrapper.wrapper_physical layout layout_widths layout_nodup _ cy _
      (JointTerminalActual.physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50000004 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc =>
    have h:=OwnDHWrapper.wrapper_slots layout layout_widths (.some hc) cy (JointTerminalActual.gen layout cx cy)
    have g:=JointTerminalActual.slots layout layout_widths layout_nodup cx cy
    change gateSlots (OwnDHWrapper.wrapper layout (.some hc) cy (JointTerminalActual.gen layout cx cy))≤_
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499809
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1592
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50000004
    rw [normalize_slots];exact program_gateSlots C
end ECDSAAdd.Entrant

