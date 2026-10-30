import ECDSAAdd.Submission.Entrant.OneFlag

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
